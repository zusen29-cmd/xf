import asyncio, aiohttp, ssl, time, requests, urllib3, json, sys, os
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from google.protobuf import descriptor_pool as _dp, symbol_database as _sd
from google.protobuf.internal import builder as _b

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
_sd.Default()
D = _dp.Default().AddSerializedFile(b'\n\rreqClan.proto\"\x1c\n\tMyMessage\x12\x0f\n\x07\x66ield_1\x18\x01 \x01(\x03\x62\x06proto3')
_g = globals()
_b.BuildMessageAndEnumDescriptors(D, _g)
_b.BuildTopDescriptorsAndMessages(D, 'ReqCLan_pb2', _g)
MyMessage = _g['MyMessage']

KEY = bytes([89,103,38,116,99,37,68,69,117,104,54,37,90,99,94,56])
IV  = bytes([54,111,121,90,68,114,50,50,69,51,121,99,104,106,77,37])
CLIENT_URL, LOGIN_URL, OB_VERSION = "https://clientbp.ppmainecoonghj.com", "https://loginbp.ppmainecoonghj.com", "OB55"
JOIN_CLAN_ENDPOINT = "/RequestJoinClan"

#3105683920
def vr(n):
    r = []
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        r.append(b)
        if not n: break
    return bytes(r)


def pb(f):
    p = bytearray()
    for k, v in f.items():
        if isinstance(v, bool): p.extend(vr((k<<3)|0)); p.extend(vr(1 if v else 0))
        elif isinstance(v, int): p.extend(vr((k<<3)|0)); p.extend(vr(v))
        elif isinstance(v, str): d=v.encode(); p.extend(vr((k<<3)|2)); p.extend(vr(len(d))); p.extend(d)
        elif isinstance(v,(bytes,bytearray)): d=bytes(v); p.extend(vr((k<<3)|2)); p.extend(vr(len(d))); p.extend(d)
    return bytes(p)


def rv(data, pos):
    r, s = 0, 0
    while pos < len(data):
        b = data[pos]; pos += 1; r |= (b & 0x7F) << s
        if not (b & 0x80): break
        s += 7
    return r, pos


def parse_pb(data):
    f, pos, n = {}, 0, len(data)
    while pos < n:
        try: key, pos = rv(data, pos)
        except: break
        fn, wt = key >> 3, key & 7
        try:
            if wt == 0: v, pos = rv(data, pos)
            elif wt == 2: l, pos = rv(data, pos); v = data[pos:pos+l]; pos += l
            elif wt == 5: v = data[pos:pos+4]; pos += 4
            elif wt == 1: v = data[pos:pos+8]; pos += 8
            else: break
        except: break
        f.setdefault(fn, []).append(v)
    return f


def ssl_ctx():
    c = ssl.create_default_context(); c.check_hostname = False; c.verify_mode = ssl.CERT_NONE
    return c

def build_major(oid, tok):
    f = {3: time.strftime("%Y-%m-%d %H:%M:%S"),4:"free fire",5:1,7:"1.132.21",8:"Android OS 16 / API-36 (BP2A.250605.031.A3/OS3.0.303.0.WOQMIXM)",9:"Handheld",10:"Viettel",11:"CarrierDataNetwork",12:2400,13:1080,14:"450",15:"x86-64 | 2000 | 6",16:7485,17:"PowerVR B-Series BXM-8-256",18:"OpenGL ES 3.2 build 25.1@6715691",19:"Google|8d7a458f-d762-483c-8b13-0432ddf69ecf",20:"27.65.22.191",21:"vn",22:oid,23:"4",24:"Handheld",25:"Xiaomi 24094RAD4G",26:"VN",29:tok,30:1,41:"Viettel",42:"4G",57:"7428b253defc164018c604a1ebbfebdf",60:233141,61:169421,62:902,64:169945,65:233141,66:169945,67:233141,73:3,74:"/data/app/~~OOxSMPtiZSaEIgYJjPoHOg==/com.dts.freefireth-KkAAAdjU2FG5Ts4HwgDgCw==/lib/arm64",76:1,77:"b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~OOxSMPtiZSaEIgYJjPoHOg==/com.dts.freefireth-KkAAAdjU2FG5Ts4HwgDgCw==/base.apk",78:3,79:2,81:"64",83:"2019121229",85:3,86:"OpenGLES2",87:8191,88:4,90:"Ho Chi Minh City",91:"SG",92:9339,93:"android",94:"KqsHTw6ig4Gc39MBHQa+5VKNNU8oo4ak8w0NllWLvoUr+2pIZc1TeWooIvcbn49btS06j6slKvWIX9RN9g+0k5QhGwsfQ6S0ZCVXh8Tr9/PC43kX",95:111207,96:'{"cur_rate":[60,90,120],"support_etc2":false}',97:1,99:"4",100:"4",102:"",103:1,104:53896,105:1,106:"https://dl.gmc.freefiremobile.com/live/ABHotUpdates/|https://core-gmc.freefiremobile.com/live/ABHotUpdates/|ac2c27398b1d5d95a4b6b6e04fa94066",107:"1.eaed02dd9f66cfa5"}
    return AES.new(KEY, AES.MODE_CBC, IV).encrypt(pad(pb(f), 16))
    
async def oauth(uid, pw):
    url = "https://100067.connect.garena.com/api/v2/oauth/guest/token:grant"
    h = {"User-Agent":"GarenaMSDK/4.0.44(iPhone11,8;iOS 17.0.2;ar;MR;app 2.126.18 2019121229;)","Content-Type":"application/json; charset=utf-8"}
    b = {"client_id":100067,"client_secret":"2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3","client_type":2,"device_id":"","password":pw,"response_type":"token","uid":int(uid)}
    async with aiohttp.ClientSession() as s:
        async with s.post(url, headers=h, json=b, ssl=ssl_ctx(), timeout=aiohttp.ClientTimeout(total=15)) as r:
            if r.status != 200: return None
            j = await r.json(); return j.get("data", j)


async def major_login(p):
    h = {"User-Agent":"UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)","Accept":"*/*","Accept-Encoding":"deflate, gzip","X-GA-SV":str(int(time.time())),"Authorization":"Bearer","X-GA":"v1 1","ReleaseVersion":OB_VERSION,"Content-Type":"application/x-www-form-urlencoded","X-Unity-Version":"2018.4.12f1"}
    async with aiohttp.ClientSession() as s:
        async with s.post(f"{LOGIN_URL}/MajorLogin", data=p, headers=h, ssl=ssl_ctx(), timeout=aiohttp.ClientTimeout(total=15)) as r:
            raw = await r.read(); return raw if r.status == 200 else None


async def get_login_data(p, tok):
    h = {"Host":"clientbp.ppmainecoonghj.com","User-Agent":"UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)","Accept":"*/*","Accept-Encoding":"deflate, gzip","X-GA-SV":str(int(time.time())),"Authorization":f"Bearer {tok}","X-GA":"v1 1","ReleaseVersion":OB_VERSION,"Content-Type":"application/x-www-form-urlencoded","X-Unity-Version":"2018.4.12f1"}
    async with aiohttp.ClientSession() as s:
        async with s.post(f"{CLIENT_URL}/GetLoginData", data=p, headers=h, ssl=ssl_ctx(), timeout=aiohttp.ClientTimeout(total=15)) as r:
            raw = await r.read(); return raw if r.status == 200 else None


def send_join_clan(clan_id, tok):
    m = MyMessage(); m.field_1 = int(clan_id)
    data = AES.new(KEY, AES.MODE_CBC, IV).encrypt(pad(m.SerializeToString(), 16))
    try:
        r = requests.post(f"{CLIENT_URL}{JOIN_CLAN_ENDPOINT}", headers={"Content-Type":"application/x-www-form-urlencoded","X-GA":"v1 1","ReleaseVersion":OB_VERSION,"Host":"clientbp.ppmainecoonghj.com","Accept-Encoding":"gzip, deflate","User-Agent":"UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)","Connection":"keep-alive","Authorization":f"Bearer {tok}","X-Unity-Version":"2018.4.12f1","Accept":"*/*"}, data=data, verify=False, timeout=10)
        return r.status_code == 200, r.status_code, r.text[:300]
    except Exception as e:
        return False, 0, str(e)


async def join_async(uid, pw, cid):
    td = await oauth(uid, pw)
    if not td: return {"ok": False, "stage": "oauth"}
    oid, tok = td.get("open_id"), td.get("access_token")
    if not oid or not tok: return {"ok": False, "stage": "oauth_fields"}
    mp = build_major(oid, tok)
    ml = await major_login(mp)
    if not ml: return {"ok": False, "stage": "major_login"}
    f = parse_pb(ml[64:])
    if 1 not in f or 8 not in f: return {"ok": False, "stage": "parse"}
    aid = int(f[1][0]); jwt = f[8][0].decode()
    ld = await get_login_data(mp, jwt)
    if not ld: return {"ok": False, "stage": "get_login_data"}
    ok, code, txt = send_join_clan(cid, jwt)
    return {"ok": ok, "status": code, "response": txt, "account_id": aid, "clan_id": str(cid)}


def join_sync(uid, pw, cid):
    try: return asyncio.run(join_async(uid, pw, cid))
    except RuntimeError:
        loop = asyncio.new_event_loop(); asyncio.set_event_loop(loop)
        try: return loop.run_until_complete(join_async(uid, pw, cid))
        finally: loop.close()


def load_accounts(json_path):
    """
    Đọc danh sách tài khoản từ file JSON.
    Hỗ trợ 2 định dạng:
      - Array trực tiếp:  [{"uid": "...", "password": "..."}, ...]
      - Object có key:    {"accounts": [{"uid": "...", "password": "..."}, ...]}
    """
    if not os.path.exists(json_path):
        print(f"[ERROR] Không tìm thấy file: {json_path}")
        sys.exit(1)
    with open(json_path, "r", encoding="utf-8") as f:
        try:
            data = json.load(f)
        except json.JSONDecodeError as e:
            print(f"[ERROR] File JSON không hợp lệ: {e}")
            sys.exit(1)
    if isinstance(data, list):
        accounts = data
    elif isinstance(data, dict) and "accounts" in data:
        accounts = data["accounts"]
    else:
        print("[ERROR] Định dạng JSON không hợp lệ. Cần array hoặc object có key 'accounts'.")
        sys.exit(1)
    # Kiểm tra từng entry
    for i, a in enumerate(accounts):
        if "uid" not in a or "password" not in a:
            print(f"[ERROR] Account #{i+1} thiếu 'uid' hoặc 'password'.")
            sys.exit(1)
    return accounts


def run(clan_id, accounts):
    for i, a in enumerate(accounts, 1):
        print(f"Account {i}: {a['uid']}")
        r = join_sync(a["uid"], a["password"], clan_id)

        if r.get("ok"):
            print("  Success")
            print(f"    Account ID: {r.get('account_id')}")
            print(f"    Status: {r.get('status')}")
        else:
            resp = r.get("response", "")
            code = r.get("status", 0)

            if "ACCOUNT_LEVEL_NOT_ENOUGH" in resp:
                print("  Failed: account level too low for this clan")
            elif "CLAN_NOT_EXIST" in resp:
                print("  Failed: clan does not exist")
            elif "ALREADY_IN_CLAN" in resp:
                print("  Failed: account already in a clan")
            elif "CLAN_FULL" in resp:
                print("  Failed: clan is full")
            elif "REQUEST_ALREADY_SENT" in resp:
                print("  Failed: request already sent")
            elif code == 400:
                print(f"  Failed: server rejected ({resp[:80]})")
            else:
                print(f"  Failed at: {r.get('stage', 'unknown')}")
    return


if __name__ == "__main__":
    clan_id = input("Enter clan ID: ").strip()

    # Mặc định đọc file "acc.json" cùng thư mục, hoặc truyền path qua arg
    json_file = sys.argv[1] if len(sys.argv) > 1 else "acc.json"
    print(f"[INFO] Đọc tài khoản từ: {json_file}")

    accounts = load_accounts(json_file)
    print(f"[INFO] Tìm thấy {len(accounts)} tài khoản\n")

    run(clan_id, accounts)
