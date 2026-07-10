#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
肇庆学院 WebVPN 全自动抢课系统 v7.0 — 微秒级触发
架构:
  交互选课 → 预构建HTTP → asyncio协程池 → 10ms轮询 → 同tick释放 → QQ加群

性能:
  - 轮询间隔: 10ms (100次/秒)
  - 并发请求释放: <1ms (同事件循环 gather)
  - TCP keep-alive 复用, 零握手延迟
"""
import re, sys, time, json, base64, io, configparser, asyncio, contextlib
from dataclasses import dataclass, field
from typing import Optional, List, Tuple, Dict, Any
from pathlib import Path
from urllib.parse import urlencode
from datetime import datetime, timezone, timedelta
from email.utils import parsedate_to_datetime

try:
    from zoneinfo import ZoneInfo
except Exception:
    ZoneInfo = None

try:
    import aiohttp
    import requests
    from loguru import logger
except ImportError:
    import subprocess
    # 这些包原来在 ensure_deps() 之前导入，缺失时会直接崩溃；先补齐再退出重跑。
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "aiohttp", "requests", "loguru"])
    print("基础依赖已安装，请重新运行。")
    sys.exit(0)

# ============================================================
def ensure_deps():
    missing = []
    for mod in ["Crypto","cv2","numpy","PIL","ddddocr","aiohttp","requests","loguru"]:
        try:
            if mod=="PIL": __import__("PIL.Image")
            elif mod=="Crypto": __import__("Crypto.Cipher")
            else: __import__(mod)
        except ImportError: missing.append(mod)
    if missing:
        import subprocess
        pkgs = {"Crypto":"pycryptodome","cv2":"opencv-python","numpy":"numpy",
                "PIL":"Pillow","ddddocr":"ddddocr","aiohttp":"aiohttp",
                "requests":"requests","loguru":"loguru"}
        names = [pkgs[m] for m in missing if m in pkgs]
        print(f"\n安装依赖: {names}")
        subprocess.check_call([sys.executable,"-m","pip","install","-q"]+names)
        print("Done! 重新运行\n"); sys.exit(0)

ensure_deps()
from Crypto.Cipher import AES
import cv2, numpy as np
from PIL import Image
import ddddocr

# ============================================================
VPN_BASE  = "https://webvpn-free.zqu.edu.cn"
AES_KEY   = b"wrdvpnisawesome!"
AES_IV    = b"wrdvpnisawesome!"
EDU_PROXY = VPN_BASE + "/https/77726476706e69737468656265737421fae04690692a7945300d8db9d6562d/"
QQ_GROUP  = "1044128566"

# ============================================================
# 课程时间计算: 第一节8:00, 每节40分钟+休息10分钟
PERIOD_START = [None, "08:00","08:50","09:40","10:30","11:20",  # 1-5 上午
                "14:00","14:50","15:40","16:30","17:20",          # 6-10 下午
                "19:00","19:50","20:40"]                           # 11-13 晚上
PERIOD_END   = [None, "08:40","09:30","10:20","11:10","12:00",
                "14:40","15:30","16:20","17:10","18:00",
                "19:40","20:30","21:20"]
WEEKDAYS = {1:"周一",2:"周二",3:"周三",4:"周四",5:"周五",6:"周六",7:"周日"}

def _safe_int(value, default: int = 0) -> int:
    """把接口返回的 '', None, '10.0', '10人' 等安全转成 int。"""
    if value is None:
        return default
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, float)):
        return int(value)
    m = re.search(r"-?\d+", str(value))
    return int(m.group(0)) if m else default

def _normalize_weekday(text: str) -> str:
    """统一 '星期三'/'周三'/'周天' 为 '周三'/'周日'。"""
    day = text.replace("星期", "周")
    return day.replace("周天", "周日")

def _period_desc(p1: int, p2: int) -> str:
    # 1-5 上午，6-10 下午，11-13 晚上；跨段时明确标注。
    if p2 <= 5:
        return "上午"
    if p1 >= 6 and p2 <= 10:
        return "下午"
    if p1 >= 11:
        return "晚上"
    if p1 <= 5 and p2 >= 6:
        return "上午+下午"
    if p1 <= 10 and p2 >= 11:
        return "下午+晚上"
    return ""

def parse_time(xmmc: str) -> str:
    """从 xmmc 解析上课时间, 如 '周二6-7匹克球' → '周二 6-7节 下午 (14:00-15:30)'"""
    if not xmmc: return ""
    xmmc = str(xmmc).strip()
    # 提取周次前缀: "9-10周星期三6-8" → weeks="9-10周", rest="星期三6-8"
    week_prefix = ""
    rest = xmmc
    wm = re.match(r'(\d+[-—]\d+周)', xmmc)
    if wm:
        week_prefix = wm.group(1)
        rest = xmmc[wm.end():]

    # 匹配 "周三6-7" / "星期三6-7" / "周三第6-7节"
    day_pat = r'((?:周|星期)[一二三四五六日天])'
    m = re.search(day_pat + r'\s*(?:第)?\s*(\d{1,2})\s*[-—~至]\s*(\d{1,2})\s*(?:节)?', rest)
    if m:
        day = _normalize_weekday(m.group(1))
        p1, p2 = int(m.group(2)), int(m.group(3))
    else:
        # 匹配连续单节数字: "周三678" / "星期三67"。10节以后请优先使用 10-11 这类写法。
        m = re.search(day_pat + r'\s*(\d{2,5})\s*(?:节)?', rest)
        if m:
            day = _normalize_weekday(m.group(1))
            digits = m.group(2)
            if len(digits) <= 3 and all(ch in "123456789" for ch in digits):
                ps = sorted(set(int(d) for d in digits))
                p1, p2 = ps[0], ps[-1]
            elif len(digits) == 4 and digits[:2] in {"10", "11", "12", "13"}:
                p1, p2 = int(digits[:2]), int(digits[2:])
            else:
                return f"{xmmc[:30]}"
        else:
            return f"{xmmc[:30]}"

    if p1 > p2:
        p1, p2 = p2, p1

    # 时间段描述
    period_desc = _period_desc(p1, p2)

    start_t = PERIOD_START[p1] if p1 < len(PERIOD_START) else "?"
    end_t = PERIOD_END[p2] if p2 < len(PERIOD_END) else "?"

    week_str = f"{week_prefix} " if week_prefix else ""
    return f"{week_str}{day} {p1}-{p2}节 {period_desc} ({start_t}-{end_t})".strip()

@dataclass
class Course:
    name: str; section: str; teacher: str
    kcrwdm: str; jxbdm: str = ""; kcdm: str = ""
    capacity: int = 0; enrolled: int = 0
    credits: str = ""; nature: str = ""
    time_info: str = ""
    raw: dict = field(default_factory=dict)

    @property
    def remaining(self) -> int: return max(0, self.capacity - self.enrolled)
    @property
    def available(self) -> bool: return self.remaining > 0 or self.capacity == 0
    def __repr__(self): return f"[{self.time_info}] {self.section} {self.teacher} 余{self.remaining}"

@dataclass
class CourseType:
    name: str; xkkzdm: str = ""; kzdm: str = ""
    controller: str = "xsxklist"
    is_special: bool = False; main_url: str = ""
    courses: List[Course] = field(default_factory=list)
    raw: dict = field(default_factory=dict)

def course_from_row(row: Dict[str, Any]) -> Course:
    """把教务接口 row 统一转换成 Course，避免同步/异步扫描字段不一致。"""
    xmmc = str(row.get("xmmc", ""))
    return Course(
        name=str(row.get("kcmc", "")),
        section=str(row.get("jxbmc", row.get("xmmc", ""))),
        teacher=str(row.get("teaxm", "")),
        kcrwdm=str(row.get("kcrwdm", "")),
        jxbdm=str(row.get("jxbdm", "")),
        kcdm=str(row.get("kcdm", "")),
        capacity=_safe_int(row.get("pkrs", row.get("jxbrs", 0))),
        enrolled=_safe_int(row.get("jxbrs", 0)),
        credits=str(row.get("xf", "")),
        nature=str(row.get("xdfsmc", "")),
        time_info=parse_time(xmmc),
        raw=row,
    )

def local_tz():
    """学校选课时间按北京时间处理。"""
    if ZoneInfo:
        try:
            return ZoneInfo("Asia/Shanghai")
        except Exception:
            pass
    return timezone(timedelta(hours=8))

CN_TZ = local_tz()

def parse_school_datetime(value: str) -> Optional[datetime]:
    """解析教务系统的 'YYYY-mm-dd HH:MM:SS' 为北京时间 aware datetime。"""
    value = str(value or "").strip()
    if not value:
        return None
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
        try:
            return datetime.strptime(value, fmt).replace(tzinfo=CN_TZ)
        except ValueError:
            continue
    return None

def get_course_windows(raw: dict) -> List[dict]:
    """从选课类型 raw 中提取多轮选课窗口。"""
    windows = []
    for stage, (sk, ek) in enumerate([('qssj1','jssj1'),('qssj2','jssj2'),('qssj3','jssj3')], 1):
        start = parse_school_datetime(raw.get(sk, ""))
        end = parse_school_datetime(raw.get(ek, ""))
        if start and end:
            windows.append({"stage": stage, "start": start, "end": end})
    return windows

def choose_active_or_next_window(raw: dict, now_dt: datetime) -> Optional[dict]:
    """优先返回进行中的窗口；否则返回最近的未来窗口。"""
    windows = sorted(get_course_windows(raw), key=lambda x: x["start"])
    for w in windows:
        if w["start"] <= now_dt <= w["end"]:
            return {**w, "status": "active"}
    for w in windows:
        if now_dt < w["start"]:
            return {**w, "status": "future"}
    return None

def server_now(server_delta: timedelta = timedelta(0)) -> datetime:
    """用校准偏移估算服务器当前 UTC 时间。"""
    return datetime.now(timezone.utc) + server_delta

def calibrate_server_time(session: requests.Session, samples: int = 3) -> timedelta:
    """
    通过 HTTP Date 头估算本机和服务器时间差。
    返回 delta：server_utc ~= local_utc + delta。
    """
    best = None
    for i in range(max(1, samples)):
        try:
            t0 = datetime.now(timezone.utc)
            r = session.get(EDU_PROXY, timeout=8, stream=True)
            t1 = datetime.now(timezone.utc)
            # 不需要正文，只拿响应头；及时关闭释放连接。
            r.close()
            date_header = r.headers.get("Date")
            if not date_header:
                continue
            srv = parsedate_to_datetime(date_header)
            if srv.tzinfo is None:
                srv = srv.replace(tzinfo=timezone.utc)
            srv = srv.astimezone(timezone.utc)
            midpoint = t0 + (t1 - t0) / 2
            rtt = (t1 - t0).total_seconds()
            delta = srv - midpoint
            if best is None or rtt < best[0]:
                best = (rtt, delta, date_header)
        except Exception as e:
            logger.debug(f"服务器时间校准失败({i+1}/{samples}): {e}")
            time.sleep(0.2)
    if not best:
        logger.warning("未能从 HTTP Date 头校准服务器时间，使用本机时间。")
        return timedelta(0)
    rtt, delta, date_header = best
    logger.info(f"服务器时间校准: Date={date_header}, RTT={rtt*1000:.0f}ms, 偏移={delta.total_seconds()*1000:.0f}ms")
    return delta

def save_target_selection(ct: CourseType, targets: List[Course], window: Optional[dict], path: str = "target_course.json"):
    """保存本次选择，便于复盘或下次无课程列表时参考。"""
    if not targets:
        return
    data = {
        "saved_at": datetime.now(CN_TZ).strftime("%Y-%m-%d %H:%M:%S"),
        "course_type": {
            "name": ct.name,
            "controller": ct.controller,
            "xkkzdm": ct.xkkzdm,
            "kzdm": ct.kzdm,
            "is_special": ct.is_special,
        },
        "window": {
            "stage": window.get("stage") if window else None,
            "status": window.get("status") if window else None,
            "start": window["start"].strftime("%Y-%m-%d %H:%M:%S") if window else None,
            "end": window["end"].strftime("%Y-%m-%d %H:%M:%S") if window else None,
        },
        "targets": [
            {
                "name": c.name,
                "section": c.section,
                "teacher": c.teacher,
                "kcrwdm": c.kcrwdm,
                "jxbdm": c.jxbdm,
                "kcdm": c.kcdm,
                "time_info": c.time_info,
                "capacity": c.capacity,
                "enrolled": c.enrolled,
            }
            for c in targets
        ],
    }
    p = Path(path)
    p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    logger.info(f"目标课程已保存: {p.resolve()}")

# ============================================================
# 通知 + QQ
# ============================================================
_qq_opened = False

def desktop_notify(title: str, msg: str):
    try:
        import subprocess
        ps = f'''
Add-Type -AssemblyName System.Windows.Forms
$n=New-Object System.Windows.Forms.NotifyIcon
$n.Icon=[System.Drawing.Icon]::ExtractAssociatedIcon([System.Diagnostics.Process]::GetCurrentProcess().MainModule.FileName)
$n.BalloonTipTitle="{title}";$n.BalloonTipText="{msg}"
$n.Visible=$true;$n.ShowBalloonTip(5000);Start-Sleep 6;$n.Dispose()'''
        subprocess.Popen(["powershell","-NoProfile","-NonInteractive","-Command",ps],
                         stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    except: pass

def beep():
    try: import winsound; winsound.MessageBeep(0x00040000)
    except: pass

def open_qq():
    global _qq_opened
    if _qq_opened: return
    _qq_opened = True
    try:
        import webbrowser, subprocess
        webbrowser.open(f"https://qm.qq.com/q/{QQ_GROUP}")
        subprocess.Popen(["start",f"tencent://AddContact/?fromId=45&fromSubId=1&subcmd=all&uin={QQ_GROUP}"],
                       shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        logger.info(f"[QQ] 加群链接已打开: {QQ_GROUP}")
    except: pass

# ============================================================
# Part 1: VPN 登录 (同步, 复用 v6.0 代码)
# ============================================================
def vpn_login(username: str, password: str, proxy: str = None) -> Optional[requests.Session]:
    s = requests.Session()
    s.headers.update({"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                       "Accept-Language":"zh-CN,zh;q=0.9"})
    if proxy: s.proxies = {"http":proxy,"https":proxy}

    def _encrypt(text):
        tl = len(text)
        padded = text if tl%16==0 else text+"0"*(16-tl%16)
        cipher = AES.new(AES_KEY, AES.MODE_CFB, iv=AES_IV, segment_size=128)
        enc = cipher.encrypt(padded.encode())
        return AES_IV.hex() + enc.hex()[:tl*2]

    def _solve_slider():
        r = s.get(f"{VPN_BASE}/login/image", params={"_":int(time.time()*1000)}, timeout=15)
        data = r.json()
        for k in ("p","s"):
            if data[k].startswith("data:"): data[k] = data[k].split(",",1)[1]
        bg = cv2.cvtColor(np.array(Image.open(io.BytesIO(base64.b64decode(data["p"])))), cv2.COLOR_RGB2GRAY)
        sl = cv2.cvtColor(np.array(Image.open(io.BytesIO(base64.b64decode(data["s"])))), cv2.COLOR_RGB2GRAY)
        be = cv2.Canny(bg,100,200); se = cv2.Canny(sl,100,200)
        res = cv2.matchTemplate(be,se,cv2.TM_CCOEFF_NORMED)
        _,_,_,ml = cv2.minMaxLoc(res)
        dist = ml[0]; locs = []; x = 0
        for i in range(int(dist)):
            p = i/dist
            if p<0.1: step=1+p/0.1*3
            elif p>0.8: step=3-(p-0.8)/0.2*2
            else: step=3+(0.5-abs(p-0.5))*0.5
            x = min(x+int(step),int(dist)); locs.append({"x":x,"y":30})
        r = s.post(f"{VPN_BASE}/login/verify",
            data={"w":int(dist),"t":len(locs)*30,"locations":json.dumps(locs)}, timeout=15)
        return r.json().get("success",False)

    r = s.get(f"{VPN_BASE}/login", timeout=15)
    m = re.search(r'name="_csrf"\s+value="([^"]+)"', r.text)
    if not m: logger.error("CSRF获取失败"); return None
    csrf = m.group(1)

    for i in range(5):
        if _solve_slider(): break
        logger.warning(f"滑块重试 {i+1}/5")
    else: logger.error("滑块失败"); return None
    time.sleep(1.5)

    enc_pw = _encrypt(password)
    r = s.post(f"{VPN_BASE}/do-login",
        data={"_csrf":csrf,"auth_type":"local","username":username,"password":enc_pw},
        timeout=15, allow_redirects=False)
    result = r.json()
    if result.get("error")=="NEED_CONFIRM":
        r = s.post(f"{VPN_BASE}/do-confirm-login", timeout=15); result = r.json()
    if result.get("error")=="NEED_TWO_STEP":
        code = input(f"短信验证码 ({result.get('phone','')}): ").strip()
        r = s.post(f"{VPN_BASE}/do-login",
            data={"_csrf":csrf,"auth_type":"local","username":username,"password":enc_pw,"code":code},
            timeout=15); result = r.json()
    if result.get("success"):
        logger.success("VPN OK")
        return s
    logger.error(f"VPN失败: {result.get('error')}"); return None

# ============================================================
# Part 2: 教务登录
# ============================================================
def edu_login(session: requests.Session, username: str, password: str) -> bool:
    ocr = ddddocr.DdddOcr(show_ad=False)
    for attempt in range(5):
        r = session.get(EDU_PROXY + "yzm?d=" + str(int(time.time()*1000)), timeout=10)
        code = ocr.classification(r.content)
        pwd_b64 = base64.b64encode(password.encode()).decode()
        r = session.post(EDU_PROXY + "login!doLogin.action",
            data={"account":username,"pwd":pwd_b64,"verifycode":code},
            headers={"Accept":"application/json","Content-Type":"application/x-www-form-urlencoded",
                     "X-Requested-With":"XMLHttpRequest","Referer":EDU_PROXY}, timeout=15)
        try: result = r.json()
        except: continue
        if result.get("status")=="y":
            logger.success("教务 OK")
            return True
        elif "验证码" in result.get("msg",""): continue
        else: logger.error(f"教务登录失败: {result.get('msg','')}"); return False
    return False

# ============================================================
# Part 3: API 扫描 (同步)
# ============================================================
class Scanner:
    def __init__(self, session: requests.Session):
        self.s = session

    def scan_types(self) -> List[CourseType]:
        logger.info("扫描选课类型...")
        types = []
        try:
            r = self.s.get(EDU_PROXY + "xsxkmain!getDataList.action",
                params={"page":"1","rows":"100"},
                headers={"Referer":EDU_PROXY+"xsxkmain!xkmain.action","X-Requested-With":"XMLHttpRequest"},
                timeout=15)
            for item in r.json():
                t = CourseType(
                    name=item.get("xklxmc","?"),
                    xkkzdm=str(item.get("xkkzdm","")),
                    kzdm=str(item.get("kzdm","")),
                    raw=item,
                )
                if t.kzdm and not t.xkkzdm: t.controller = "jlxklist"
                elif "补修" in t.name: t.controller="bcbmxx"; t.is_special=True; t.main_url="bcbmxx!bcbmMain.action"
                elif "体测" in t.name: t.controller="xstcbm"; t.is_special=True; t.main_url="xstcbm!xstcbmMain.action"
                else: t.controller = "xsxklist"
                types.append(t)
        except Exception as e:
            logger.error(f"扫描类型失败: {e}")
        return types

    def scan_courses(self, ct: CourseType) -> List[Course]:
        params = {"page":"1","rows":"500"}
        if ct.is_special: pass
        elif ct.controller == "jlxklist": params["kzdm"] = ct.kzdm
        else: params["xkkzdm"] = ct.xkkzdm

        try:
            r = self.s.post(EDU_PROXY + f"{ct.controller}!getDataList.action", data=params,
                headers={"Referer":EDU_PROXY,"X-Requested-With":"XMLHttpRequest",
                         "Content-Type":"application/x-www-form-urlencoded"}, timeout=15)
            data = r.json()
            rows = data.get("rows",[]) if isinstance(data,dict) else (data if isinstance(data,list) else [])
            courses = []
            for row in rows:
                c = course_from_row(row)
                if c.kcrwdm: courses.append(c)
            ct.courses = courses
            return courses
        except Exception as e:
            logger.debug(f"扫描课程失败 ({ct.name}): {e}")
            return []

    def scan_enrolled(self, ct: CourseType) -> List[dict]:
        try:
            if ct.controller=="jlxklist": params={"kzdm":ct.kzdm}
            elif ct.is_special: params={}
            else: params={"xkkzdm":ct.xkkzdm}
            r = self.s.post(EDU_PROXY + f"{ct.controller}!getXzkcList.action", data=params,
                headers={"Referer":EDU_PROXY,"X-Requested-With":"XMLHttpRequest",
                         "Content-Type":"application/x-www-form-urlencoded"}, timeout=15)
            data = r.json()
            return data if isinstance(data,list) else data.get("rows",[])
        except: return []

# ============================================================
# Part 4: 微秒级异步抢课引擎
# ============================================================
class MicroGrabber:
    """
    微秒级触发引擎 v2.0:
    - 预编码 HTTP 请求字节 (零构建延迟)
    - 1ms 间隔轮询 (1000次/秒)
    - asyncio.gather() 同 tick 齐射 (<500us 内全部发出)
    - 预发射模式: 窗口开启前持续发送, 确保请求已在服务器TCP缓冲区

    原理:
      服务器选课窗口开启的瞬间, 它的 TCP 栈会开始 accept() 连接并处理 HTTP 请求.
      我们在窗口开启前就维持 N 个 keep-alive 连接, 每 1ms 检查一次 getDataList.
      检测到数据的同一毫秒内, N 个预编码的 getAdd 请求通过 gather() 同时写入 socket,
      成为服务器启动后处理的第一批请求.
    """

    def __init__(
        self,
        cookies: dict,
        pool_size: int = 16,
        *,
        retry_ms: int = 1000,
        prefire: bool = False,
        prefire_interval_ms: int = 200,
    ):
        self.cookies = cookies
        self.pool_size = max(1, int(pool_size or 1))
        self.retry_ms = max(200, int(retry_ms or 1000))
        self.prefire = bool(prefire)
        self.prefire_interval_ms = max(50, int(prefire_interval_ms or 200))
        self._connector: Optional[aiohttp.TCPConnector] = None
        self._sessions: List[aiohttp.ClientSession] = []
        self._ct: Optional[CourseType] = None
        self._targets: List[Course] = []
        self._grabbed = set()
        self._first_done = False
        self._notified_failure = False
        self._headers = {
            "User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Accept":"application/json, text/javascript, */*; q=0.01",
            "Accept-Language":"zh-CN,zh;q=0.9",
            "X-Requested-With":"XMLHttpRequest",
            "Connection":"keep-alive",
        }
        # 预编码的请求数据 (避免每次构建)
        self._encoded_select_bodies: dict = {}   # kcrwdm → urlencoded bytes
        self._encoded_search_body: bytes = b""

    async def _warm_up(self):
        """预热: 创建连接池 + 预编码所有请求体"""
        self._connector = aiohttp.TCPConnector(
            limit=self.pool_size,
            limit_per_host=self.pool_size,
            force_close=False,
            enable_cleanup_closed=False,
            keepalive_timeout=300,
            ttl_dns_cache=3600,
        )

        cookie_jar = aiohttp.CookieJar(unsafe=True)
        cookie_jar.update_cookies({str(k): str(v) for k, v in self.cookies.items()})

        for _ in range(self.pool_size):
            session = aiohttp.ClientSession(
                connector=self._connector,
                connector_owner=False,
                cookie_jar=cookie_jar,
                headers=self._headers,
            )
            self._sessions.append(session)

        async def _touch(session: aiohttp.ClientSession):
            try:
                async with session.get(EDU_PROXY, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                    await resp.read()  # 必须释放响应，否则连接不会回到 keep-alive 池
            except Exception as e:
                logger.debug(f"预热连接失败: {e}")

        # 预建立 TCP 连接。并发触发，读完响应后连接保留在 keep-alive 池中。
        warm_tasks = [_touch(s) for s in self._sessions[:min(4, self.pool_size)]]
        await asyncio.gather(*warm_tasks, return_exceptions=True)

        logger.success(f"连接池 + TCP预热: {self.pool_size} 就绪")

    def _encode_select(self, ct: CourseType, course: Course) -> bytes:
        """预编码选课请求体"""
        key = (ct.controller, ct.xkkzdm, ct.kzdm, course.kcrwdm)
        if key not in self._encoded_select_bodies:
            params = {"kcrwdm": course.kcrwdm, "kcmc": course.name, "tzjf": "0"}
            if ct.controller=="jlxklist":
                params["kzdm"] = ct.kzdm
            elif not ct.is_special:
                params["xkkzdm"] = ct.xkkzdm
            # 不能手写 "a=b&kcmc=中文"：课程名包含中文、空格、& 时会提交错。
            self._encoded_select_bodies[key] = urlencode(params).encode("utf-8")
        return self._encoded_select_bodies[key]

    async def _poll_once(self, session: aiohttp.ClientSession, ct: CourseType) -> Optional[List[Course]]:
        """1ms 轮询: 检查选课窗口是否开启"""
        params = {"page":"1","rows":"500"}
        if not ct.is_special:
            if ct.controller=="jlxklist": params["kzdm"]=ct.kzdm
            else: params["xkkzdm"]=ct.xkkzdm

        try:
            async with session.post(EDU_PROXY + f"{ct.controller}!getDataList.action",
                                     data=params, timeout=aiohttp.ClientTimeout(total=3)) as resp:
                text = await resp.text()
                if not text or len(text) < 10: return None
                data = json.loads(text)
                rows = data.get("rows",[]) if isinstance(data,dict) else (data if isinstance(data,list) else [])
                if not rows: return None
                courses = []
                for row in rows:
                    c = course_from_row(row)
                    if c.kcrwdm:
                        courses.append(c)
                return courses if courses else None
        except Exception as e:
            logger.debug(f"轮询失败: {e}")
            return None

    async def _fire_one_raw(self, session: aiohttp.ClientSession, ct: CourseType,
                             course: Course) -> Tuple[str, bool, str, float]:
        """单次选课请求 (预编码body, 零构建开销)"""
        body = self._encode_select(ct, course)
        t0 = time.perf_counter()
        try:
            async with session.post(EDU_PROXY + f"{ct.controller}!getAdd.action",
                                     data=body,
                                     headers={"Content-Type":"application/x-www-form-urlencoded; charset=UTF-8",
                                              "Referer":EDU_PROXY,
                                              "X-Requested-With":"XMLHttpRequest"},
                                     timeout=aiohttp.ClientTimeout(total=6)) as resp:
                text = await resp.text()
                lat = (time.perf_counter()-t0)*1_000_000
                return (course.kcrwdm, text.strip()=="1", text[:80], lat)
        except asyncio.TimeoutError:
            return (course.kcrwdm, False, "timeout", (time.perf_counter()-t0)*1_000_000)
        except Exception as e:
            return (course.kcrwdm, False, str(e)[:60], (time.perf_counter()-t0)*1_000_000)

    async def _volley(self, ct: CourseType, targets: List[Course]):
        """
        齐射: 所有连接 × 所有目标, 同一个 gather() 释放
        预编码的请求体直接写入 socket, 全部请求在 <500us 内发出
        """
        if not targets:
            logger.debug("齐射跳过: 未指定目标课程")
            return False

        tasks = []
        # 使用整个连接池做轮转分配，避免多目标时所有请求挤在前几个 session 上。
        for i in range(self.pool_size):
            course = targets[i % len(targets)]
            session = self._sessions[i % len(self._sessions)]
            tasks.append(self._fire_one_raw(session, ct, course))

        t0 = time.perf_counter()
        results = await asyncio.gather(*tasks, return_exceptions=True)
        elapsed = (time.perf_counter()-t0)*1_000_000

        success = False
        failures: Dict[str, int] = {}
        for r in results:
            if isinstance(r, tuple) and r[1]:
                kcrwdm, ok, msg, lat = r
                self._grabbed.add(kcrwdm)
                success = True
                logger.success(f"抢课成功! kcrwdm={kcrwdm[-6:]} ({lat:.0f}us)")
            elif isinstance(r, tuple):
                msg = (r[2] or "").strip()[:80]
                failures[msg] = failures.get(msg, 0) + 1
            elif isinstance(r, Exception):
                msg = str(r)[:80]
                failures[msg] = failures.get(msg, 0) + 1

        logger.info(f"齐射: {len(tasks)}请求 {elapsed:.0f}us, 成功={success}")
        if failures:
            brief = "; ".join(f"{k or '<empty>'}×{v}" for k, v in list(failures.items())[:3])
            logger.debug(f"齐射失败摘要: {brief}")

        # 旧版这里无论成功/失败都会置 _first_done=True，导致第一次失败后直接退出。
        # 现在只有真正成功才停止；失败则按 retry_ms 继续重试。
        if success and not self._first_done:
            self._first_done = True
            open_qq()
            desktop_notify("抢课结果", "抢到了!")
            beep()
        elif not success and not self._notified_failure:
            self._notified_failure = True
            desktop_notify("抢课结果", "本次提交失败，继续重试中...")

        return success

    async def _prefire_loop(self, ct: CourseType, course: Course, session_idx: int):
        """
        预发射循环: 按固定间隔试探提交，并且读取/释放响应。
        注意：旧版 fire-and-forget 不读取响应，会把连接池耗尽，也无法知道是否成功。
        """
        session = self._sessions[session_idx % self.pool_size]
        count = 0
        while not self._first_done:
            try:
                kcrwdm, ok, msg, lat = await self._fire_one_raw(session, ct, course)
                count += 1
                if ok:
                    self._grabbed.add(kcrwdm)
                    self._first_done = True
                    open_qq()
                    desktop_notify("抢课结果", "抢到了!")
                    beep()
                    logger.success(f"预发射成功! kcrwdm={kcrwdm[-6:]} ({lat:.0f}us)")
                    break
                if count % 20 == 0:
                    logger.debug(f"  预发射[{session_idx}]: {count}次，最近响应={msg[:60]}")
            except Exception as e:
                logger.debug(f"预发射[{session_idx}]异常: {e}")
            await asyncio.sleep(self.prefire_interval_ms / 1000.0)

        logger.debug(f"预发射[{session_idx}] 停止: {count}次")

    async def _wait_and_fire(self, ct: CourseType, targets: List[Course], poll_ms: int = 1):
        """
        核心: 预发射 + 1ms轮询 + 检测齐射 三重保障

        策略:
          1. 一半连接做预发射 (持续发送getAdd, 不等响应)
          2. 一个连接做轮询检测 (1ms检查getDataList)
          3. 检测到数据后所有连接齐射确认
        """
        poll_ms = max(1, int(poll_ms or 1))
        poll_s = self._sessions[0]

        # 分配: 前半做预发射, 后半做齐射备份
        half = max(1, self.pool_size // 2)
        pref_sessions = self._sessions[:half]
        fire_sessions = self._sessions[half:]

        # 预发射默认关闭。旧版无目标/未开窗时会持续 fire-and-forget，容易耗尽连接池。
        pref_tasks = []
        if self.prefire and targets:
            for i, course in enumerate(targets):
                sidx = i % len(pref_sessions)
                task = asyncio.create_task(self._prefire_loop(ct, course, sidx))
                pref_tasks.append(task)

        logger.info(f"预发射: {'开启' if pref_tasks else '关闭'}" + (f" ({len(pref_tasks)}协程, {self.prefire_interval_ms}ms间隔)" if pref_tasks else ""))
        logger.info(f"轮询检测: 每{poll_ms}ms ({1000//poll_ms}次/秒)")
        logger.info(f"齐射备份: {len(fire_sessions)}连接待命")
        logger.info(f"目标: {len(targets)}门 → {[t.kcrwdm[-6:] for t in targets]}")
        if not targets:
            logger.warning("未指定目标课程：将只监控窗口并展示可选课程，不会自动提交任意课程。")
        logger.info("选课窗口开启后按目标课程提交；失败会按重试间隔继续尝试。\n")

        check = 0; start = time.perf_counter(); had_data = False; last_fire = 0.0

        try:
            while True:
                check += 1
                courses = await self._poll_once(poll_s, ct)

                if courses:
                    if not had_data:
                        elapsed = (time.perf_counter()-start)*1000
                        logger.success(f"[检测{check}] 窗口已开 ({elapsed:.0f}ms)")

                        # 显示当前课程
                        for c in sorted(courses, key=lambda x:-x.remaining)[:10]:
                            logger.info(f"  {c.teacher:6s} | {c.section[:30]} | 余{c.remaining}")

                    if targets:
                        # 只提交用户选中的目标。旧版 targets 为空时会退化成“任意可选课第一门”，风险很高。
                        target_ids = {t.kcrwdm for t in targets}
                        hit = [c for c in courses if c.kcrwdm in target_ids and c.available]
                        if not hit:
                            logger.debug("窗口有数据，但目标课程暂无余量/未出现在列表中")
                        now = time.perf_counter()
                        if hit and (now - last_fire) * 1000 >= self.retry_ms:
                            logger.info(f"齐射确认: {len(hit)}目标 × {self.pool_size}连接")
                            await self._volley(ct, hit)
                            last_fire = now

                    had_data = True
                else:
                    if had_data:
                        logger.info("窗口关闭")
                        had_data = False

                # 如果抢到了, 停止
                if self._first_done:
                    logger.success("目标课程提交成功，监控30秒后退出...")
                    await asyncio.sleep(30)
                    break

                if check % 1000 == 0:
                    elapsed = time.perf_counter()-start
                    logger.debug(f"[{check}] {elapsed:.0f}s 监控中...")

                await asyncio.sleep(poll_ms / 1000.0)
        finally:
            for t in pref_tasks:
                t.cancel()
            if pref_tasks:
                await asyncio.gather(*pref_tasks, return_exceptions=True)

    async def _sleep_until_server_time(self, target_dt: datetime, server_delta: timedelta, label: str = ""):
        """按校准后的服务器时间等待到目标时刻。"""
        target_utc = target_dt.astimezone(timezone.utc)
        while True:
            remain = (target_utc - server_now(server_delta)).total_seconds()
            if remain <= 0:
                return
            if remain > 60:
                logger.info(f"{label} 剩余 {remain:.1f}s")
                await asyncio.sleep(min(30, remain - 30))
            elif remain > 5:
                await asyncio.sleep(min(1, remain - 3))
            elif remain > 0.5:
                await asyncio.sleep(min(0.1, remain - 0.2))
            elif remain > 0.02:
                await asyncio.sleep(min(0.01, remain))
            else:
                # 最后 20ms 不做 busy wait，只让出事件循环，尽量贴近目标时间。
                await asyncio.sleep(0)

    async def _timed_fire(
        self,
        ct: CourseType,
        targets: List[Course],
        window: dict,
        server_delta: timedelta,
        warmup_ms: int = 300,
        lead_ms: int = 30,
        burst_count: int = 5,
        burst_gap_ms: int = 25,
        monitor_after_success: int = 30,
    ):
        """
        极速定时模式：
        - 登录后先由用户选择目标；
        - 按服务器时间等到开始前 warmup_ms 再预热连接；
        - 开放前 lead_ms 进入边界爆发，尽量让请求在服务器开窗瞬间抵达；
        - 边界 burst_count 轮，每轮间隔 burst_gap_ms；
        - 失败按 self.retry_ms 重试，不退化成任意课程。
        """
        if not targets:
            logger.warning("未指定目标课程，极速定时模式不会提交任何课程。")
            return False

        warmup_ms = max(0, int(warmup_ms or 0))
        lead_ms = max(0, int(lead_ms or 0))
        burst_count = max(1, int(burst_count or 1))
        burst_gap_ms = max(1, int(burst_gap_ms or 1))
        min_warmup_ms = lead_ms + 200 if lead_ms > 0 else warmup_ms
        if warmup_ms < min_warmup_ms:
            logger.warning(f"预热时间 {warmup_ms}ms 小于提前提交 {lead_ms}ms + 安全余量，自动提高到 {min_warmup_ms}ms")
            warmup_ms = min_warmup_ms
        start_dt = window["start"]
        end_dt = window.get("end")
        now_cn = server_now(server_delta).astimezone(CN_TZ)
        target_ids = [t.kcrwdm[-6:] for t in targets]

        logger.info("极速定时模式已启用:")
        logger.info(f"  服务器当前时间: {now_cn.strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]}")
        logger.info(f"  开始时间: {start_dt.strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]}")
        if end_dt:
            logger.info(f"  结束时间: {end_dt.strftime('%Y-%m-%d %H:%M:%S')}")
        logger.info(f"  预热提前: {warmup_ms}ms")
        logger.info(f"  边界提前: {lead_ms}ms")
        logger.info(f"  边界爆发: {burst_count}轮 × 间隔{burst_gap_ms}ms")
        logger.info(f"  失败重试: {self.retry_ms}ms")
        logger.info(f"  目标: {len(targets)}门 → {target_ids}")

        warm_dt = start_dt - timedelta(milliseconds=warmup_ms)
        fire_dt = start_dt - timedelta(milliseconds=lead_ms)
        if now_cn < warm_dt:
            await self._sleep_until_server_time(warm_dt, server_delta, "等待预热")

        if not self._sessions:
            logger.info("开始预热连接池...")
            await self._warm_up()
        else:
            logger.debug("连接池已预热，跳过重复预热")

        # 如果预热耗时超过提前点，这里会立即返回并马上提交。
        await self._sleep_until_server_time(fire_dt, server_delta, "等待边界提交")

        logger.success(f"到达边界提交点：开放前 {lead_ms}ms，开始爆发提交目标课程!")
        attempt = 0

        for burst_idx in range(burst_count):
            now_cn = server_now(server_delta).astimezone(CN_TZ)
            if end_dt and now_cn > end_dt:
                logger.warning("选课窗口已结束，停止边界爆发。")
                break

            attempt += 1
            offset_ms = (now_cn - start_dt).total_seconds() * 1000
            logger.info(f"边界爆发第 {burst_idx+1}/{burst_count} 轮，总第 {attempt} 轮，服务器偏移 {offset_ms:+.0f}ms")
            ok = await self._volley(ct, targets)
            if ok or self._first_done:
                logger.success("目标课程提交成功，监控30秒后退出...")
                await asyncio.sleep(monitor_after_success)
                return True

            if burst_idx < burst_count - 1:
                await asyncio.sleep(burst_gap_ms / 1000.0)

        logger.info("边界爆发未成功，进入持续重试。")
        while not self._first_done:
            now_cn = server_now(server_delta).astimezone(CN_TZ)
            if end_dt and now_cn > end_dt:
                logger.warning("选课窗口已结束，停止定时提交。")
                break

            attempt += 1
            offset_ms = (now_cn - start_dt).total_seconds() * 1000
            logger.info(f"持续重试第 {attempt} 轮，服务器偏移 {offset_ms:+.0f}ms")
            ok = await self._volley(ct, targets)
            if ok or self._first_done:
                logger.success("目标课程提交成功，监控30秒后退出...")
                await asyncio.sleep(monitor_after_success)
                return True

            await asyncio.sleep(self.retry_ms / 1000.0)

        return self._first_done

    async def _close(self):
        for s in self._sessions:
            with contextlib.suppress(Exception):
                await s.close()
        self._sessions.clear()
        if self._connector and not self._connector.closed:
            with contextlib.suppress(Exception):
                await self._connector.close()

# ============================================================
# Part 5: 交互式选菜单
# ============================================================
def format_window(raw: dict) -> list:
    """格式化选课时间窗口 + 倒计时"""
    from datetime import datetime
    now = datetime.now()
    windows = []
    for stage, (sk, ek) in enumerate([('qssj1','jssj1'),('qssj2','jssj2'),('qssj3','jssj3')]):
        qs = raw.get(sk,'').strip()
        js = raw.get(ek,'').strip()
        if qs and js:
            try:
                qs_dt = datetime.strptime(qs, "%Y-%m-%d %H:%M:%S")
                js_dt = datetime.strptime(js, "%Y-%m-%d %H:%M:%S")
                if now < qs_dt:
                    diff = qs_dt - now
                    d,h,m = diff.days, diff.seconds//3600, (diff.seconds%3600)//60
                    windows.append((f"第{stage+1}轮: {qs} ~ {js}", f"距离开启: {d}天{h}时{m}分"))
                elif qs_dt <= now <= js_dt:
                    diff = js_dt - now
                    d,h,m = diff.days, diff.seconds//3600, (diff.seconds%3600)//60
                    windows.append((f"第{stage+1}轮: {qs} ~ {js}", f"进行中! 剩余{d}天{h}时{m}分"))
                else:
                    windows.append((f"第{stage+1}轮: {qs} ~ {js}", "已结束"))
            except: pass
    return windows

def interactive_select(scanner: Scanner) -> Tuple[Optional[CourseType], List[Course]]:
    """交互式选择: 扫描 → 显示 → 用户选 → 返回目标"""

    print("\n" + "=" * 60)
    print("  扫描选课系统 (只读, 不会修改任何数据)")
    print("=" * 60)

    types = scanner.scan_types()
    if not types:
        logger.warning("当前无可用选课类型")
        return None, []

    print(f"\n发现 {len(types)} 种选课类型:\n")
    for i, t in enumerate(types):
        tips = ""
        if t.raw.get("xk_tips"):
            tips = t.raw["xk_tips"].replace("&mdash;","—").replace("&amp;","&")[:120]
        # 时间窗口 + 倒计时
        windows = format_window(t.raw)
        if windows:
            win_lines = []
            for win_str, countdown in windows:
                win_lines.append(f"{win_str} [{countdown}]")
            print(f"  [{i+1}] {t.name}  {' | '.join(win_lines)}")
        else:
            print(f"  [{i+1}] {t.name}")
        if tips: print(f"      {tips}")

    while True:
        try:
            choice = input(f"\n选类型 [1-{len(types)}]: ").strip()
            idx = int(choice)-1
            if 0 <= idx < len(types): ct = types[idx]; break
        except: pass
        print("无效")

    print(f"\n已选: [{ct.name}]")
    print(f"扫描课程...")

    courses = scanner.scan_courses(ct)

    if not courses:
        logger.warning("当前无课程数据 (选课窗口未开)")
        enrolled = scanner.scan_enrolled(ct)
        if enrolled:
            print(f"\n已选 ({len(enrolled)}门):")
            for e in enrolled:
                print(f"  {e.get('kcmc','?')} - {e.get('jxbmc',e.get('xmmc','?'))}")
        return ct, []

    # 加载已选课程。注意：同一门课的不同教学班通常 kcdm 相同，
    # 不能用 kcdm 判断“这一行已选”，否则会把同一门课的所有班都误标成 [已选]。
    enrolled_list = scanner.scan_enrolled(ct)
    enrolled_kcrwdm = {str(e.get("kcrwdm","")) for e in enrolled_list if str(e.get("kcrwdm",""))}
    enrolled_jxbdm = {str(e.get("jxbdm","")) for e in enrolled_list if str(e.get("jxbdm",""))}
    enrolled_kcdm = {str(e.get("kcdm","")) for e in enrolled_list if str(e.get("kcdm",""))}
    enrolled_sections = {str(e.get("jxbmc", e.get("xmmc",""))) for e in enrolled_list}
    enrolled_times = []
    for e in enrolled_list:
        et = parse_time(str(e.get("xmmc","")))
        if et: enrolled_times.append(et)

    def is_exact_enrolled(c: Course) -> bool:
        return (
            (c.kcrwdm and c.kcrwdm in enrolled_kcrwdm) or
            (c.jxbdm and c.jxbdm in enrolled_jxbdm) or
            (c.section and c.section in enrolled_sections)
        )

    def is_same_course_selected(c: Course) -> bool:
        return bool(c.kcdm and c.kcdm in enrolled_kcdm)

    # 按课程名称分组
    course_groups = {}
    for c in courses:
        name = c.name or "其他"
        if name not in course_groups: course_groups[name] = []
        course_groups[name].append(c)

    # 只把“有名额且未选过同一门课程”的班放进可选列表。
    # 已经选过同一 kcdm 的其它教学班，前端 JS 也会拦截“你已经选过该课程”，所以不应继续显示成可选。
    available_groups = {}
    duplicate_groups = {}
    for name, clist in course_groups.items():
        avail = [c for c in clist if c.available and not is_same_course_selected(c)]
        dup = [c for c in clist if c.available and is_same_course_selected(c) and not is_exact_enrolled(c)]
        if avail:
            available_groups[name] = avail
        if dup:
            duplicate_groups[name] = dup

    GREEN = '\033[92m'
    RESET = '\033[0m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    CYAN = '\033[96m'

    print(f"\n可选课程 ({sum(len(v) for v in available_groups.values())}个班):")
    if enrolled_list:
        print(f"{GREEN}已选 {len(enrolled_list)}门: {', '.join(e.get('jxbmc',e.get('xmmc','?')) for e in enrolled_list)}{RESET}")
    print()

    idx = 1
    index_map = {}
    for name, clist in sorted(available_groups.items()):
        print(f"  [{idx}] {name} ({len(clist)}个班可选)")
        index_map[idx] = clist
        for c in clist:
            time_str = f" {c.time_info}" if c.time_info else ""
            already = f" {GREEN}[已选]{RESET}" if is_exact_enrolled(c) else ""
            # Check time conflict with enrolled
            conflict = ""
            if not already and c.time_info:
                for et in enrolled_times:
                    if et and et.split('节')[0] == c.time_info.split('节')[0]:
                        conflict = f" {RED}[时间冲突]{RESET}"
                        break
            print(f"       {YELLOW}余{c.remaining:>4}{RESET} | {c.teacher:6s} | {c.section[:35]}{time_str}{already}{conflict}")
        idx += 1

    if duplicate_groups:
        print(f"\n{CYAN}已选同一课程的其它班（不列入可选，直接选会被系统提示“你已经选过该课程”）:{RESET}")
        for name, clist in sorted(duplicate_groups.items()):
            print(f"  - {name} ({len(clist)}个班)")
            for c in clist:
                time_str = f" {c.time_info}" if c.time_info else ""
                print(f"       余{c.remaining:>4} | {c.teacher:6s} | {c.section[:35]}{time_str} {CYAN}[同课程已选]{RESET}")

    if not available_groups:
        print("\n当前没有可重复选择的新课程。")
        return ct, []

    print(f"\n  [1-{len(available_groups)}] 选择课程")
    print(f"  [q] 退出")
    print(f"\n  {GREEN}绿色{RESET}=精确已选班  {YELLOW}黄色{RESET}=有余量  {RED}红色{RESET}=时间冲突  {CYAN}青色{RESET}=同课程已选")

    choices = []
    while True:
        s = input("> ").strip().lower()
        if s == 'q': return ct, []
        try:
            idx = int(s)
            if idx in index_map:
                choices = index_map[idx]
                # 如果有多个班, 让用户选
                if len(choices) > 1:
                    print(f"\n选哪个班?")
                    for i, c in enumerate(choices):
                        print(f"  [{i+1}] {c.teacher} | {c.section} | 余{c.remaining}")
                    s2 = input("> ").strip()
                    try:
                        i2 = int(s2)-1
                        if 0 <= i2 < len(choices):
                            choices = [choices[i2]]
                    except: pass
                break
        except: pass
        print("无效")

    print(f"\n目标: {choices[0]}")
    return ct, choices

# ============================================================
# Part 6: 主入口
# ============================================================
BANNER = """
========================================================
  肇庆学院 全自动抢课系统 v7.0 — 微秒级触发
  登录 → 扫描API → 交互选课 → 异步轮询 → 齐射触发
  QQ群: 1044128566
========================================================"""

def load_config(config_path: str = "config.ini") -> dict:
    cfg = configparser.ConfigParser()
    if Path(config_path).exists():
        cfg.read(config_path, encoding='utf-8')
        return {
            "username": cfg.get("account","username",fallback=""),
            "password": cfg.get("account","password",fallback=""),
            "concurrent": cfg.getint("grab","concurrent",fallback=16),
            "pool_size": cfg.getint("grab","pool_size",fallback=16),
            "poll_ms": cfg.getint("grab","poll_ms",fallback=1),
            "retry_ms": cfg.getint("grab","retry_ms",fallback=250),
            "warmup_ms": cfg.getint("grab","warmup_ms",fallback=300),
            "lead_ms": cfg.getint("grab","lead_ms",fallback=30),
            "burst_count": cfg.getint("grab","burst_count",fallback=5),
            "burst_gap_ms": cfg.getint("grab","burst_gap_ms",fallback=25),
            "mode": cfg.get("grab","mode",fallback="auto"),
            "prefire": cfg.getboolean("grab","prefire",fallback=False),
            "prefire_interval_ms": cfg.getint("grab","prefire_interval_ms",fallback=200),
            "proxy": cfg.get("advanced","proxy",fallback=None) or None,
            "log_level": cfg.get("advanced","log_level",fallback="INFO"),
        }
    return {}

def setup_log(level="INFO"):
    logger.remove()
    logger.add(sys.stderr, level=level, colorize=True,
        format="<green>{time:HH:mm:ss.SSS}</green> | <level>{level: <8}</level> | <level>{message}</level>")

def main():
    import argparse
    p = argparse.ArgumentParser(description="肇庆学院 WebVPN 全自动抢课系统 v7.0")
    p.add_argument("-u","--username", help="学号")
    p.add_argument("-p","--password", help="密码")
    p.add_argument("--pool", type=int, default=None, help="连接池大小")
    p.add_argument("--poll-ms", type=int, default=None, help="轮询间隔(毫秒, 默认读取配置/1ms)")
    p.add_argument("--retry-ms", type=int, default=None, help="提交失败后的重试间隔(毫秒, 默认250)")
    p.add_argument("--warmup-ms", type=int, default=None, help="极速定时模式提前预热毫秒数(默认300)")
    p.add_argument("--lead-ms", type=int, default=None, help="开放前提前多少毫秒开始边界提交(默认30)")
    p.add_argument("--burst-count", type=int, default=None, help="开窗边界爆发提交轮数(默认5)")
    p.add_argument("--burst-gap-ms", type=int, default=None, help="边界爆发每轮间隔毫秒数(默认25)")
    p.add_argument("--mode", choices=["auto","timed","poll"], default=None, help="auto=有窗口时间则定时, timed=强制定时, poll=传统轮询")
    p.add_argument("--prefire", action="store_true", help="开启预发射试探提交(默认关闭)")
    p.add_argument("--prefire-ms", type=int, default=None, help="预发射间隔(毫秒, 默认200)")
    p.add_argument("--login-only", action="store_true")
    p.add_argument("--config", default="config.ini")
    p.add_argument("--proxy", help="HTTP代理")
    p.add_argument("--debug", action="store_true")
    args = p.parse_args()

    cfg = load_config(args.config)
    username = args.username or cfg.get("username","")
    password = args.password or cfg.get("password","")
    pool_size = max(1, args.pool if args.pool is not None else cfg.get("pool_size",16))
    poll_ms = max(1, args.poll_ms if args.poll_ms is not None else cfg.get("poll_ms",1))
    retry_ms = max(200, args.retry_ms if args.retry_ms is not None else cfg.get("retry_ms",250))
    warmup_ms = max(0, args.warmup_ms if args.warmup_ms is not None else cfg.get("warmup_ms",300))
    lead_ms = max(0, args.lead_ms if args.lead_ms is not None else cfg.get("lead_ms",30))
    burst_count = max(1, args.burst_count if args.burst_count is not None else cfg.get("burst_count",5))
    burst_gap_ms = max(1, args.burst_gap_ms if args.burst_gap_ms is not None else cfg.get("burst_gap_ms",25))
    mode = (args.mode or cfg.get("mode","auto") or "auto").lower()
    if mode not in {"auto","timed","poll"}:
        mode = "auto"
    prefire = bool(args.prefire or cfg.get("prefire", False))
    prefire_interval_ms = max(50, args.prefire_ms if args.prefire_ms is not None else cfg.get("prefire_interval_ms",200))
    proxy = args.proxy or cfg.get("proxy") or None
    log_level = "DEBUG" if args.debug else cfg.get("log_level","INFO")

    setup_log(log_level)
    print(BANNER)

    if not username:
        username = input("学号: ").strip()
    if not password:
        password = input("密码: ").strip()
    if not username or not password:
        logger.error("账号密码不能为空!"); return

    # ═══ 登录 (同步) ═══
    logger.info("Step 1/2: VPN 登录")
    s = vpn_login(username, password, proxy)
    if not s: return

    logger.info("Step 2/2: 教务登录")
    if not edu_login(s, username, password): return

    # ═══ 登录完, 显示已选 ═══
    scanner = Scanner(s)
    types = scanner.scan_types()
    if types:
        for t in types:
            enrolled = scanner.scan_enrolled(t)
            if enrolled:
                logger.info(f"[{t.name}] 已选 {len(enrolled)}门:")
                for e in enrolled:
                    logger.info(f"  {e.get('kcmc','?')} - {e.get('jxbmc',e.get('xmmc','?'))}")

    if args.login_only:
        logger.success("登录链路正常!"); return

    # ═══ 交互式选课 ═══
    ct, targets = interactive_select(scanner)

    if ct is None:
        logger.info("没有可用的选课类型, 退出")
        return

    if not targets:
        logger.info(f"[{ct.name}] 当前未选择目标课程 — 进入只读监控模式")
        logger.info("提示: 发现课程后不会自动提交任意课程，请重新运行并选择具体目标。")

    # 校准服务器时间，并选择当前/下一轮选课窗口。
    server_delta = calibrate_server_time(s)
    now_cn = server_now(server_delta).astimezone(CN_TZ)
    selected_window = choose_active_or_next_window(ct.raw, now_cn)
    if selected_window:
        logger.info(
            f"选课窗口: 第{selected_window['stage']}轮 "
            f"{selected_window['start'].strftime('%Y-%m-%d %H:%M:%S')} ~ "
            f"{selected_window['end'].strftime('%Y-%m-%d %H:%M:%S')} "
            f"({selected_window['status']})"
        )
    else:
        logger.warning("未识别到当前或未来选课窗口时间；定时模式将回退到轮询模式。")

    if targets:
        save_target_selection(ct, targets, selected_window)

    use_timed_mode = bool(targets and selected_window and mode in {"auto", "timed"})
    if mode == "timed" and not use_timed_mode:
        logger.warning("强制定时模式条件不足：需要已选择目标课程且能识别选课窗口，已回退轮询/监控。")

    # 提取 cookies 给 aiohttp
    cookies = {k:v for k,v in s.cookies.items()}

    # ═══ 微秒级引擎 ═══
    grabber = MicroGrabber(
        cookies,
        pool_size,
        retry_ms=retry_ms,
        prefire=prefire,
        prefire_interval_ms=prefire_interval_ms,
    )
    grabber._ct = ct
    grabber._targets = targets

    logger.info(f"\n启动微秒级引擎:")
    logger.info(f"  模式: {'极速定时' if use_timed_mode else '轮询'} ({mode})")
    logger.info(f"  连接池: {pool_size} keep-alive")
    logger.info(f"  轮询: {poll_ms}ms ({1000//poll_ms}次/秒)")
    logger.info(f"  失败重试: {retry_ms}ms")
    logger.info(f"  定时预热: {warmup_ms}ms")
    logger.info(f"  边界提前: {lead_ms}ms")
    logger.info(f"  边界爆发: {burst_count}轮 × {burst_gap_ms}ms")
    logger.info(f"  预发射: {'开启' if prefire else '关闭'}" + (f" ({prefire_interval_ms}ms)" if prefire else ""))
    logger.info(f"  目标: {len(targets)}门课")
    logger.info(f"  只提交已选择目标，不会退化为任意课程。")
    logger.info("按 Ctrl+C 停止\n")

    async def run():
        try:
            if use_timed_mode:
                await grabber._timed_fire(
                    ct,
                    targets,
                    selected_window,
                    server_delta,
                    warmup_ms=warmup_ms,
                    lead_ms=lead_ms,
                    burst_count=burst_count,
                    burst_gap_ms=burst_gap_ms,
                )
            else:
                await grabber._warm_up()
                await grabber._wait_and_fire(ct, targets, poll_ms)
        except KeyboardInterrupt:
            logger.info("用户中断")
        finally:
            await grabber._close()

    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        logger.info("已停止")

if __name__ == "__main__":
    main()
