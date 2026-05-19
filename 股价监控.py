# -*- coding: utf-8 -*-
"""股价监控

功能：
1. A 股交易时间内每 10 秒轮询多个股票价格
2. 监控多个 ETF 的溢价/折价
3. 价格到达指定阈值后通过 magicpush 推送消息
4. 提供 Tkinter GUI
5. 配置本地持久化保存到同目录 JSON 文件
6. 非交易时段支持手动获取股票和 ETF 最新行情
7. 手动触发技术指标分析：MACD 顶背离卖出 + RSI<15+BOLL下轨买入

依赖：
- Python 3.9+
- 标准库即可运行（tkinter、urllib、json）

MagicPush 推送接口：
POST {base_url}/api/push/{token}
Body: {"title": "...", "content": "...", "type": "text"}
"""

from __future__ import annotations

import datetime as dt
import json
import math
import queue
import re
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib import parse, request

import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk


DEFAULT_PUSH_BASE_URL = "http://127.0.0.1:3000"
DEFAULT_PUSH_TITLE = "股价监控告警"
POLL_INTERVAL = 10
HTTP_TIMEOUT = 10
CONFIG_FILE = Path(__file__).with_name("股价监控_config.json")


@dataclass
class StockItem:
    code: str
    upper_target: Optional[float] = None
    lower_target: Optional[float] = None
    last_name: str = ""
    last_price: str = ""
    last_time: str = ""


@dataclass
class EtfItem:
    code: str
    premium_threshold: float
    last_name: str = ""
    last_price: str = ""
    last_estimate: str = ""
    last_nav: str = ""
    last_premium: str = ""
    last_time: str = ""


@dataclass
class StockQuote:
    code: str
    name: str
    price: float
    prev_close: Optional[float] = None
    quote_time: Optional[str] = None


@dataclass
class EtfQuote:
    code: str
    name: str
    price: float  # 市场最新价
    nav: float
    estimated_nav: float
    premium_pct: float
    quote_time: Optional[str] = None


@dataclass
class KLine:
    date: str
    open: float
    close: float
    high: float
    low: float
    volume: float


@dataclass
class MonitorConfig:
    stocks: List[StockItem]
    etfs: List[EtfItem]
    push_base_url: str
    push_token: str
    push_title: str



class MonitorState:
    def __init__(self) -> None:
        self.stock_upper_date: Dict[str, str] = {}
        self.stock_lower_date: Dict[str, str] = {}
        self.etf_high_date: Dict[str, str] = {}
        self.etf_low_date: Dict[str, str] = {}
        self.macd_sell_active: Dict[str, bool] = {}
        self.rsi_buy_active: Dict[str, bool] = {}
        self.last_not_trading_day: Optional[str] = None
        self.kline_cache: Dict[str, List[KLine]] = {}
        self.kline_cache_time: Dict[str, float] = {}


def normalize_code(code: str) -> str:
    digits = re.sub(r"\D", "", code or "")
    return digits.zfill(6) if digits else ""


def fmt_price(value: Optional[float]) -> str:
    if value is None:
        return ""
    if abs(value) < 100:
        return f"{value:.4f}"
    return f"{value:g}"


def market_prefix(code: str) -> str:
    code = normalize_code(code)
    if not code:
        return ""
    if code.startswith(("5", "6", "9")):
        return "sh"
    return "sz"


def is_trading_time(now: Optional[dt.datetime] = None) -> bool:
    now = now or dt.datetime.now()
    if now.weekday() >= 5:
        return False
    t = now.time()
    morning_start = dt.time(9, 30)
    morning_end = dt.time(11, 30)
    afternoon_start = dt.time(13, 0)
    afternoon_end = dt.time(15, 0)
    return (morning_start <= t <= morning_end) or (afternoon_start <= t <= afternoon_end)


def http_get(url: str, timeout: int = HTTP_TIMEOUT, headers: Optional[dict] = None) -> bytes:
    req = request.Request(url, headers=headers or {"User-Agent": "Mozilla/5.0"})
    with request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()
    return data



def decode_http_text(data: bytes, encoding: str = "utf-8") -> str:
    return data.decode(encoding, errors="ignore")



def http_post_json(url: str, payload: dict, timeout: int = HTTP_TIMEOUT, headers: Optional[dict] = None) -> str:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req_headers = {"Content-Type": "application/json; charset=utf-8", "User-Agent": "Mozilla/5.0"}
    if headers:
        req_headers.update(headers)
    req = request.Request(url, data=body, headers=req_headers, method="POST")
    with request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()
    return data.decode("utf-8", errors="ignore")



def clean_security_name(name: str, fallback: str) -> str:
    cleaned = (name or "").strip().strip("\ufeff").replace("\u3000", " ")
    if not cleaned or cleaned.lower() in {"null", "none"}:
        return fallback
    return cleaned



def parse_sina_quote_text(code: str, raw: str) -> StockQuote:
    match = re.search(r'="([^"]*)";', raw)
    if not match:
        raise ValueError("未能解析行情数据")
    values = match.group(1).split(",")
    if len(values) < 4:
        raise ValueError("行情字段不足")

    name = clean_security_name(values[0], code)
    price_text = values[3].strip()
    if not price_text:
        raise ValueError("未获取到最新价格")
    price = float(price_text)

    prev_close = None
    try:
        prev_close = float(values[2]) if values[2] else None
    except ValueError:
        prev_close = None

    quote_time = None
    if len(values) >= 32:
        date_text = values[30].strip()
        time_text = values[31].strip()
        if date_text or time_text:
            quote_time = f"{date_text} {time_text}".strip()

    return StockQuote(code=code, name=name, price=price, prev_close=prev_close, quote_time=quote_time)



def fetch_stock_quote(code: str) -> StockQuote:
    code = normalize_code(code)
    if not code:
        raise ValueError("股票代码不能为空")
    prefix = market_prefix(code)
    if not prefix:
        raise ValueError("无法识别股票代码所属市场")
    url = f"https://hq.sinajs.cn/list={prefix}{code}"
    raw = decode_http_text(http_get(url, timeout=HTTP_TIMEOUT, headers={"Referer": "https://finance.sina.com.cn"}), "gb18030")
    if "=" not in raw:
        raise ValueError("未获取到股票行情")
    return parse_sina_quote_text(code, raw)



def parse_fundgz_response(code: str, raw: str) -> Tuple[str, float, float, Optional[str]]:
    match = re.search(r"\{.*\}", raw)
    if not match:
        raise ValueError("未能解析 ETF 溢价数据")
    data = json.loads(match.group(0))

    name = clean_security_name(data.get("name") or "", code)
    nav = float(data["dwjz"])
    estimated_nav = float(data["gsz"])
    quote_time = data.get("gztime") or None
    return name, nav, estimated_nav, quote_time


def fetch_etf_quote(code: str) -> EtfQuote:
    code = normalize_code(code)
    if not code:
        raise ValueError("ETF 代码不能为空")

    # ETF 需要同时获取市场最新价和基金估值/净值
    market_quote = fetch_stock_quote(code)
    url = f"https://fundgz.1234567.com.cn/js/{code}.js?rt={int(time.time())}"
    raw = decode_http_text(http_get(url, timeout=HTTP_TIMEOUT, headers={"Referer": "https://fund.eastmoney.com"}), "utf-8")
    name, nav, estimated_nav, estimate_time = parse_fundgz_response(code, raw)

    premium_pct = (market_quote.price - nav) / nav * 100 if nav else 0.0
    quote_time = market_quote.quote_time or estimate_time
    return EtfQuote(
        code=code,
        name=name if name != code else market_quote.name,
        price=market_quote.price,
        nav=nav,
        estimated_nav=estimated_nav,
        premium_pct=premium_pct,
        quote_time=quote_time,
    )



def build_push_url(base_url: str, token: str) -> str:
    base = (base_url or "").strip().rstrip("/")
    if not base:
        raise ValueError("MagicPush 服务地址不能为空")
    if not token.strip():
        raise ValueError("MagicPush Token 不能为空")
    if base.endswith("/api/push"):
        return f"{base}/{token.strip()}"
    return f"{base}/api/push/{token.strip()}"


def send_magicpush(base_url: str, token: str, title: str, content: str) -> Tuple[bool, str]:
    url = build_push_url(base_url, token)
    payload = {"title": title, "content": content, "type": "text"}
    try:
        resp = http_post_json(url, payload, timeout=HTTP_TIMEOUT)
        return True, resp
    except Exception as exc:  # noqa: BLE001
        return False, str(exc)


KLINE_CACHE_DURATION = 300  # 5 分钟


SEARCH_TOKEN = "D43BF722C8E33BDC906FB84D85E326E8"


def search_security(query: str) -> Tuple[str, str, str]:
    """搜索证券代码/名称，返回 (code, name, type)，type 为 stock/etf/gp 等。
    优先按代码搜索，否则按名称搜索。
    """
    raw_input = query.strip()
    code = normalize_code(raw_input)
    if code:
        # 直接查行情获取名称
        try:
            quote = fetch_stock_quote(code)
            return code, quote.name, "stock"
        except Exception:
            # 代码可能是 ETF，试试 ETF 接口
            try:
                etf = fetch_etf_premium(code)
                return code, etf.name, "etf"
            except Exception:
                pass
            # 放弃，让 API 搜
    # 按名称搜索（或代码搜不到时转名称搜）
    try:
        url = (
            f"https://searchadapter.eastmoney.com/api/suggest/get"
            f"?input={parse.quote(raw_input)}&type=14&token={SEARCH_TOKEN}"
        )
        raw = decode_http_text(http_get(url, timeout=HTTP_TIMEOUT), "utf-8")
        data = json.loads(raw)
        table = data.get("QuotationCodeTable") or {}
        items = table.get("Data") or []
        if not items:
            raise ValueError(f"未找到匹配的证券：{raw_input}")
        item = items[0]
        result_code = normalize_code(str(item.get("Code", "")))
        result_name = str(item.get("Name", ""))
        sec_type = str(item.get("SecurityTypeName", "") or item.get("Type", "") or "")
        if not result_code:
            raise ValueError(f"搜索结果无有效代码：{raw_input}")
        return result_code, result_name, sec_type.lower()
    except Exception as exc:
        raise ValueError(f"搜索失败：{exc}") from exc


def fetch_kline(code: str, count: int = 120) -> List[KLine]:
    """获取日 K 线数据（新浪 API），返回最近 count 根。最多重试 3 次。"""
    code = normalize_code(code)
    if not code:
        raise ValueError("代码不能为空")
    prefix = market_prefix(code)
    if not prefix:
        raise ValueError("无法识别代码所属市场")
    url = (
        f"https://money.finance.sina.com.cn/quotes_service/api/json_v2.php"
        f"/CN_MarketData.getKLineData?symbol={prefix}{code}"
        f"&scale=240&ma=no&datalen={count}"
    )
    last_err: Optional[Exception] = None
    for attempt in range(3):
        try:
            raw = decode_http_text(http_get(url, timeout=HTTP_TIMEOUT * 2, headers={
                "Referer": "https://finance.sina.com.cn",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            }), "utf-8")
            data = json.loads(raw)
            if not isinstance(data, list) or len(data) < 20:
                last_err = ValueError(f"K 线数据不足 ({len(data) if isinstance(data, list) else 0})")
                time.sleep(1 * (attempt + 1))
                continue
            klines: List[KLine] = []
            for item in data:
                klines.append(KLine(
                    date=str(item.get("day", "")),
                    open=float(item.get("open", 0)),
                    close=float(item.get("close", 0)),
                    high=float(item.get("high", 0)),
                    low=float(item.get("low", 0)),
                    volume=float(item.get("volume", item.get("moneytimes", 0))),
                ))
            return klines
        except Exception as exc:
            last_err = exc
            time.sleep(1.5 * (attempt + 1))
    raise last_err or ValueError(f"获取 K 线失败：{code}")


def calc_ema(data: List[float], period: int) -> List[float]:
    ema: List[float] = []
    multiplier = 2.0 / (period + 1)
    for i, val in enumerate(data):
        if i == 0:
            ema.append(val)
        else:
            ema.append((val - ema[-1]) * multiplier + ema[-1])
    return ema


def calc_sma(data: List[float], period: int) -> List[float]:
    result: List[float] = []
    for i in range(len(data)):
        if i < period - 1:
            result.append(0.0)
        else:
            result.append(sum(data[i - period + 1:i + 1]) / period)
    return result


def calc_macd(closes: List[float]) -> Tuple[List[float], List[float], List[float]]:
    ema12 = calc_ema(closes, 12)
    ema26 = calc_ema(closes, 26)
    dif = [ema12[i] - ema26[i] for i in range(len(closes))]
    dea = calc_ema(dif, 9)
    macd_hist = [2 * (dif[i] - dea[i]) for i in range(len(closes))]
    return dif, dea, macd_hist


def calc_rsi(closes: List[float], period: int = 14) -> List[float]:
    rsi: List[float] = [50.0] * len(closes)
    gains: List[float] = []
    losses: List[float] = []
    for i in range(1, len(closes)):
        change = closes[i] - closes[i - 1]
        gains.append(change if change > 0 else 0.0)
        losses.append(-change if change < 0 else 0.0)
    for i in range(period, len(closes)):
        avg_gain = sum(gains[i - period:i]) / period
        avg_loss = sum(losses[i - period:i]) / period
        if avg_loss == 0:
            rsi[i] = 100.0
        else:
            rs = avg_gain / avg_loss
            rsi[i] = 100.0 - 100.0 / (1 + rs)
    return rsi


def calc_boll(closes: List[float], period: int = 20) -> Tuple[List[float], List[float], List[float]]:
    middle = calc_sma(closes, period)
    upper: List[float] = []
    lower: List[float] = []
    for i in range(len(closes)):
        if i < period - 1:
            upper.append(0.0)
            lower.append(0.0)
        else:
            window = closes[i - period + 1:i + 1]
            std = math.sqrt(sum((x - middle[i]) ** 2 for x in window) / period)
            upper.append(middle[i] + 2 * std)
            lower.append(middle[i] - 2 * std)
    return middle, upper, lower


def find_peaks(values: List[float], order: int = 3) -> List[int]:
    """找出局部极值点的索引（peak 指极大值）。"""
    peaks: List[int] = []
    for i in range(order, len(values) - order):
        if all(values[i] >= values[i - j] for j in range(1, order + 1)) and \
           all(values[i] >= values[i + j] for j in range(1, order + 1)):
            peaks.append(i)
    return peaks


def check_macd_top_divergence(klines: List[KLine], dif: List[float]) -> bool:
    """MACD 顶背离：价格创新高但 DIF 未创新高（最近两根明显峰比较）。"""
    if len(klines) < 30 or len(dif) < 30:
        return False
    closes = [k.close for k in klines]
    price_peaks = find_peaks(closes, order=3)
    if len(price_peaks) < 2:
        return False
    p2, p1 = price_peaks[-2], price_peaks[-1]

    # 在 DIF 上找对应的峰索引范围内寻找
    dif_peaks = find_peaks(dif, order=2)
    if len(dif_peaks) < 2:
        return False
    dp2, dp1 = dif_peaks[-2], dif_peaks[-1]

    # 价格后峰高于前峰，DIF 后峰低于前峰
    if closes[p1] > closes[p2] and dif[dp1] < dif[dp2]:
        return True
    return False


def check_rsi_boll_buy(closes: List[float], rsi: List[float], boll_lower: List[float]) -> bool:
    """RSI<15 且价格 <= BOLL 下轨。"""
    if len(closes) < 3 or len(rsi) < 3 or len(boll_lower) < 3:
        return False
    price = closes[-1]
    return rsi[-1] < 15 and boll_lower[-1] > 0 and price <= boll_lower[-1]


def load_config() -> MonitorConfig:
    if not CONFIG_FILE.exists():
        return MonitorConfig(stocks=[], etfs=[], push_base_url=DEFAULT_PUSH_BASE_URL, push_token="", push_title=DEFAULT_PUSH_TITLE)

    with CONFIG_FILE.open("r", encoding="utf-8") as f:
        raw = json.load(f)

    stocks: List[StockItem] = []
    for item in raw.get("stocks", []):
        code = normalize_code(item.get("code", ""))
        if not code:
            continue

        # 兼容旧配置：target + direction
        if "target" in item or "direction" in item:
            target = item.get("target")
            direction = str(item.get("direction", "above")).lower()
            upper_target = float(target) if direction == "above" and target not in (None, "") else None
            lower_target = float(target) if direction == "below" and target not in (None, "") else None
        else:
            upper_raw = item.get("upper_target")
            lower_raw = item.get("lower_target")
            upper_target = float(upper_raw) if upper_raw not in (None, "") else None
            lower_target = float(lower_raw) if lower_raw not in (None, "") else None

        stocks.append(StockItem(
            code=code,
            upper_target=upper_target,
            lower_target=lower_target,
            last_name=str(item.get("last_name", "")),
            last_price=str(item.get("last_price", "")),
            last_time=str(item.get("last_time", "")),
        ))

    etfs: List[EtfItem] = []
    for item in raw.get("etfs", []):
        code = normalize_code(item.get("code", ""))
        if not code:
            continue
        etfs.append(EtfItem(
            code=code,
            premium_threshold=float(item.get("premium_threshold", 0)),
            last_name=str(item.get("last_name", "")),
            last_price=str(item.get("last_price", "")),
            last_estimate=str(item.get("last_estimate", "")),
            last_nav=str(item.get("last_nav", "")),
            last_premium=str(item.get("last_premium", "")),
            last_time=str(item.get("last_time", "")),
        ))

    push = raw.get("push", {})
    return MonitorConfig(
        stocks=stocks,
        etfs=etfs,
        push_base_url=str(push.get("base_url", DEFAULT_PUSH_BASE_URL)),
        push_token=str(push.get("token", "")),
        push_title=str(push.get("title", DEFAULT_PUSH_TITLE)),
    )



def save_config(config: MonitorConfig) -> None:
    data = {
        "stocks": [asdict(item) for item in config.stocks],
        "etfs": [asdict(item) for item in config.etfs],
        "push": {
            "base_url": config.push_base_url,
            "token": config.push_token,
            "title": config.push_title,
        },
        "updated_at": dt.datetime.now().isoformat(timespec="seconds"),
    }
    with CONFIG_FILE.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


class StockMonitorApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("股价监控")
        self.geometry("1220x820")
        self.minsize(1100, 740)

        self.log_queue: queue.Queue[str] = queue.Queue()
        self.push_log_queue: queue.Queue[str] = queue.Queue()
        self.ui_queue: queue.Queue[Tuple[str, tuple]] = queue.Queue()
        self.running = False
        self.worker: Optional[threading.Thread] = None
        self.state = MonitorState()

        self.stock_code_var = tk.StringVar(value="")
        self.stock_upper_var = tk.StringVar(value="")
        self.stock_lower_var = tk.StringVar(value="")
        self.etf_code_var = tk.StringVar(value="")
        self.etf_threshold_var = tk.StringVar(value="")
        self.push_base_url_var = tk.StringVar(value=DEFAULT_PUSH_BASE_URL)
        self.push_token_var = tk.StringVar(value="")
        self.push_title_var = tk.StringVar(value=DEFAULT_PUSH_TITLE)
        self.status_var = tk.StringVar(value="就绪")
        self.config_hint_var = tk.StringVar(value=f"配置文件：{CONFIG_FILE.name}")

        self.stock_tree: ttk.Treeview
        self.etf_tree: ttk.Treeview
        self.log_text: scrolledtext.ScrolledText
        self.push_log_text: scrolledtext.ScrolledText

        self._build_ui()
        self._load_saved_config_to_ui()
        self.after(300, self._drain_queues)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_ui(self) -> None:
        self.configure(bg="#f4f6fb")
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TFrame", background="#f4f6fb")
        style.configure("TLabel", background="#f4f6fb", font=("Microsoft YaHei UI", 10))
        style.configure("TButton", font=("Microsoft YaHei UI", 10, "bold"))
        style.configure("Header.TLabel", font=("Microsoft YaHei UI", 16, "bold"), foreground="#1f2a44")
        style.configure("Sub.TLabel", font=("Microsoft YaHei UI", 9), foreground="#5d6982")
        style.configure("TLabelframe", background="#f4f6fb")
        style.configure("TLabelframe.Label", background="#f4f6fb", font=("Microsoft YaHei UI", 10, "bold"))

        outer = ttk.Frame(self, padding=14)
        outer.pack(fill="both", expand=True)

        header = ttk.Frame(outer)
        header.pack(fill="x", pady=(0, 10))
        ttk.Label(header, text="股价监控", style="Header.TLabel").pack(anchor="w")
        ttk.Label(
            header,
            text="输入股票/ETF 代码或名称可自动搜索匹配；设置涨破/跌破价留空则不监控该方向。",
            style="Sub.TLabel",
        ).pack(anchor="w", pady=(2, 0))

        main = ttk.Frame(outer)
        main.pack(fill="both", expand=False)

        left = ttk.Labelframe(main, text="监控列表", padding=10)
        left.pack(side="left", fill="both", expand=True, padx=(0, 8))
        right = ttk.Labelframe(main, text="推送配置", padding=10)
        right.pack(side="left", fill="both", expand=True, padx=(8, 0))

        self._build_monitor_section(left)
        self._build_push_section(right)

        actions = ttk.Frame(outer)
        actions.pack(fill="x", pady=(12, 10))
        ttk.Button(actions, text="保存配置", command=self.save_ui_config).pack(side="left")
        ttk.Button(actions, text="手动刷新行情", command=self.manual_refresh).pack(side="left", padx=8)
        ttk.Button(actions, text="技术指标分析", command=self.manual_technicals).pack(side="left", padx=8)
        ttk.Button(actions, text="开始监控", command=self.start_monitoring).pack(side="left", padx=8)
        ttk.Button(actions, text="停止监控", command=self.stop_monitoring).pack(side="left", padx=8)
        ttk.Button(actions, text="测试推送", command=self.test_push).pack(side="left", padx=8)
        ttk.Label(actions, textvariable=self.status_var, style="Sub.TLabel").pack(side="right")

        log_frame = ttk.Labelframe(outer, text="日志", padding=8)
        log_frame.pack(fill="both", expand=True)
        self.log_text = scrolledtext.ScrolledText(
            log_frame,
            height=14,
            font=("Consolas", 10),
            wrap="word",
            bg="#0f172a",
            fg="#dbeafe",
            insertbackground="#ffffff",
        )
        self.log_text.pack(fill="both", expand=True)
        self.log_text.configure(state="disabled")

        footer = ttk.Frame(outer)
        footer.pack(fill="x", pady=(8, 0))
        ttk.Label(footer, textvariable=self.config_hint_var, style="Sub.TLabel").pack(side="left")
        ttk.Label(footer, text="自动监控仅在 A 股交易时段运行；手动刷新不受交易时段限制。", style="Sub.TLabel").pack(side="right")

    def _build_monitor_section(self, parent: ttk.Labelframe) -> None:
        stock_add = ttk.Frame(parent)
        stock_add.pack(fill="x", pady=(0, 6))
        ttk.Label(stock_add, text="股票代码").pack(side="left")
        entry_code = ttk.Entry(stock_add, textvariable=self.stock_code_var, width=10)
        entry_code.pack(side="left", padx=(4, 8))
        ttk.Label(stock_add, text="涨破价").pack(side="left")
        ttk.Entry(stock_add, textvariable=self.stock_upper_var, width=10).pack(side="left", padx=(4, 8))
        ttk.Label(stock_add, text="跌破价").pack(side="left")
        ttk.Entry(stock_add, textvariable=self.stock_lower_var, width=10).pack(side="left", padx=(4, 8))
        ttk.Button(stock_add, text="添加股票", command=self.add_stock).pack(side="left")
        ttk.Button(stock_add, text="删除选中", command=self.remove_selected_stock).pack(side="left", padx=6)

        stock_columns = ("code", "upper", "lower", "name", "price", "time")
        self.stock_tree = ttk.Treeview(parent, columns=stock_columns, show="headings", height=8)
        self.stock_tree.pack(fill="both", expand=True, pady=(0, 10))
        for key, title, width in [
            ("code", "代码", 90),
            ("upper", "涨破价", 90),
            ("lower", "跌破价", 90),
            ("name", "名称", 140),
            ("price", "最新价", 90),
            ("time", "行情时间", 170),
        ]:
            self.stock_tree.heading(key, text=title)
            self.stock_tree.column(key, width=width, anchor="center")
        self._setup_cell_edit(self.stock_tree, {"upper", "lower"})

        etf_add = ttk.Frame(parent)
        etf_add.pack(fill="x", pady=(0, 6))
        ttk.Label(etf_add, text="ETF代码").pack(side="left")
        ttk.Entry(etf_add, textvariable=self.etf_code_var, width=10).pack(side="left", padx=(4, 8))
        ttk.Label(etf_add, text="溢价阈值(%)").pack(side="left")
        ttk.Entry(etf_add, textvariable=self.etf_threshold_var, width=10).pack(side="left", padx=(4, 8))
        ttk.Button(etf_add, text="添加ETF", command=self.add_etf).pack(side="left")
        ttk.Button(etf_add, text="删除选中", command=self.remove_selected_etf).pack(side="left", padx=6)

        etf_columns = ("code", "threshold", "name", "market_price", "estimate", "nav", "premium", "time")
        self.etf_tree = ttk.Treeview(parent, columns=etf_columns, show="headings", height=7)
        self.etf_tree.pack(fill="both", expand=True)
        for key, title, width in [
            ("code", "代码", 90),
            ("threshold", "阈值%", 80),
            ("name", "名称", 140),
            ("market_price", "最新价", 80),
            ("estimate", "估值", 80),
            ("nav", "净值", 80),
            ("premium", "溢价%", 80),
            ("time", "行情时间", 170),
        ]:
            self.etf_tree.heading(key, text=title)
            self.etf_tree.column(key, width=width, anchor="center")

    def _build_push_section(self, parent: ttk.Labelframe) -> None:
        rows = ttk.Frame(parent)
        rows.pack(fill="x")
        self._add_row(rows, 0, "MagicPush 地址", self.push_base_url_var, "http://127.0.0.1:3000")
        self._add_row(rows, 1, "Token", self.push_token_var, "接口令牌")
        self._add_row(rows, 2, "推送标题", self.push_title_var, "股价触发告警")
        ttk.Label(
            parent,
            text="调用：POST {base_url}/api/push/{token}",
            style="Sub.TLabel",
            wraplength=380,
            justify="left",
        ).pack(anchor="w", pady=(6, 0))
        ttk.Separator(parent, orient="horizontal").pack(fill="x", pady=(8, 6))
        ttk.Label(parent, text="推送记录", style="Sub.TLabel").pack(anchor="w")
        self.push_log_text = scrolledtext.ScrolledText(
            parent,
            height=10,
            font=("Consolas", 9),
            wrap="word",
            bg="#0f172a",
            fg="#86efac",
            insertbackground="#ffffff",
        )
        self.push_log_text.pack(fill="both", expand=True)
        self.push_log_text.configure(state="disabled")

    def _setup_cell_edit(self, tree: ttk.Treeview, editable_columns: set) -> None:
        """双击可编辑列弹出 Entry 直接修改，修改后自动保存配置。"""

        def on_double_click(event: tk.Event) -> None:
            region = tree.identify_region(event.x, event.y)
            if region != "cell":
                return
            col_id = tree.identify_column(event.x)
            col_key = tree.column(col_id, "id")
            if col_key not in editable_columns:
                return
            iid = tree.identify_row(event.y)
            if not iid:
                return
            x, y, w, h = tree.bbox(iid, col_id)
            current = tree.set(iid, col_key)

            entry = tk.Entry(tree, borderwidth=1, relief="solid", justify="center")
            entry.place(x=x, y=y, width=w, height=h + 2)
            entry.insert(0, current if current.strip() != "" else "")
            entry.focus_set()
            entry.selection_range(0, "end")

            def commit() -> None:
                new_val = entry.get().strip()
                try:
                    entry.destroy()
                except tk.TclError:
                    pass
                if new_val == "":
                    tree.set(iid, col_key, "")
                else:
                    try:
                        float(new_val)
                        tree.set(iid, col_key, new_val)
                    except ValueError:
                        pass
                self.save_ui_config(show_message=False)

            entry.bind("<Return>", lambda e: commit())
            entry.bind("<FocusOut>", lambda e: tree.after(200, commit))

        tree.bind("<Double-1>", on_double_click)

    def _add_row(self, parent: ttk.Frame, row: int, label: str, variable: tk.StringVar, placeholder: str) -> None:
        container = ttk.Frame(parent)
        container.grid(row=row, column=0, sticky="ew", pady=5)
        container.columnconfigure(1, weight=1)
        ttk.Label(container, text=label, width=14).grid(row=0, column=0, sticky="w")
        entry = ttk.Entry(container, textvariable=variable, width=34)
        entry.grid(row=0, column=1, sticky="ew", padx=(0, 8))
        ttk.Label(container, text=placeholder, style="Sub.TLabel").grid(row=0, column=2, sticky="w")

    def _append_log(self, text: str) -> None:
        timestamp = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.log_queue.put(f"[{timestamp}] {text}")

    def _append_push_log(self, text: str) -> None:
        """推送记录专用日志，同时写入通用日志。"""
        timestamp = dt.datetime.now().strftime("%H:%M:%S")
        self.push_log_queue.put(f"[{timestamp}] {text}")
        self._append_log(text)

    def _drain_queues(self) -> None:
        try:
            while True:
                line = self.log_queue.get_nowait()
                self.log_text.configure(state="normal")
                self.log_text.insert("end", line + "\n")
                self.log_text.see("end")
                self.log_text.configure(state="disabled")
        except queue.Empty:
            pass

        try:
            while True:
                action, args = self.ui_queue.get_nowait()
                if action == "stock":
                    self._update_stock_row(*args)
                elif action == "etf":
                    self._update_etf_row(*args)
                elif action == "status":
                    self.status_var.set(args[0])
        except queue.Empty:
            pass

        try:
            while True:
                line = self.push_log_queue.get_nowait()
                self.push_log_text.configure(state="normal")
                self.push_log_text.insert("end", line + "\n")
                self.push_log_text.see("end")
                self.push_log_text.configure(state="disabled")
        except queue.Empty:
            pass

        self.after(300, self._drain_queues)

    def add_stock(self) -> None:
        raw = self.stock_code_var.get().strip()
        if not raw:
            messagebox.showerror("输入错误", "请输入股票代码或名称")
            return
        try:
            code, name, _ = search_security(raw)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("搜索失败", str(exc))
            return

        upper_raw = self.stock_upper_var.get().strip()
        lower_raw = self.stock_lower_var.get().strip()
        upper: Optional[float] = None
        lower: Optional[float] = None
        if upper_raw:
            try:
                upper = float(upper_raw)
            except ValueError:
                messagebox.showerror("输入错误", "涨破价必须是数字")
                return
        if lower_raw:
            try:
                lower = float(lower_raw)
            except ValueError:
                messagebox.showerror("输入错误", "跌破价必须是数字")
                return
        if upper is None and lower is None:
            messagebox.showerror("输入错误", "请至少设置涨破价或跌破价中的一个")
            return

        values = (code, fmt_price(upper), fmt_price(lower), name, "", "")
        if code in self.stock_tree.get_children(""):
            self.stock_tree.item(code, values=values)
            self._append_log(f"已更新股票：{code} {name}")
        else:
            self.stock_tree.insert("", "end", iid=code, values=values)
            self._append_log(f"已添加股票：{code} {name}")
        self.stock_code_var.set("")
        self.stock_upper_var.set("")
        self.stock_lower_var.set("")
        self.save_ui_config(show_message=False)

    def add_etf(self) -> None:
        raw = self.etf_code_var.get().strip()
        if not raw:
            messagebox.showerror("输入错误", "请输入 ETF 代码或名称")
            return
        try:
            code, name, _ = search_security(raw)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("搜索失败", str(exc))
            return

        try:
            threshold = float(self.etf_threshold_var.get().strip())
        except ValueError:
            messagebox.showerror("输入错误", "ETF 溢价阈值必须是数字")
            return
        if code in self.etf_tree.get_children(""):
            self.etf_tree.item(code, values=(code, f"{threshold:g}", name, "", "", "", "", ""))
            self._append_log(f"已更新 ETF：{code} {name}")
        else:
            self.etf_tree.insert("", "end", iid=code, values=(code, f"{threshold:g}", name, "", "", "", "", ""))
            self._append_log(f"已添加 ETF：{code} {name}")
        self.etf_code_var.set("")
        self.etf_threshold_var.set("")
        self.save_ui_config(show_message=False)

    def remove_selected_stock(self) -> None:
        for iid in self.stock_tree.selection():
            self.stock_tree.delete(iid)
            self._append_log(f"已删除股票：{iid}")
        self.save_ui_config(show_message=False)

    def remove_selected_etf(self) -> None:
        for iid in self.etf_tree.selection():
            self.etf_tree.delete(iid)
            self._append_log(f"已删除 ETF：{iid}")
        self.save_ui_config(show_message=False)

    def _load_saved_config_to_ui(self) -> None:
        try:
            config = load_config()
        except Exception as exc:  # noqa: BLE001
            self._append_log(f"读取本地配置失败，使用默认值：{exc}")
            return

        self.push_base_url_var.set(config.push_base_url)
        self.push_token_var.set(config.push_token)
        self.push_title_var.set(config.push_title)

        for item in config.stocks:
            self.stock_tree.insert("", "end", iid=item.code, values=(
                item.code,
                fmt_price(item.upper_target),
                fmt_price(item.lower_target),
                item.last_name,
                item.last_price,
                item.last_time,
            ))
        for item in config.etfs:
            self.etf_tree.insert("", "end", iid=item.code, values=(
                item.code,
                f"{item.premium_threshold:g}",
                item.last_name,
                item.last_price,
                item.last_estimate,
                item.last_nav,
                item.last_premium,
                item.last_time,
            ))
        if config.stocks or config.etfs:
            self._append_log(f"已加载本地配置：{CONFIG_FILE}")

    def _read_config_from_ui(self, require_items: bool = True, require_push: bool = True) -> MonitorConfig:
        stocks: List[StockItem] = []
        for iid in self.stock_tree.get_children(""):
            vals = self.stock_tree.item(iid, "values")
            upper: Optional[float] = None
            lower: Optional[float] = None
            try:
                if vals[1].strip():
                    upper = float(vals[1])
            except ValueError:
                pass
            try:
                if vals[2].strip():
                    lower = float(vals[2])
            except ValueError:
                pass
            stocks.append(StockItem(
                code=normalize_code(vals[0]),
                upper_target=upper,
                lower_target=lower,
                last_name=str(vals[3]) if len(vals) > 3 and vals[3] else "",
                last_price=str(vals[4]) if len(vals) > 4 and vals[4] else "",
                last_time=str(vals[5]) if len(vals) > 5 and vals[5] else "",
            ))

        etfs: List[EtfItem] = []
        for iid in self.etf_tree.get_children(""):
            vals = self.etf_tree.item(iid, "values")
            etfs.append(EtfItem(
                code=normalize_code(vals[0]),
                premium_threshold=float(vals[1]),
                last_name=str(vals[2]) if len(vals) > 2 and vals[2] else "",
                last_price=str(vals[3]) if len(vals) > 3 and vals[3] else "",
                last_estimate=str(vals[4]) if len(vals) > 4 and vals[4] else "",
                last_nav=str(vals[5]) if len(vals) > 5 and vals[5] else "",
                last_premium=str(vals[6]) if len(vals) > 6 and vals[6] else "",
                last_time=str(vals[7]) if len(vals) > 7 and vals[7] else "",
            ))

        if require_items and not stocks and not etfs:
            raise ValueError("请至少添加一个股票或 ETF 监控项")

        push_base_url = self.push_base_url_var.get().strip()
        push_token = self.push_token_var.get().strip()
        push_title = self.push_title_var.get().strip() or DEFAULT_PUSH_TITLE
        if require_push:
            if not push_base_url:
                raise ValueError("MagicPush 地址不能为空")
            if not push_token:
                raise ValueError("MagicPush Token 不能为空")

        return MonitorConfig(
            stocks=stocks,
            etfs=etfs,
            push_base_url=push_base_url,
            push_token=push_token,
            push_title=push_title,
        )

    def save_ui_config(self, show_message: bool = True) -> None:
        try:
            config = self._read_config_from_ui(require_items=False, require_push=False)
            save_config(config)
        except Exception as exc:  # noqa: BLE001
            if show_message:
                messagebox.showerror("保存失败", str(exc))
            return
        if show_message:
            self._append_log(f"配置已保存到：{CONFIG_FILE}")

    def start_monitoring(self) -> None:
        if self.running:
            self._append_log("监控已经在运行中")
            return
        try:
            config = self._read_config_from_ui(require_items=True, require_push=True)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("配置错误", str(exc))
            return

        save_config(config)
        self.running = True
        self.worker = threading.Thread(target=self._monitor_loop, args=(config,), daemon=True)
        self.worker.start()
        self.status_var.set("监控中")
        self._append_log("开始监控")

    def stop_monitoring(self) -> None:
        if not self.running:
            self._append_log("当前没有运行中的监控")
            return
        self.running = False
        self.status_var.set("已停止")
        self._append_log("停止监控")

    def test_push(self) -> None:
        try:
            config = self._read_config_from_ui(require_items=False, require_push=True)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("配置错误", str(exc))
            return

        def worker() -> None:
            ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, "这是一条测试推送消息。")
            self._append_push_log("测试推送")

        threading.Thread(target=worker, daemon=True).start()

    def manual_refresh(self) -> None:
        try:
            config = self._read_config_from_ui(require_items=True, require_push=False)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("配置错误", str(exc))
            return
        self.status_var.set("手动刷新中")
        self._append_log("开始手动刷新行情（不受交易时段限制）")
        threading.Thread(target=self._refresh_quotes, args=(config,), daemon=True).start()

    def manual_technicals(self) -> None:
        """手动触发技术指标分析，点按后执行所有股票的 MACD 顶背离和 RSI+BOLL 判断，符合条件的推送。"""
        try:
            config = self._read_config_from_ui(require_items=True, require_push=False)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("配置错误", str(exc))
            return
        self.state.macd_sell_active.clear()
        self.state.rsi_buy_active.clear()
        self.status_var.set("分析中")
        self._append_log("开始技术指标分析...")
        now = dt.datetime.now()
        threading.Thread(target=self._refresh_technicals, args=(config, now), daemon=True).start()

    def _refresh_quotes(self, config: MonitorConfig) -> None:
        for stock_item in config.stocks:
            try:
                stock = fetch_stock_quote(stock_item.code)
                self.ui_queue.put(("stock", (stock, stock_item)))
                self._append_log(self._stock_log_line(stock))
            except Exception as exc:
                self._append_log(f"股票 {stock_item.code} 行情获取失败：{exc}")
        for etf_item in config.etfs:
            try:
                etf = fetch_etf_quote(etf_item.code)
                self.ui_queue.put(("etf", (etf, etf_item)))
                self._append_log(self._etf_log_line(etf))
            except Exception as exc:
                self._append_log(f"ETF {etf_item.code} 行情获取失败：{exc}")
        self.ui_queue.put(("status", ("就绪" if not self.running else "监控中",)))

    @staticmethod
    def _stock_log_line(stock: StockQuote) -> str:
        line = f"股票 {stock.code} {stock.name} 最新价 {stock.price:.2f}"
        if stock.quote_time:
            line += f" | {stock.quote_time}"
        return line

    @staticmethod
    def _etf_log_line(etf: EtfQuote) -> str:
        line = (
            f"ETF {etf.code} {etf.name} 市场价 {etf.price:.4f} | 估值 {etf.estimated_nav:.4f} | "
            f"净值 {etf.nav:.4f} | 溢价 {etf.premium_pct:+.2f}%"
        )
        if etf.quote_time:
            line += f" | {etf.quote_time}"
        return line

    def _update_stock_row(self, stock: StockQuote, stock_item: StockItem) -> None:
        if stock.code not in self.stock_tree.get_children(""):
            return
        self.stock_tree.item(
            stock.code,
            values=(
                stock.code,
                fmt_price(stock_item.upper_target),
                fmt_price(stock_item.lower_target),
                stock.name,
                f"{stock.price:.2f}",
                stock.quote_time or "",
            ),
        )

    def _update_etf_row(self, etf: EtfQuote, etf_item: EtfItem) -> None:
        if etf.code not in self.etf_tree.get_children(""):
            return
        self.etf_tree.item(
            etf.code,
            values=(
                etf.code,
                f"{etf_item.premium_threshold:g}",
                etf.name,
                f"{etf.price:.4f}",
                f"{etf.estimated_nav:.4f}",
                f"{etf.nav:.4f}",
                f"{etf.premium_pct:+.2f}",
                etf.quote_time or "",
            ),
        )

    def _monitor_loop(self, config: MonitorConfig) -> None:
        self.state = MonitorState()
        self._append_log(f"监控配置：股票 {len(config.stocks)} 个，ETF {len(config.etfs)} 个；MagicPush={config.push_base_url}")

        while self.running:
            now = dt.datetime.now()
            if not is_trading_time(now):
                day_key = now.strftime("%Y-%m-%d")
                if self.state.last_not_trading_day != day_key:
                    self._append_log("当前不在 A 股交易时段，自动监控等待开盘；如需当前行情请点“手动刷新行情”。")
                    self.state.last_not_trading_day = day_key
                time.sleep(POLL_INTERVAL)
                continue

            self.state.last_not_trading_day = None
            self._refresh_and_alert(config, now)
            time.sleep(POLL_INTERVAL)

        self._append_log("监控线程已退出")

    def _get_kline_cached(self, code: str) -> List[KLine]:
        now_t = time.time()
        cache = self.state.kline_cache.get(code)
        cache_t = self.state.kline_cache_time.get(code, 0)
        if cache is not None and now_t - cache_t < KLINE_CACHE_DURATION:
            return cache
        klines = fetch_kline(code, 120)
        self.state.kline_cache[code] = klines
        self.state.kline_cache_time[code] = now_t
        return klines

    def _refresh_technicals(self, config: MonitorConfig, now: dt.datetime) -> None:
        for stock_item in config.stocks:
            code = stock_item.code
            label = f"{code} {stock_item.last_name}" if stock_item.last_name else code
            macd_signal = False
            rsi_signal = False
            try:
                klines = self._get_kline_cached(code)
                closes = [k.close for k in klines]

                # MACD 顶背离
                dif, _, _ = calc_macd(closes)
                macd_signal = check_macd_top_divergence(klines, dif)
                if macd_signal:
                    prev = self.state.macd_sell_active.get(code, False)
                    if not prev:
                        content = (
                            f"MACD 顶背离卖出信号：{label}\n"
                            f"价格创新高但 DIF 未创新高，建议适当减仓。\n"
                            f"时间：{now.strftime('%Y-%m-%d %H:%M:%S')}"
                        )
                        ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, content)
                        self._append_push_log(f"MACD顶背离 {label}")
                    self.state.macd_sell_active[code] = True
                else:
                    self.state.macd_sell_active[code] = False

                # RSI + BOLL
                rsi = calc_rsi(closes, 14)
                _, _, boll_lower = calc_boll(closes, 20)
                rsi_signal = check_rsi_boll_buy(closes, rsi, boll_lower)
                if rsi_signal:
                    prev = self.state.rsi_buy_active.get(code, False)
                    if not prev:
                        content = (
                            f"RSI+BOLL 买入信号：{label}\n"
                            f"RSI({rsi[-1]:.1f}) < 15 且价格({closes[-1]:.2f}) <= BOLL下轨({boll_lower[-1]:.2f})，建议短线买入。\n"
                            f"时间：{now.strftime('%Y-%m-%d %H:%M:%S')}"
                        )
                        ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, content)
                        self._append_push_log(f"RSI+BOLL买入 {label}")
                    self.state.rsi_buy_active[code] = True
                else:
                    self.state.rsi_buy_active[code] = False

            except Exception as exc:
                self._append_log(f"技术指标 {code} 分析失败：{exc}")

            # 无论是否有信号，每只股票都打印分析结果
            parts = []
            if macd_signal:
                parts.append("MACD顶背离 ✓")
            else:
                parts.append("MACD正常")
            if rsi_signal:
                parts.append("RSI+BOLL买入 ✓")
            else:
                parts.append("RSI+BOLL无信号")
            self._append_log(f"{label} {' | '.join(parts)}")
            # 每个股票间等待，避免 API 限流
            time.sleep(0.5)
        self.ui_queue.put(("status", ("就绪" if not self.running else "监控中",)))

    def _refresh_and_alert(self, config: MonitorConfig, now: dt.datetime) -> None:
        for stock_item in config.stocks:
            if not self.running:
                break
            try:
                stock = fetch_stock_quote(stock_item.code)
                self.ui_queue.put(("stock", (stock, stock_item)))
                self._append_log(self._stock_log_line(stock))

                price = stock.price
                today = now.strftime("%Y-%m-%d")
                alerts_triggered: List[str] = []

                # 检查涨破（每交易日一次）
                if stock_item.upper_target is not None and price >= stock_item.upper_target:
                    last_upper = self.state.stock_upper_date.get(stock.code, "")
                    if last_upper != today:
                        alerts_triggered.append(f"涨破 {stock_item.upper_target:.2f}")
                    self.state.stock_upper_date[stock.code] = today

                # 检查跌破（每交易日一次）
                if stock_item.lower_target is not None and price <= stock_item.lower_target:
                    last_lower = self.state.stock_lower_date.get(stock.code, "")
                    if last_lower != today:
                        alerts_triggered.append(f"跌破 {stock_item.lower_target:.2f}")
                    self.state.stock_lower_date[stock.code] = today

                if alerts_triggered:
                    content = (
                        f"股票触发：{stock.code} {stock.name}\n"
                        f"当前价格：{stock.price:.2f}\n"
                        f"条件：{'，'.join(alerts_triggered)}\n"
                        f"时间：{stock.quote_time or now.strftime('%Y-%m-%d %H:%M:%S')}"
                    )
                    ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, content)
                    cond_str = " ".join(alerts_triggered)
                    self._append_push_log(f"{stock.code} {stock.name} {cond_str}")
            except Exception as exc:
                self._append_log(f"股票 {stock_item.code} 行情获取失败：{exc}")

        for etf_item in config.etfs:
            if not self.running:
                break
            try:
                etf = fetch_etf_quote(etf_item.code)
                self.ui_queue.put(("etf", (etf, etf_item)))
                self._append_log(self._etf_log_line(etf))

                today = now.strftime("%Y-%m-%d")
                premium = etf.premium_pct
                threshold = etf_item.premium_threshold
                etf_label = f"{etf.code} {etf.name}"

                # 高于阈值 → 溢价过高
                if premium > threshold:
                    last_high = self.state.etf_high_date.get(etf.code, "")
                    if last_high != today:
                        content = (
                            f"ETF 溢价过高：{etf_label}\n"
                            f"市场最新价：{etf.price:.4f}\n"
                            f"估算净值：{etf.estimated_nav:.4f}\n"
                            f"单位净值：{etf.nav:.4f}\n"
                            f"溢价：{premium:+.2f}%\n"
                            f"阈值：> {threshold:.2f}%\n"
                            f"时间：{etf.quote_time or today} {now.strftime('%H:%M:%S')}"
                        )
                        ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, content)
                        self._append_push_log(f"ETF溢价过高 {etf_label}")
                    self.state.etf_high_date[etf.code] = today
                # 低于阈值 → 溢价过低（含折价）
                if premium < threshold:
                    last_low = self.state.etf_low_date.get(etf.code, "")
                    if last_low != today:
                        content = (
                            f"ETF 溢价过低：{etf_label}\n"
                            f"市场最新价：{etf.price:.4f}\n"
                            f"估算净值：{etf.estimated_nav:.4f}\n"
                            f"单位净值：{etf.nav:.4f}\n"
                            f"溢价：{premium:+.2f}%\n"
                            f"阈值：< {threshold:.2f}%\n"
                            f"时间：{etf.quote_time or today} {now.strftime('%H:%M:%S')}"
                        )
                        ok, resp = send_magicpush(config.push_base_url, config.push_token, config.push_title, content)
                        self._append_push_log(f"ETF溢价过低 {etf_label}")
                    self.state.etf_low_date[etf.code] = today
            except Exception as exc:
                self._append_log(f"ETF {etf_item.code} 行情获取失败：{exc}")

    def _on_close(self) -> None:
        self.save_ui_config(show_message=False)
        self.running = False
        self.destroy()


def main() -> None:
    app = StockMonitorApp()
    app.mainloop()


if __name__ == "__main__":
    main()
