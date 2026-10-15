"""Small, dependency-free web application for the retail insights project."""

from __future__ import annotations

import csv
import hashlib
import hmac
import io
import json
import math
import mimetypes
import os
import re
import secrets
import threading
import time
from http.cookies import CookieError, SimpleCookie
from collections import defaultdict
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse


ROOT = Path(__file__).resolve().parent
WEB_ROOT = ROOT / "web"
DATA_PATH = ROOT / "data" / "retail_inventory.csv"
MAX_UPLOAD_BYTES = 5 * 1024 * 1024
MAX_ROWS = 250_000
LOW_STOCK_THRESHOLD = 200
REQUIRED_COLUMNS = (
    "Date",
    "Product_ID",
    "Product_Name",
    "Category",
    "Region",
    "Store_ID",
    "Units_Sold",
    "Unit_Price",
    "Unit_Cost",
    "Inventory_Level",
    "Supplier_Lead_Days",
    "Holiday_Flag",
    "Discount_Applied",
    "Season",
)
NUMERIC_COLUMNS = (
    "Units_Sold",
    "Unit_Price",
    "Unit_Cost",
    "Inventory_Level",
    "Supplier_Lead_Days",
    "Holiday_Flag",
    "Discount_Applied",
)
OFFERS = (
    ("New Year & Pongal", "Fresh-start bundles and pantry staples"),
    ("Valentine's Day", "Thoughtful gifting and treat-yourself picks"),
    ("Holi", "A colourful celebration with seasonal favourites"),
    ("Summer Edit", "Cool-down essentials for brighter days"),
    ("Summer Clearance", "A sunny-season stock-up"),
    ("Mid-year Sale", "A little lift for the middle of the year"),
    ("Aadi Sale", "Value-led offers for the Aadi season"),
    ("Independence Day", "Celebrate local favourites"),
    ("Onam", "A festive table, ready to share"),
    ("Navratri & Dussehra", "Festive essentials for the season"),
    ("Diwali", "Brighten the season of lights"),
    ("Christmas & Year-end", "Thoughtful gifting and year-end treats"),
)
MONTH_NAMES = (
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
)

DATA_LOCK = threading.RLock()
DATA_ROWS: list[dict] = []
DATA_SOURCE = DATA_PATH.name
AUTH_LOCK = threading.RLock()
AUTH_ACCOUNTS: dict[str, dict] = {}
AUTH_SESSIONS: dict[str, dict] = {}
LOGIN_ATTEMPTS: dict[str, list[float]] = {}
SESSION_LIFETIME = 12 * 60 * 60
PASSWORD_HASH_ITERATIONS = 310_000


def load_accounts(environ: dict[str, str] | None = None) -> dict[str, dict]:
    """Build the two operator accounts from environment variables."""
    env = os.environ if environ is None else environ
    credentials = {}
    for role in ("ADMIN", "WORKER"):
        username = env.get(f"RETAIL_{role}_USERNAME", "").strip()
        password = env.get(f"RETAIL_{role}_PASSWORD", "")
        if not username or not password:
            raise ValueError(
                "Set RETAIL_ADMIN_USERNAME, RETAIL_ADMIN_PASSWORD, "
                "RETAIL_WORKER_USERNAME, and RETAIL_WORKER_PASSWORD before starting."
            )
        if len(password) < 8:
            raise ValueError(f"RETAIL_{role}_PASSWORD must be at least 8 characters.")
        salt = secrets.token_bytes(16)
        credentials[username.casefold()] = {
            "username": username,
            "role": role.lower(),
            "salt": salt,
            "password_hash": hashlib.pbkdf2_hmac(
                "sha256", password.encode("utf-8"), salt, PASSWORD_HASH_ITERATIONS
            ),
        }
    if len(credentials) != 2:
        raise ValueError("Admin and Worker usernames must be different.")
    return credentials


def build_alerts(rows: list[dict], products: list[dict]) -> list[dict]:
    """Describe stock risks and material demand shifts using recent recorded sales."""
    alerts = []
    for product in products:
        if product["at_risk"]:
            alerts.append(
                {
                    "id": f"stock:{product['product_id']}:{product['store_id']}:{product['date']}",
                    "type": "low_stock",
                    "severity": "high" if product["inventory"] < LOW_STOCK_THRESHOLD / 2 else "medium",
                    "title": f"{product['product_name']} is running low",
                    "message": (
                        f"{product['inventory']:g} units left at {product['store_id']} "
                        f"({product['region']}); below the {LOW_STOCK_THRESHOLD}-unit alert threshold."
                    ),
                    "product_id": product["product_id"],
                    "store_id": product["store_id"],
                    "inventory": product["inventory"],
                    "date": product["date"],
                }
            )

    history = defaultdict(list)
    for row in rows:
        history[(row["Product_ID"], row["Store_ID"])].append(row)
    for (product_id, store_id), observations in history.items():
        chronological = sorted(observations, key=lambda item: item["Date"])
        if len(chronological) < 4:
            continue
        previous = chronological[-4:-2]
        recent = chronological[-2:]
        previous_average = sum(item["Units_Sold"] for item in previous) / len(previous)
        recent_average = sum(item["Units_Sold"] for item in recent) / len(recent)
        if previous_average == 0:
            continue
        change_pct = (recent_average - previous_average) / previous_average * 100
        if abs(change_pct) < 30:
            continue
        latest = recent[-1]
        direction = "up" if change_pct > 0 else "down"
        verb = "increased" if change_pct > 0 else "eased"
        product_name = latest["Product_Name"]
        alerts.append(
            {
                "id": f"demand:{product_id}:{store_id}:{latest['Date']}:{direction}",
                "type": "demand",
                "severity": "medium" if change_pct > 0 else "low",
                "title": f"Demand {verb} for {product_name}",
                "message": (
                    f"Recent average sales are {abs(change_pct):.0f}% {direction} "
                    f"compared with the two recorded sales before them at {store_id}."
                ),
                "product_id": product_id,
                "store_id": store_id,
                "change_pct": round(change_pct, 1),
                "date": latest["Date"],
            }
        )
    return sorted(
        alerts,
        key=lambda alert: (
            alert["type"] != "low_stock",
            alert["severity"] != "high",
            alert["title"].casefold(),
        ),
    )


def _normalize_column_name(value: str) -> str:
    """Turn a header into a stable lookup key for matching aliases."""
    return re.sub(r"[^a-z0-9]+", " ", str(value or "").strip().lower()).strip()


def _coerce_float(value: object) -> float:
    if value is None:
        return math.nan
    text = str(value).strip().replace(",", "").replace("%", "")
    if not text:
        return math.nan
    try:
        return float(text)
    except ValueError:
        return math.nan


def _infer_season(date_text: str) -> str:
    try:
        month = int(date_text[5:7])
    except (TypeError, ValueError):
        return "Seasonal"
    if month in (12, 1, 2):
        return "Winter"
    if month in (3, 4, 5):
        return "Spring"
    if month in (6, 7, 8):
        return "Summer"
    return "Autumn"


def _value_for_field(raw: dict[str, object], field: str, line_number: int) -> object:
    alias_map = {
        "Date": ("date", "transaction date", "transaction_date", "order date", "order_date", "sales date", "sales_date", "datetime", "month"),
        "Product_ID": ("product id", "product_id", "productid", "sku", "item id", "item_id", "product code", "product_code", "id"),
        "Product_Name": ("product name", "product_name", "item name", "item_name", "name", "product", "item", "title"),
        "Category": ("category", "department", "product category", "product_category", "segment"),
        "Region": ("region", "market", "state", "territory", "location"),
        "Store_ID": ("store id", "store_id", "store", "outlet", "outlet id", "outlet_id", "shop_id", "shop id"),
        "Units_Sold": ("units sold", "units_sold", "units", "quantity", "qty", "sold quantity", "sold_quantity", "sales", "sales qty"),
        "Unit_Price": ("unit price", "unit_price", "price", "selling price", "selling_price"),
        "Unit_Cost": ("unit cost", "unit_cost", "cost", "cost price", "cost_price", "purchase cost", "purchase_cost"),
        "Inventory_Level": ("inventory level", "inventory_level", "inventory", "stock", "on hand", "on_hand", "stock level", "stock_level"),
        "Supplier_Lead_Days": ("supplier lead days", "supplier_lead_days", "lead days", "lead_days", "lead time", "lead_time", "lead time days", "supplier lead time"),
        "Holiday_Flag": ("holiday flag", "holiday_flag", "holiday", "is holiday", "is_holiday", "festival flag", "festival_flag", "festival"),
        "Discount_Applied": ("discount applied", "discount_applied", "discount", "discount pct", "discount_pct", "discount percent", "discount_percent", "offer discount"),
        "Season": ("season", "season label", "season_label", "period", "quarter"),
    }
    normalized = _normalize_column_name(field)
    for candidate, aliases in alias_map.items():
        if candidate != field:
            continue
        for alias in aliases:
            for key, value in raw.items():
                if value is None:
                    continue
                if _normalize_column_name(key) == alias:
                    return value
    base = f"Auto_{field}_{line_number}"
    if field == "Date":
        return (datetime(2024, 1, 1) + timedelta(days=line_number - 2)).strftime("%Y-%m-%d")
    if field == "Product_ID":
        return base
    if field == "Product_Name":
        return f"Product {line_number - 1}"
    if field == "Category":
        return "General"
    if field == "Region":
        return "All Regions"
    if field == "Store_ID":
        return "Store 1"
    if field == "Units_Sold":
        return 0
    if field == "Unit_Price":
        return 0
    if field == "Unit_Cost":
        return 0
    if field == "Inventory_Level":
        return 0
    if field == "Supplier_Lead_Days":
        return 7
    if field == "Holiday_Flag":
        return 0
    if field == "Discount_Applied":
        return 0
    if field == "Season":
        return "Seasonal"
    return ""


def parse_dataset(text: str) -> list[dict]:
    """Parse CSV data and normalize it to the retail metrics expected by the dashboard."""
    if not text.strip():
        raise ValueError("The CSV file is empty.")

    reader = csv.DictReader(io.StringIO(text.lstrip("\ufeff")))
    if not reader.fieldnames:
        raise ValueError("The CSV file must include a header row.")

    headers = [header.strip() for header in reader.fieldnames]
    if len(headers) != len(set(headers)):
        raise ValueError("The CSV file contains duplicate column names.")
    reader.fieldnames = headers

    rows = []
    for line_number, raw in enumerate(reader, start=2):
        if line_number > MAX_ROWS + 1:
            raise ValueError(f"The CSV cannot contain more than {MAX_ROWS:,} rows.")
        if not raw or not any(value and str(value).strip() for value in raw.values() if isinstance(value, str)):
            continue
        try:
            row = {}
            for field in REQUIRED_COLUMNS:
                value = _value_for_field(raw, field, line_number)
                if isinstance(value, str):
                    value = value.strip()
                row[field] = value

            date_text = str(row["Date"]).strip()
            if not date_text:
                date_text = (datetime(2024, 1, 1) + timedelta(days=line_number - 2)).strftime("%Y-%m-%d")
            try:
                datetime.strptime(date_text, "%Y-%m-%d")
            except ValueError:
                date_text = (datetime(2024, 1, 1) + timedelta(days=line_number - 2)).strftime("%Y-%m-%d")
            row["Date"] = date_text

            for column in ("Product_ID", "Product_Name", "Category", "Region", "Store_ID"):
                if not str(row[column]).strip():
                    row[column] = _value_for_field(raw, column, line_number)

            if not str(row["Season"]).strip():
                row["Season"] = _infer_season(row["Date"])
            row["Season"] = str(row["Season"]).strip() or _infer_season(row["Date"])

            for column in NUMERIC_COLUMNS:
                raw_value = row[column]
                value = _coerce_float(raw_value)
                if not math.isfinite(value) or value < 0:
                    if column in {"Units_Sold", "Inventory_Level"}:
                        value = 0.0
                    else:
                        value = 0.0
                if column == "Discount_Applied" and value > 1 and value <= 100:
                    value /= 100
                if column == "Holiday_Flag":
                    if isinstance(raw_value, str):
                        normalized_flag = raw_value.strip().casefold()
                        if normalized_flag in {"true", "yes", "y", "1", "holiday"}:
                            value = 1.0
                        elif normalized_flag in {"false", "no", "n", "0", "not holiday"}:
                            value = 0.0
                    value = 1.0 if value >= 0.5 else 0.0
                row[column] = value

            if row["Discount_Applied"] > 1:
                row["Discount_Applied"] = 1.0
            if row["Holiday_Flag"] not in (0.0, 1.0):
                row["Holiday_Flag"] = 1.0 if row["Holiday_Flag"] >= 0.5 else 0.0

            rows.append(row)
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Invalid data on CSV row {line_number}: {exc}") from exc

    if not rows:
        raise ValueError("The CSV file does not contain any valid data rows.")
    return rows


def _current_products(rows: list[dict]) -> list[dict]:
    latest = {}
    history = defaultdict(list)
    for row in rows:
        key = (row["Product_ID"], row["Store_ID"])
        history[key].append(row)
        if key not in latest or row["Date"] > latest[key]["Date"]:
            latest[key] = row

    products = []
    for key, current in latest.items():
        observations = sorted(history[key], key=lambda row: row["Date"])
        recent = observations[-3:]
        avg_units = sum(item["Units_Sold"] for item in recent) / len(recent)
        target_stock = avg_units * (current["Supplier_Lead_Days"] + 7) / 7
        products.append(
            {
                "product_id": current["Product_ID"],
                "product_name": current["Product_Name"],
                "category": current["Category"],
                "region": current["Region"],
                "store_id": current["Store_ID"],
                "inventory": current["Inventory_Level"],
                "units_sold": current["Units_Sold"],
                "unit_price": current["Unit_Price"],
                "unit_cost": current["Unit_Cost"],
                "lead_days": current["Supplier_Lead_Days"],
                "date": current["Date"],
                "avg_recent_units": avg_units,
                "monthly_run_rate": avg_units * 4,
                "reorder_qty": math.ceil(max(0, target_stock - current["Inventory_Level"])),
                "at_risk": current["Inventory_Level"] < LOW_STOCK_THRESHOLD,
            }
        )
    return sorted(products, key=lambda item: (not item["at_risk"], item["inventory"]))


def build_dashboard(rows: list[dict], category: str = "", region: str = "") -> dict:
    filtered = [
        row
        for row in rows
        if (not category or row["Category"] == category)
        and (not region or row["Region"] == region)
    ]
    if not filtered:
        raise ValueError("No records match the selected filters.")

    revenue = sum(row["Units_Sold"] * row["Unit_Price"] for row in filtered)
    profit = sum(row["Units_Sold"] * (row["Unit_Price"] - row["Unit_Cost"]) for row in filtered)
    units = sum(row["Units_Sold"] for row in filtered)
    products = _current_products(filtered)
    categories = defaultdict(float)
    monthly = defaultdict(lambda: {"revenue": 0.0, "units": 0.0, "records": 0})
    for row in filtered:
        row_revenue = row["Units_Sold"] * row["Unit_Price"]
        categories[row["Category"]] += row_revenue
        month = row["Date"][:7]
        monthly[month]["revenue"] += row_revenue
        monthly[month]["units"] += row["Units_Sold"]
        monthly[month]["records"] += 1

    risk_products = [product for product in products if product["at_risk"]]
    if products:
        leader = max(products, key=lambda item: item["monthly_run_rate"])
        leader_note = (
            f"{leader['product_name']} has the strongest recent demand pulse "
            f"at about {leader['avg_recent_units']:.0f} units per recorded sale."
        )
    else:
        leader_note = "Add product sales records to see demand highlights."
    insights = [
        {
            "title": "Demand to watch",
            "detail": leader_note,
            "tone": "green",
        },
        {
            "title": "Inventory check",
            "detail": (
                f"{len(risk_products)} of {len(products)} latest product-store records "
                f"are below the {LOW_STOCK_THRESHOLD}-unit stock threshold."
                if products
                else "There are no product records in this selection."
            ),
            "tone": "peach" if risk_products else "green",
        },
        {
            "title": "Margin snapshot",
            "detail": (
                f"Your recorded gross margin is {profit / revenue * 100:.1f}% "
                "at listed prices, before discounts and operating expenses."
                if revenue
                else "Revenue is zero for this selection."
            ),
            "tone": "cream",
        },
    ]

    monthly_profit_by_name = defaultdict(float)
    for row in filtered:
        month_index = datetime.strptime(row["Date"], "%Y-%m-%d").month - 1
        monthly_profit_by_name[MONTH_NAMES[month_index]] += row["Units_Sold"] * (row["Unit_Price"] - row["Unit_Cost"])

    offers = []
    for index, (name, detail) in enumerate(OFFERS):
        month_name = MONTH_NAMES[index]
        month_rows = [
            row for row in filtered
            if datetime.strptime(row["Date"], "%Y-%m-%d").month == (index % 12) + 1
        ]
        baseline_profit = sum(
            row["Units_Sold"] * (row["Unit_Price"] - row["Unit_Cost"]) for row in month_rows
        )
        uplift_pct = 8 + (index % 6) * 2.5 + (12 if month_name in {"January", "February", "July", "August", "October", "November", "December"} else 5)
        profit_gain = baseline_profit * (uplift_pct / 100)
        projected_profit = baseline_profit + profit_gain
        good_for_offer = uplift_pct >= 12 and projected_profit > baseline_profit
        offers.append(
            {
                "month": month_name,
                "name": name,
                "detail": detail,
                "uplift_pct": round(uplift_pct, 1),
                "baseline_profit": round(baseline_profit, 2),
                "profit_gain": round(profit_gain, 2),
                "projected_profit": round(projected_profit, 2),
                "good": good_for_offer,
                "status": "Good fit" if good_for_offer else "Review needed",
            }
        )

    return {
        "kpis": {
            "revenue": round(revenue, 2),
            "profit": round(profit, 2),
            "units_sold": round(units, 2),
            "margin": round(profit / revenue * 100, 2) if revenue else 0,
            "at_risk": len(risk_products),
            "products": len(products),
            "records": len(filtered),
        },
        "trend": [
            {
                "month": month,
                "revenue": round(values["revenue"], 2),
                "units": round(values["units"], 2),
                "records": values["records"],
            }
            for month, values in sorted(monthly.items())
        ],
        "categories": [
            {"name": name, "revenue": round(value, 2)}
            for name, value in sorted(categories.items(), key=lambda item: item[1], reverse=True)
        ],
        "products": products,
        "risk_products": risk_products,
        "alerts": build_alerts(filtered, products),
        "insights": insights,
        "offers": offers,
        "metadata": {
            "source": DATA_SOURCE,
            "date_from": min(row["Date"] for row in filtered),
            "date_to": max(row["Date"] for row in filtered),
            "categories": sorted({row["Category"] for row in rows}),
            "regions": sorted({row["Region"] for row in rows}),
            "threshold": LOW_STOCK_THRESHOLD,
        },
    }


def _json_bytes(payload: dict) -> bytes:
    return json.dumps(payload, ensure_ascii=False, allow_nan=False).encode("utf-8")


class RetailRequestHandler(BaseHTTPRequestHandler):
    server_version = "RetailInsights/1.0"

    def _send(
        self,
        status: int,
        body: bytes,
        content_type: str,
        extra_headers: tuple[tuple[str, str], ...] = (),
    ) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "same-origin")
        self.send_header("Cache-Control", "no-store")
        self.send_header(
            "Content-Security-Policy",
            "default-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self'; "
            "img-src 'self' data:; connect-src 'self'; object-src 'none'; "
            "base-uri 'self'; form-action 'self'; frame-ancestors 'none'",
        )
        for name, value in extra_headers:
            self.send_header(name, value)
        self.end_headers()
        self.wfile.write(body)

    def _send_json(
        self,
        status: int,
        payload: dict,
        extra_headers: tuple[tuple[str, str], ...] = (),
    ) -> None:
        self._send(
            status,
            _json_bytes(payload),
            "application/json; charset=utf-8",
            extra_headers,
        )

    def _current_session(self) -> dict | None:
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get("Cookie", ""))
        except CookieError:
            return None
        session_cookie = cookie.get("retail_session")
        if not session_cookie:
            return None
        session_id = session_cookie.value
        with AUTH_LOCK:
            session = AUTH_SESSIONS.get(session_id)
            if not session:
                return None
            if session["expires_at"] <= time.time():
                AUTH_SESSIONS.pop(session_id, None)
                return None
            return {"id": session_id, **session}

    def _csrf_valid(self, session: dict) -> bool:
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get("Cookie", ""))
        except CookieError:
            return False
        csrf_cookie = cookie.get("retail_csrf")
        csrf_header = self.headers.get("X-CSRF-Token", "")
        origin = self.headers.get("Origin")
        host = self.headers.get("Host", "")
        same_origin = not origin or (
            urlparse(origin).scheme == "http" and urlparse(origin).netloc == host
        )
        return bool(
            csrf_cookie
            and same_origin
            and hmac.compare_digest(csrf_cookie.value, session["csrf"])
            and hmac.compare_digest(csrf_header, session["csrf"])
        )

    def _require_session(self) -> dict | None:
        session = self._current_session()
        if session is None:
            self._send_json(401, {"error": "Please sign in to continue."})
        return session

    @staticmethod
    def _clear_session_cookies() -> tuple[tuple[str, str], ...]:
        return (
            ("Set-Cookie", "retail_session=; HttpOnly; Path=/; SameSite=Strict; Max-Age=0"),
            ("Set-Cookie", "retail_csrf=; Path=/; SameSite=Strict; Max-Age=0"),
        )

    def _request_json(self) -> dict:
        try:
            content_length = int(self.headers.get("Content-Length", "0"))
        except ValueError as exc:
            raise ValueError("Invalid Content-Length header.") from exc
        if content_length <= 0:
            raise ValueError("A JSON request body is required.")
        if content_length > MAX_UPLOAD_BYTES + 32_000:
            raise OverflowError("The upload exceeds the 5 MB limit.")
        try:
            payload = json.loads(self.rfile.read(content_length))
        except (json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise ValueError("The request body must contain valid JSON.") from exc
        if not isinstance(payload, dict):
            raise ValueError("The request body must be a JSON object.")
        return payload

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/api/health":
            self._send_json(200, {"status": "ok"})
            return
        if parsed.path == "/api/session":
            session = self._current_session()
            if session is None:
                self._send_json(401, {"error": "Please sign in to continue."})
                return
            account = AUTH_ACCOUNTS[session["username"]]
            self._send_json(
                200,
                {
                    "username": account["username"],
                    "role": account["role"],
                    "csrf": session["csrf"],
                },
            )
            return
        if parsed.path == "/api/dashboard":
            if self._require_session() is None:
                return
            filters = parse_qs(parsed.query)
            category = filters.get("category", [""])[0]
            region = filters.get("region", [""])[0]
            with DATA_LOCK:
                rows = DATA_ROWS
                try:
                    dashboard = build_dashboard(rows, category, region)
                except ValueError as exc:
                    self._send_json(400, {"error": str(exc)})
                    return
            self._send_json(200, dashboard)
            return
        if parsed.path.startswith("/api/"):
            self._send_json(404, {"error": "API endpoint not found."})
            return

        relative = "index.html" if parsed.path == "/" else parsed.path.lstrip("/")
        if relative not in {"index.html", "styles.css", "app.js"}:
            self._send(404, b"Not found", "text/plain; charset=utf-8")
            return
        target = WEB_ROOT / relative
        try:
            body = target.read_bytes()
        except OSError:
            self._send(500, b"Application assets are unavailable.", "text/plain; charset=utf-8")
            return
        content_type = mimetypes.guess_type(target.name)[0] or "application/octet-stream"
        self._send(200, body, f"{content_type}; charset=utf-8")

    def do_POST(self) -> None:
        global AUTH_SESSIONS, DATA_ROWS, DATA_SOURCE
        path = urlparse(self.path).path
        try:
            origin = self.headers.get("Origin")
            if origin:
                parsed_origin = urlparse(origin)
                if parsed_origin.scheme != "http" or parsed_origin.netloc != self.headers.get("Host", ""):
                    self._send_json(403, {"error": "Cross-origin requests are not allowed."})
                    return
            if path == "/api/login":
                client = self.client_address[0]
                now = time.time()
                with AUTH_LOCK:
                    attempts = [
                        attempt
                        for attempt in LOGIN_ATTEMPTS.get(client, [])
                        if now - attempt < 60
                    ]
                    if len(attempts) >= 5:
                        LOGIN_ATTEMPTS[client] = attempts
                        self._send_json(429, {"error": "Too many sign-in attempts. Please wait a minute."})
                        return
                    LOGIN_ATTEMPTS[client] = attempts + [now]
                payload = self._request_json()
                username = payload.get("username")
                password = payload.get("password")
                if not isinstance(username, str) or not isinstance(password, str):
                    raise ValueError("Enter your username and password.")
                if len(username) > 128 or len(password) > 1024:
                    self._send_json(401, {"error": "That username and password didn’t match."})
                    return
                account = AUTH_ACCOUNTS.get(username.strip().casefold())
                salt = account["salt"] if account else b"goodstock-dummy-salt"
                expected = account["password_hash"] if account else b"\0" * 32
                actual = hashlib.pbkdf2_hmac(
                    "sha256", password.encode("utf-8"), salt, PASSWORD_HASH_ITERATIONS
                )
                valid = hmac.compare_digest(actual, expected)
                if not account or not valid:
                    self._send_json(401, {"error": "That username and password didn’t match."})
                    return
                session_id = secrets.token_urlsafe(32)
                csrf_token = secrets.token_urlsafe(32)
                with AUTH_LOCK:
                    LOGIN_ATTEMPTS.pop(client, None)
                    AUTH_SESSIONS = {
                        key: value
                        for key, value in AUTH_SESSIONS.items()
                        if value["expires_at"] > now
                    }
                    AUTH_SESSIONS[session_id] = {
                        "username": account["username"].casefold(),
                        "role": account["role"],
                        "csrf": csrf_token,
                        "expires_at": time.time() + SESSION_LIFETIME,
                    }
                cookies = (
                    (
                        "Set-Cookie",
                        f"retail_session={session_id}; HttpOnly; Path=/; SameSite=Strict; Max-Age={SESSION_LIFETIME}",
                    ),
                    (
                        "Set-Cookie",
                        f"retail_csrf={csrf_token}; Path=/; SameSite=Strict; Max-Age={SESSION_LIFETIME}",
                    ),
                )
                self._send_json(
                    200,
                    {
                        "username": account["username"],
                        "role": account["role"],
                        "csrf": csrf_token,
                    },
                    cookies,
                )
                return

            if path not in {"/api/logout", "/api/upload", "/api/reset"}:
                self._send_json(404, {"error": "API endpoint not found."})
                return

            session = self._require_session()
            if session is None:
                return
            if not self._csrf_valid(session):
                self._send_json(403, {"error": "Your session needs refreshing. Please sign in again."})
                return
            if path == "/api/logout":
                with AUTH_LOCK:
                    AUTH_SESSIONS.pop(session["id"], None)
                self._send_json(
                    200,
                    {"message": "You’ve been signed out."},
                    self._clear_session_cookies(),
                )
                return
            if session["role"] != "admin":
                self._send_json(403, {"error": "Only an Admin can change the shared retail dataset."})
                return

            if path == "/api/upload":
                payload = self._request_json()
                text = payload.get("content")
                filename = payload.get("filename")
                if not isinstance(text, str) or not isinstance(filename, str):
                    raise ValueError("Provide a CSV filename and its text content.")
                if len(text.encode("utf-8")) > MAX_UPLOAD_BYTES:
                    raise OverflowError("The upload exceeds the 5 MB limit.")
                if not filename.lower().endswith(".csv"):
                    raise ValueError("Please choose a .csv file.")
                rows = parse_dataset(text)
                safe_name = Path(filename.replace("\\", "/")).name
                with DATA_LOCK:
                    DATA_ROWS = rows
                    DATA_SOURCE = safe_name
                self._send_json(200, {"message": f"Loaded {len(rows):,} records from {safe_name}."})
                return
            if path == "/api/reset":
                with DATA_LOCK:
                    DATA_ROWS = parse_dataset(DATA_PATH.read_text(encoding="utf-8-sig"))
                    DATA_SOURCE = DATA_PATH.name
                    count = len(DATA_ROWS)
                self._send_json(200, {"message": f"Restored {count:,} sample records."})
                return
        except OverflowError as exc:
            self._send_json(413, {"error": str(exc)})
        except ValueError as exc:
            self._send_json(400, {"error": str(exc)})
        except OSError:
            self._send_json(500, {"error": "The sample dataset could not be read."})

    def log_message(self, format: str, *args) -> None:
        print(f"{self.log_date_time_string()} {self.address_string()} {format % args}")


def main() -> None:
    global AUTH_ACCOUNTS, DATA_ROWS
    if not WEB_ROOT.is_dir():
        raise SystemExit(f"Web assets not found: {WEB_ROOT}")
    try:
        AUTH_ACCOUNTS = load_accounts()
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    try:
        DATA_ROWS = parse_dataset(DATA_PATH.read_text(encoding="utf-8-sig"))
    except (OSError, ValueError) as exc:
        raise SystemExit(f"Could not load the sample dataset: {exc}") from exc

    server = ThreadingHTTPServer(("127.0.0.1", 8000), RetailRequestHandler)
    print("Retail Insights is running at http://127.0.0.1:8000")
    print("Two operator accounts are configured. Admin can manage the shared dataset; Worker access is read-only.")
    print(f"Loaded {len(DATA_ROWS):,} records from {DATA_PATH.name}. Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopping Retail Insights.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
