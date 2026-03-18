from flask import Flask, request, jsonify, Response
import sqlite3
from datetime import datetime, timedelta, timezone
import io
import json
import math
import time
import threading
from statistics import median

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

try:
    import board
    import busio
    import adafruit_ads1x15.ads1115 as ADS
    from adafruit_ads1x15.analog_in import AnalogIn
except Exception as exc:
    board = None
    busio = None
    ADS = None
    AnalogIn = None
    ADS_IMPORT_ERROR = str(exc)
else:
    ADS_IMPORT_ERROR = None

try:
    import serial
except Exception as exc:
    serial = None
    ATLAS_UART_IMPORT_ERROR = str(exc)
else:
    ATLAS_UART_IMPORT_ERROR = None

try:
    import adafruit_sgp30
except Exception as exc:
    adafruit_sgp30 = None
    VOC_IMPORT_ERROR = str(exc)
else:
    VOC_IMPORT_ERROR = None

DB_PATH = "weather.db"
app = Flask(__name__)

DEFAULT_HOURS = 24
ALLOWED_WINDOWS = [1, 24, 168]
ONLINE_AFTER_MINUTES = 5
STALE_AFTER_MINUTES = 30

STATION_RULES = {
    "default": {
        "label": "General zone",
        "danger_low": 20,
        "warn_low": 35,
        "target_low": 40,
        "target_high": 85,
        "warn_high": 95,
    },
    "soil_sat_1": {
        "label": "Bog zone",
        "danger_low": 55,
        "warn_low": 70,
        "target_low": 75,
        "target_high": 95,
        "warn_high": 99,
    },
}

PROBES = [
    {"key": "soil_moisture_1_pct", "raw_key": "soil_raw_1", "default_name": "Probe 1"},
    {"key": "soil_moisture_2_pct", "raw_key": "soil_raw_2", "default_name": "Probe 2"},
]
PROBE_INDEX = {p["key"]: p for p in PROBES}

BENCH_POLL_SECONDS = 5

PH_ENABLED = True
PH_NAME = "Bench pH Probe"
PH_DESCRIPTION = "Atlas Surveyor through ADS1115 A0"
PH_CHANNEL_INDEX = 0
PH_ADC_GAIN = 1
PH_SAMPLES = 9
PH_SAMPLE_DELAY = 0.03
PH_LOG_EVERY_SECONDS = 15
PH_DEFAULT_HOURS = 24
PH_RECENT_LIMIT = 25
PH_CHANGE_EPSILON = 0.02
PH_VOLTS_MIN = 0.265
PH_VOLTS_MAX = 3.000
PH_SLOPE = -5.6548
PH_INTERCEPT = 15.509
PH_CAL_SCALE = 1.0
PH_CAL_OFFSET = 0.0

TEMP_ENABLED = True
TEMP_NAME = "Bench Temperature Probe"
TEMP_DESCRIPTION = "Atlas EZO RTD on UART"
TEMP_UART_PORT = "/dev/ttyAMA0"
TEMP_UART_BAUD = 9600
TEMP_UART_TIMEOUT = 1.5
TEMP_READ_DELAY = 1.0
TEMP_LOG_EVERY_SECONDS = 15
TEMP_DEFAULT_HOURS = 24
TEMP_RECENT_LIMIT = 25
TEMP_CHANGE_EPSILON = 0.05

TDS_ENABLED = True
TDS_NAME = "Bench TDS Probe"
TDS_DESCRIPTION = "Inland TDS meter through ADS1115 A1"
TDS_CHANNEL_INDEX = 1
TDS_SAMPLES = 15
TDS_SAMPLE_DELAY = 0.02
TDS_LOG_EVERY_SECONDS = 15
TDS_DEFAULT_HOURS = 24
TDS_RECENT_LIMIT = 25
TDS_CHANGE_EPSILON = 5.0
TDS_BASE_TEMP_C = 25.0
TDS_MAX_PPM = 1000.0

VOC_ENABLED = True
VOC_NAME = "Bench VOC / eCO2"
VOC_DESCRIPTION = "Adafruit SGP30 on I²C"
VOC_LOG_EVERY_SECONDS = 15
VOC_DEFAULT_HOURS = 24
VOC_RECENT_LIMIT = 25
VOC_CHANGE_ECO2_EPSILON = 15.0
VOC_CHANGE_TVOC_EPSILON = 5.0

SERIES_CONFIG = {
    "ph": {
        "table": "ph_readings",
        "value_col": "ph_value",
        "extra_cols": ["ph_voltage"],
    },
    "temp": {
        "table": "temp_readings",
        "value_col": "temp_c",
        "extra_cols": [],
    },
    "tds": {
        "table": "tds_readings",
        "value_col": "tds_ppm",
        "extra_cols": ["tds_voltage", "comp_temp_c"],
    },
    "voc_eco2": {
        "table": "voc_readings",
        "value_col": "eco2_ppm",
        "extra_cols": ["tvoc_ppb"],
    },
    "voc_tvoc": {
        "table": "voc_readings",
        "value_col": "tvoc_ppb",
        "extra_cols": ["eco2_ppm"],
    },
}

_ads_i2c = None
_ads = None
_ph_chan = None
_tds_chan = None
_ads_error = ADS_IMPORT_ERROR
_ph_last_logged = None
_tds_last_logged = None

_temp_ser = None
_temp_error = ATLAS_UART_IMPORT_ERROR
_temp_last_logged = None

_voc = None
_voc_error = VOC_IMPORT_ERROR
_voc_last_logged = None

_bench_lock = threading.Lock()
_bench_thread = None
_bench_stop = threading.Event()

_ph_last_live = {
    "ok": False,
    "ph": None,
    "voltage": None,
    "samples": 0,
    "error": "Starting",
    "state": {"cls": "nodata", "text": "Starting…"},
    "updated_at": None,
    "collecting_enabled": True,
}

_temp_last_live = {
    "ok": False,
    "temp_c": None,
    "temp_f": None,
    "temp_k": None,
    "samples": 0,
    "error": "Starting",
    "state": {"cls": "nodata", "text": "Starting…"},
    "updated_at": None,
}

_tds_last_live = {
    "ok": False,
    "tds_ppm": None,
    "voltage": None,
    "comp_temp_c": TDS_BASE_TEMP_C,
    "samples": 0,
    "error": "Starting",
    "state": {"cls": "nodata", "text": "Starting…"},
    "updated_at": None,
}

_voc_last_live = {
    "ok": False,
    "eco2_ppm": None,
    "tvoc_ppb": None,
    "samples": 0,
    "error": "Starting",
    "state": {"cls": "nodata", "text": "Starting…"},
    "updated_at": None,
    "baseline_ready": False,
}


def db():
    conn = sqlite3.connect(DB_PATH, timeout=5)
    conn.row_factory = sqlite3.Row
    return conn


def utc_now():
    return datetime.now(timezone.utc)


def utc_now_iso():
    return utc_now().replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_iso(ts):
    return datetime.fromisoformat(str(ts).replace("Z", "+00:00"))


def safe_num(v, default=0.0):
    try:
        if v is None or v == "":
            return float(default)
        return float(v)
    except Exception:
        return float(default)


def temp_c_to_f(value):
    if value is None:
        return None
    return (float(value) * 9.0 / 5.0) + 32.0


def temp_c_to_k(value):
    if value is None:
        return None
    return float(value) + 273.15


def get_base_rules(station_id):
    return STATION_RULES.get(station_id, STATION_RULES["default"]).copy()


def clamp_hours(v):
    v = int(v or DEFAULT_HOURS)
    return v if v in ALLOWED_WINDOWS else DEFAULT_HOURS


def clamp_percent(v, fallback):
    try:
        num = float(v)
    except Exception:
        return float(fallback)
    return max(0.0, min(100.0, num))


def clamp_bucket_s(bucket_s, hours):
    allowed = [15, 30, 60, 300, 900, 1800, 3600]
    try:
        bucket_s = int(bucket_s)
    except Exception:
        bucket_s = 60 if hours <= 24 else 300
    return bucket_s if bucket_s in allowed else (60 if hours <= 24 else 300)


def age_text(ts):
    delta = utc_now() - parse_iso(ts)
    seconds = max(0, int(delta.total_seconds()))
    if seconds < 60:
        return f"{seconds}s ago"
    minutes = seconds // 60
    if minutes < 60:
        return f"{minutes}m ago"
    hours = minutes // 60
    if hours < 48:
        return f"{hours}h ago"
    days = hours // 24
    return f"{days}d ago"


def connectivity_meta(ts):
    minutes = (utc_now() - parse_iso(ts)).total_seconds() / 60.0
    if minutes <= ONLINE_AFTER_MINUTES:
        return {"state": "online", "label": "Online"}
    if minutes <= STALE_AFTER_MINUTES:
        return {"state": "stale", "label": "Stale"}
    return {"state": "offline", "label": "Offline"}


def current_value_from_row(row, probe_key):
    probe = PROBE_INDEX[probe_key]
    raw = safe_num(row[probe["raw_key"]], 65535)
    val = safe_num(row[probe_key], 0)
    if raw >= 65535 or val < 0 or val > 100:
        return None
    return val


def station_value_from_row(row):
    vals = []
    for probe in PROBES:
        val = current_value_from_row(row, probe["key"])
        if val is not None:
            vals.append(val)
    if vals:
        return sum(vals) / len(vals)
    return None


def value_state(value, rules):
    if value is None:
        return {"cls": "nodata", "text": "No live data"}
    if value < rules["danger_low"]:
        return {"cls": "bad", "text": "Too dry"}
    if value < rules["warn_low"]:
        return {"cls": "warn", "text": "Dry side"}
    if value <= rules["target_high"]:
        return {"cls": "ok", "text": "On target"}
    if value <= rules["warn_high"]:
        return {"cls": "warn", "text": "Very wet"}
    return {"cls": "bad", "text": "Extreme wet"}


def probe_value_sql(probe_key):
    if probe_key not in PROBE_INDEX:
        raise ValueError("unknown probe")
    raw_key = PROBE_INDEX[probe_key]["raw_key"]
    return f"CASE WHEN {raw_key} >= 65535 OR {probe_key} < 0 OR {probe_key} > 100 THEN NULL ELSE {probe_key} END"


def ensure_station_defaults(conn, station_id):
    base = get_base_rules(station_id)
    conn.execute(
        """
        INSERT INTO station_config (station_id, display_name, description, default_hours, is_collapsed)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(station_id) DO NOTHING
        """,
        (station_id, station_id, base["label"], DEFAULT_HOURS, 0),
    )

    for probe in PROBES:
        conn.execute(
            """
            INSERT INTO probe_config (
                station_id, probe_key, display_name, location_name,
                danger_low, warn_low, target_low, target_high, warn_high, enabled
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1)
            ON CONFLICT(station_id, probe_key) DO NOTHING
            """,
            (
                station_id,
                probe["key"],
                probe["default_name"],
                "",
                base["danger_low"],
                base["warn_low"],
                base["target_low"],
                base["target_high"],
                base["warn_high"],
            ),
        )


def get_station_config(conn, station_id):
    ensure_station_defaults(conn, station_id)
    row = conn.execute(
        """
        SELECT station_id, display_name, description, default_hours, is_collapsed
        FROM station_config
        WHERE station_id = ?
        """,
        (station_id,),
    ).fetchone()
    return dict(row)


def get_probe_configs(conn, station_id):
    ensure_station_defaults(conn, station_id)
    rows = conn.execute(
        """
        SELECT station_id, probe_key, display_name, location_name,
               danger_low, warn_low, target_low, target_high, warn_high, enabled
        FROM probe_config
        WHERE station_id = ?
        ORDER BY probe_key
        """,
        (station_id,),
    ).fetchall()
    return {row["probe_key"]: dict(row) for row in rows}


def bench_setting_get(conn, key, default=None):
    row = conn.execute("SELECT value FROM bench_config WHERE key = ?", (key,)).fetchone()
    if row is None:
        return default
    return row["value"]


def bench_setting_get_bool(conn, key, default=False):
    value = bench_setting_get(conn, key, "1" if default else "0")
    return str(value).strip().lower() in ("1", "true", "yes", "on")


def bench_setting_set(conn, key, value):
    conn.execute(
        """
        INSERT INTO bench_config (key, value)
        VALUES (?, ?)
        ON CONFLICT(key) DO UPDATE SET value = excluded.value
        """,
        (key, str(value)),
    )


def get_ph_collect_enabled():
    conn = db()
    try:
        return bench_setting_get_bool(conn, "ph_collect_enabled", True)
    finally:
        conn.close()


def get_ph_calibration():
    conn = db()
    try:
        scale = safe_num(bench_setting_get(conn, "ph_cal_scale", PH_CAL_SCALE), PH_CAL_SCALE)
        offset = safe_num(bench_setting_get(conn, "ph_cal_offset", PH_CAL_OFFSET), PH_CAL_OFFSET)
        mode = bench_setting_get(conn, "ph_cal_mode", "factory")
        last_ts = bench_setting_get(conn, "ph_cal_last_ts", "")
        last_target = bench_setting_get(conn, "ph_cal_last_target", "")
        return {
            "scale": scale,
            "offset": offset,
            "mode": mode,
            "last_ts": last_ts,
            "last_target": None if last_target in (None, "") else safe_num(last_target, math.nan),
        }
    finally:
        conn.close()


def surveyor_voltage_to_ph(voltage):
    cal = get_ph_calibration()
    raw_ph = (PH_SLOPE * float(voltage)) + PH_INTERCEPT
    return (raw_ph * cal["scale"]) + cal["offset"]


def ph_state_from_reading(voltage, ph_value):
    if voltage is None or ph_value is None:
        return {"cls": "nodata", "text": "No valid reading"}
    if voltage < (PH_VOLTS_MIN - 0.10) or voltage > (PH_VOLTS_MAX + 0.10):
        return {"cls": "warn", "text": "Check probe / wiring"}
    if ph_value < 4.5:
        return {"cls": "warn", "text": "Acidic range"}
    if ph_value > 9.0:
        return {"cls": "warn", "text": "Basic range"}
    return {"cls": "ok", "text": "Live"}


def temp_state_from_reading(temp_c):
    if temp_c is None:
        return {"cls": "nodata", "text": "No valid reading"}
    return {"cls": "ok", "text": "Live"}


def tds_state_from_reading(voltage, tds_ppm):
    if voltage is None or tds_ppm is None:
        return {"cls": "nodata", "text": "No valid reading"}
    if voltage < 0.01:
        return {"cls": "warn", "text": "Probe dry / out of water"}
    if tds_ppm > TDS_MAX_PPM:
        return {"cls": "warn", "text": "Above nominal range"}
    return {"cls": "ok", "text": "Live"}


def voc_state_from_reading(eco2_ppm, tvoc_ppb):
    if eco2_ppm is None or tvoc_ppb is None:
        return {"cls": "nodata", "text": "No valid reading"}
    if eco2_ppm <= 420 and tvoc_ppb == 0:
        return {"cls": "warn", "text": "Warming up"}
    return {"cls": "ok", "text": "Live"}


def build_ads_channel(ads, channel_index):
    names = {0: "P0", 1: "P1", 2: "P2", 3: "P3"}
    channel_name = names.get(channel_index)
    if channel_name and hasattr(ADS, channel_name):
        try:
            return AnalogIn(ads, getattr(ADS, channel_name))
        except Exception:
            pass
    return AnalogIn(ads, channel_index)


def reset_ads_hardware(reason=None):
    global _ads_i2c, _ads, _ph_chan, _tds_chan, _ads_error
    try:
        if _ads_i2c is not None:
            try:
                _ads_i2c.deinit()
            except Exception:
                pass
    finally:
        _ads_i2c = None
        _ads = None
        _ph_chan = None
        _tds_chan = None
        if reason:
            _ads_error = str(reason)


def reset_temp_hardware(reason=None):
    global _temp_ser, _temp_error
    try:
        if _temp_ser is not None:
            try:
                _temp_ser.close()
            except Exception:
                pass
    finally:
        _temp_ser = None
        if reason:
            _temp_error = str(reason)


def init_ads_hardware():
    global _ads_i2c, _ads, _ph_chan, _tds_chan, _ads_error

    if _ads is not None and (_ph_chan is not None or _tds_chan is not None):
        return

    if ADS is None or board is None or busio is None or AnalogIn is None:
        _ads_error = ADS_IMPORT_ERROR or "ADS1115 libraries not available"
        return

    try:
        i2c = busio.I2C(board.SCL, board.SDA)
        deadline = time.monotonic() + 2.0
        while not i2c.try_lock():
            if time.monotonic() >= deadline:
                raise RuntimeError("Could not lock I2C bus for ADS1115")
            time.sleep(0.01)
        i2c.unlock()

        ads = ADS.ADS1115(i2c)
        ads.gain = PH_ADC_GAIN

        _ads_i2c = i2c
        _ads = ads
        _ph_chan = build_ads_channel(ads, PH_CHANNEL_INDEX) if PH_ENABLED else None
        _tds_chan = build_ads_channel(ads, TDS_CHANNEL_INDEX) if TDS_ENABLED else None
        _ads_error = None
    except Exception as exc:
        reset_ads_hardware(exc)


def init_temp_hardware():
    global _temp_ser, _temp_error

    if not TEMP_ENABLED:
        _temp_error = "Temperature disabled"
        return

    if _temp_ser is not None and getattr(_temp_ser, "is_open", False):
        return

    if serial is None:
        _temp_error = ATLAS_UART_IMPORT_ERROR or "pyserial not available"
        return

    try:
        _temp_ser = serial.Serial(
            TEMP_UART_PORT,
            TEMP_UART_BAUD,
            timeout=TEMP_UART_TIMEOUT,
            write_timeout=TEMP_UART_TIMEOUT,
        )
        try:
            _temp_ser.reset_input_buffer()
            _temp_ser.reset_output_buffer()
        except Exception:
            pass
        _temp_error = None
    except Exception as exc:
        reset_temp_hardware(exc)


def init_voc_hardware():
    global _voc, _voc_error

    if not VOC_ENABLED:
        _voc_error = "VOC disabled"
        return

    if _voc is not None:
        return

    init_ads_hardware()
    if _ads_i2c is None:
        _voc_error = _ads_error or "I2C unavailable"
        return

    if adafruit_sgp30 is None:
        _voc_error = VOC_IMPORT_ERROR or "SGP30 library unavailable"
        return

    try:
        _voc = adafruit_sgp30.Adafruit_SGP30(_ads_i2c)
        if hasattr(_voc, "iaq_init"):
            try:
                _voc.iaq_init()
            except Exception:
                pass
        _voc_error = None
    except Exception as exc:
        _voc = None
        _voc_error = str(exc)


def _temp_readline(timeout_s=2.0):
    init_temp_hardware()
    if _temp_ser is None:
        raise RuntimeError(_temp_error or "RTD UART unavailable")

    deadline = time.monotonic() + timeout_s
    buf = bytearray()
    while time.monotonic() < deadline:
        chunk = _temp_ser.read(1)
        if not chunk or chunk == b"\x00":
            continue
        if chunk in (b"\r", b"\n"):
            if buf:
                break
            continue
        buf.extend(chunk)
    return buf.decode("utf-8", errors="ignore").strip()


def ezo_uart_query(command="R", wait_s=1.0):
    init_temp_hardware()
    if _temp_ser is None:
        raise RuntimeError(_temp_error or "RTD UART unavailable")

    try:
        _temp_ser.reset_input_buffer()
    except Exception:
        pass

    _temp_ser.write((command + "\r").encode("utf-8"))
    _temp_ser.flush()
    time.sleep(wait_s)

    lines = []
    end_time = time.monotonic() + max(1.2, TEMP_UART_TIMEOUT + wait_s)
    while time.monotonic() < end_time:
        line = _temp_readline(timeout_s=0.35)
        if not line:
            continue
        lines.append(line)
        try:
            float(line)
            return line
        except Exception:
            pass

    if lines:
        raise RuntimeError("; ".join(lines))
    raise RuntimeError("No UART response from RTD")


def read_live_ph_hw(samples=PH_SAMPLES, sample_delay=PH_SAMPLE_DELAY):
    collect_enabled = get_ph_collect_enabled()
    if not collect_enabled:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": "Paused by user",
            "state": {"cls": "nodata", "text": "Paused"},
            "collecting_enabled": False,
            "quality": "Paused",
        }

    init_ads_hardware()
    if _ph_chan is None:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": _ads_error or "ADS1115 unavailable",
            "state": {"cls": "nodata", "text": "Unavailable"},
            "collecting_enabled": True,
            "quality": "No ADC",
        }

    voltages = []
    try:
        with _bench_lock:
            for _ in range(max(3, int(samples))):
                voltages.append(float(_ph_chan.voltage))
                time.sleep(sample_delay)
    except Exception as exc:
        reset_ads_hardware(exc)
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": len(voltages),
            "error": str(exc),
            "state": {"cls": "nodata", "text": "Read failed"},
            "collecting_enabled": True,
            "quality": "Read failed",
        }

    if not voltages:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": "No ADC samples returned",
            "state": {"cls": "nodata", "text": "No samples"},
            "collecting_enabled": True,
            "quality": "No samples",
        }

    voltage = round(median(voltages), 4)
    ph_value = surveyor_voltage_to_ph(voltage)
    if ph_value < -0.5 or ph_value > 14.5:
        ph_value = None
    else:
        ph_value = round(max(0.0, min(14.0, ph_value)), 2)

    quality = "Nominal voltage" if voltage is not None and PH_VOLTS_MIN - 0.1 <= voltage <= PH_VOLTS_MAX + 0.1 else "Review signal"
    return {
        "ok": True,
        "ph": ph_value,
        "voltage": voltage,
        "samples": len(voltages),
        "error": None,
        "state": ph_state_from_reading(voltage, ph_value),
        "collecting_enabled": True,
        "quality": quality,
    }


def read_live_temp_hw():
    try:
        with _bench_lock:
            text = ezo_uart_query("R", TEMP_READ_DELAY)
        temp_c = round(float(text), 2)
        return {
            "ok": True,
            "temp_c": temp_c,
            "temp_f": round(temp_c_to_f(temp_c), 2),
            "temp_k": round(temp_c_to_k(temp_c), 2),
            "samples": 1,
            "error": None,
            "state": temp_state_from_reading(temp_c),
            "quality": "RTD live",
        }
    except Exception as exc:
        reset_temp_hardware(exc)
        return {
            "ok": False,
            "temp_c": None,
            "temp_f": None,
            "temp_k": None,
            "samples": 0,
            "error": str(exc),
            "state": {"cls": "nodata", "text": "Unavailable"},
            "quality": "No RTD",
        }


def tds_voltage_to_ppm(voltage, temp_c=TDS_BASE_TEMP_C):
    if voltage is None:
        return None
    comp_coeff = 1.0 + 0.02 * (float(temp_c) - 25.0)
    comp_voltage = float(voltage) / comp_coeff
    ppm = (
        133.42 * comp_voltage * comp_voltage * comp_voltage
        - 255.86 * comp_voltage * comp_voltage
        + 857.39 * comp_voltage
    ) * 0.5
    return max(0.0, ppm)


def read_live_tds_hw(temp_c_for_comp=TDS_BASE_TEMP_C, samples=TDS_SAMPLES, sample_delay=TDS_SAMPLE_DELAY):
    init_ads_hardware()
    if _tds_chan is None:
        return {
            "ok": False,
            "tds_ppm": None,
            "voltage": None,
            "comp_temp_c": temp_c_for_comp,
            "samples": 0,
            "error": _ads_error or "ADS1115 unavailable",
            "state": {"cls": "nodata", "text": "Unavailable"},
            "quality": "No ADC",
        }

    voltages = []
    try:
        with _bench_lock:
            for _ in range(max(5, int(samples))):
                voltages.append(float(_tds_chan.voltage))
                time.sleep(sample_delay)
    except Exception as exc:
        reset_ads_hardware(exc)
        return {
            "ok": False,
            "tds_ppm": None,
            "voltage": None,
            "comp_temp_c": temp_c_for_comp,
            "samples": len(voltages),
            "error": str(exc),
            "state": {"cls": "nodata", "text": "Read failed"},
            "quality": "Read failed",
        }

    if not voltages:
        return {
            "ok": False,
            "tds_ppm": None,
            "voltage": None,
            "comp_temp_c": temp_c_for_comp,
            "samples": 0,
            "error": "No ADC samples returned",
            "state": {"cls": "nodata", "text": "No samples"},
            "quality": "No samples",
        }

    voltage = round(median(voltages), 4)
    tds_ppm = tds_voltage_to_ppm(voltage, temp_c_for_comp)
    ppm_value = None if tds_ppm is None else round(min(max(tds_ppm, 0.0), 5000.0), 1)
    quality = "Compensated with RTD" if _temp_last_live.get("ok") else "Using base temp"

    return {
        "ok": True,
        "tds_ppm": ppm_value,
        "voltage": voltage,
        "comp_temp_c": round(float(temp_c_for_comp), 2),
        "samples": len(voltages),
        "error": None,
        "state": tds_state_from_reading(voltage, ppm_value),
        "quality": quality,
    }


def read_live_voc_hw():
    init_voc_hardware()
    if _voc is None:
        return {
            "ok": False,
            "eco2_ppm": None,
            "tvoc_ppb": None,
            "samples": 0,
            "error": _voc_error or "SGP30 unavailable",
            "state": {"cls": "nodata", "text": "Unavailable"},
            "baseline_ready": False,
            "quality": "No SGP30",
        }

    try:
        with _bench_lock:
            if hasattr(_voc, "set_iaq_relative_humidity") and _temp_last_live.get("ok") and _temp_last_live.get("temp_c") is not None:
                try:
                    _voc.set_iaq_relative_humidity(celsius=float(_temp_last_live["temp_c"]), relative_humidity=50)
                except Exception:
                    pass
            eco2 = int(_voc.eCO2)
            tvoc = int(_voc.TVOC)

        warmup = eco2 <= 420 and tvoc == 0
        return {
            "ok": True,
            "eco2_ppm": eco2,
            "tvoc_ppb": tvoc,
            "samples": 1,
            "error": None,
            "state": voc_state_from_reading(eco2, tvoc),
            "baseline_ready": not warmup,
            "quality": "Humidity-compensated" if _temp_last_live.get("ok") else "No humidity compensation",
        }
    except Exception as exc:
        return {
            "ok": False,
            "eco2_ppm": None,
            "tvoc_ppb": None,
            "samples": 0,
            "error": str(exc),
            "state": {"cls": "nodata", "text": "Unavailable"},
            "baseline_ready": False,
            "quality": "Unavailable",
        }


def maybe_log_ph(ph_data):
    global _ph_last_logged
    if not ph_data.get("ok") or ph_data.get("ph") is None:
        return
    now = utc_now()
    if _ph_last_logged and (now - _ph_last_logged).total_seconds() < PH_LOG_EVERY_SECONDS:
        return
    ts = now.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    conn.execute(
        "INSERT INTO ph_readings (ts, ph_voltage, ph_value) VALUES (?, ?, ?)",
        (ts, ph_data["voltage"], ph_data["ph"]),
    )
    conn.commit()
    conn.close()
    _ph_last_logged = now


def maybe_log_temp(temp_data):
    global _temp_last_logged
    if not temp_data.get("ok") or temp_data.get("temp_c") is None:
        return
    now = utc_now()
    if _temp_last_logged and (now - _temp_last_logged).total_seconds() < TEMP_LOG_EVERY_SECONDS:
        return
    ts = now.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    conn.execute("INSERT INTO temp_readings (ts, temp_c) VALUES (?, ?)", (ts, temp_data["temp_c"]))
    conn.commit()
    conn.close()
    _temp_last_logged = now


def maybe_log_tds(tds_data):
    global _tds_last_logged
    if not tds_data.get("ok") or tds_data.get("tds_ppm") is None:
        return
    now = utc_now()
    if _tds_last_logged and (now - _tds_last_logged).total_seconds() < TDS_LOG_EVERY_SECONDS:
        return
    ts = now.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    conn.execute(
        "INSERT INTO tds_readings (ts, tds_voltage, tds_ppm, comp_temp_c) VALUES (?, ?, ?, ?)",
        (ts, tds_data["voltage"], tds_data["tds_ppm"], tds_data["comp_temp_c"]),
    )
    conn.commit()
    conn.close()
    _tds_last_logged = now


def maybe_log_voc(voc_data):
    global _voc_last_logged
    if not voc_data.get("ok"):
        return
    if voc_data.get("eco2_ppm") is None and voc_data.get("tvoc_ppb") is None:
        return
    now = utc_now()
    if _voc_last_logged and (now - _voc_last_logged).total_seconds() < VOC_LOG_EVERY_SECONDS:
        return
    ts = now.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    conn.execute(
        "INSERT INTO voc_readings (ts, eco2_ppm, tvoc_ppb) VALUES (?, ?, ?)",
        (ts, voc_data.get("eco2_ppm"), voc_data.get("tvoc_ppb")),
    )
    conn.commit()
    conn.close()
    _voc_last_logged = now


def bench_logger_loop():
    global _ph_last_live, _temp_last_live, _tds_last_live, _voc_last_live

    while not _bench_stop.is_set():
        now_iso = utc_now_iso()

        try:
            temp_data = read_live_temp_hw()
            temp_data["updated_at"] = now_iso if temp_data.get("ok") else _temp_last_live.get("updated_at")
            _temp_last_live = temp_data
            if temp_data.get("ok"):
                maybe_log_temp(temp_data)
        except Exception as exc:
            _temp_last_live = {
                "ok": False,
                "temp_c": None,
                "temp_f": None,
                "temp_k": None,
                "samples": 0,
                "error": str(exc),
                "state": {"cls": "nodata", "text": "Unavailable"},
                "updated_at": _temp_last_live.get("updated_at"),
                "quality": "Unavailable",
            }

        try:
            ph_data = read_live_ph_hw()
            ph_data["updated_at"] = now_iso if ph_data.get("ok") else _ph_last_live.get("updated_at")
            _ph_last_live = ph_data
            if ph_data.get("ok"):
                maybe_log_ph(ph_data)
        except Exception as exc:
            _ph_last_live = {
                "ok": False,
                "ph": None,
                "voltage": None,
                "samples": 0,
                "error": str(exc),
                "state": {"cls": "nodata", "text": "Unavailable"},
                "updated_at": _ph_last_live.get("updated_at"),
                "collecting_enabled": get_ph_collect_enabled(),
                "quality": "Unavailable",
            }

        try:
            comp_temp = _temp_last_live.get("temp_c") if _temp_last_live.get("ok") else TDS_BASE_TEMP_C
            tds_data = read_live_tds_hw(comp_temp)
            tds_data["updated_at"] = now_iso if tds_data.get("ok") else _tds_last_live.get("updated_at")
            _tds_last_live = tds_data
            if tds_data.get("ok"):
                maybe_log_tds(tds_data)
        except Exception as exc:
            _tds_last_live = {
                "ok": False,
                "tds_ppm": None,
                "voltage": None,
                "comp_temp_c": _temp_last_live.get("temp_c") if _temp_last_live.get("ok") else TDS_BASE_TEMP_C,
                "samples": 0,
                "error": str(exc),
                "state": {"cls": "nodata", "text": "Unavailable"},
                "updated_at": _tds_last_live.get("updated_at"),
                "quality": "Unavailable",
            }

        try:
            voc_data = read_live_voc_hw()
            voc_data["updated_at"] = now_iso if voc_data.get("ok") else _voc_last_live.get("updated_at")
            _voc_last_live = voc_data
            if voc_data.get("ok"):
                maybe_log_voc(voc_data)
        except Exception as exc:
            _voc_last_live = {
                "ok": False,
                "eco2_ppm": None,
                "tvoc_ppb": None,
                "samples": 0,
                "error": str(exc),
                "state": {"cls": "nodata", "text": "Unavailable"},
                "updated_at": _voc_last_live.get("updated_at"),
                "baseline_ready": False,
                "quality": "Unavailable",
            }

        _bench_stop.wait(BENCH_POLL_SECONDS)


def start_bench_logger():
    global _bench_thread
    if _bench_thread and _bench_thread.is_alive():
        return
    _bench_thread = threading.Thread(target=bench_logger_loop, name="bench-logger", daemon=True)
    _bench_thread.start()


def init_db():
    conn = db()
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS readings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            station_id TEXT NOT NULL,
            ts TEXT NOT NULL,
            air_temp_c REAL NOT NULL DEFAULT 0,
            humidity_pct REAL NOT NULL DEFAULT 0,
            soil_moisture_pct REAL NOT NULL DEFAULT 0,
            soil_moisture_1_pct REAL NOT NULL DEFAULT 0,
            soil_moisture_2_pct REAL NOT NULL DEFAULT 0,
            soil_raw_1 REAL NOT NULL DEFAULT 65535,
            soil_raw_2 REAL NOT NULL DEFAULT 65535,
            eco2_ppm REAL NOT NULL DEFAULT 0
        )
        """
    )

    existing = {row["name"] for row in conn.execute("PRAGMA table_info(readings)").fetchall()}
    needed = {
        "soil_moisture_1_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_2_pct": "REAL NOT NULL DEFAULT 0",
        "soil_raw_1": "REAL NOT NULL DEFAULT 65535",
        "soil_raw_2": "REAL NOT NULL DEFAULT 65535",
        "eco2_ppm": "REAL NOT NULL DEFAULT 0",
        "air_temp_c": "REAL NOT NULL DEFAULT 0",
        "humidity_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_pct": "REAL NOT NULL DEFAULT 0",
    }
    for col, coltype in needed.items():
        if col not in existing:
            conn.execute(f"ALTER TABLE readings ADD COLUMN {col} {coltype}")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS station_config (
            station_id TEXT PRIMARY KEY,
            display_name TEXT NOT NULL DEFAULT '',
            description TEXT NOT NULL DEFAULT '',
            default_hours INTEGER NOT NULL DEFAULT 24,
            is_collapsed INTEGER NOT NULL DEFAULT 0
        )
        """
    )

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS probe_config (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            station_id TEXT NOT NULL,
            probe_key TEXT NOT NULL,
            display_name TEXT NOT NULL DEFAULT '',
            location_name TEXT NOT NULL DEFAULT '',
            danger_low REAL NOT NULL,
            warn_low REAL NOT NULL,
            target_low REAL NOT NULL,
            target_high REAL NOT NULL,
            warn_high REAL NOT NULL,
            enabled INTEGER NOT NULL DEFAULT 1,
            UNIQUE(station_id, probe_key)
        )
        """
    )

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS bench_config (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )
        """
    )
    defaults = {
        "ph_collect_enabled": "1",
        "ph_cal_scale": str(PH_CAL_SCALE),
        "ph_cal_offset": str(PH_CAL_OFFSET),
        "ph_cal_mode": "factory",
        "ph_cal_last_ts": "",
        "ph_cal_last_target": "",
    }
    for key, value in defaults.items():
        conn.execute(
            "INSERT INTO bench_config (key, value) VALUES (?, ?) ON CONFLICT(key) DO NOTHING",
            (key, value),
        )

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS ph_readings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT NOT NULL,
            ph_voltage REAL,
            ph_value REAL
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_ph_readings_ts ON ph_readings(ts)")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS temp_readings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT NOT NULL,
            temp_c REAL
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_temp_readings_ts ON temp_readings(ts)")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS tds_readings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT NOT NULL,
            tds_voltage REAL,
            tds_ppm REAL,
            comp_temp_c REAL
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_tds_readings_ts ON tds_readings(ts)")

    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS voc_readings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts TEXT NOT NULL,
            eco2_ppm REAL,
            tvoc_ppb REAL
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_voc_readings_ts ON voc_readings(ts)")

    conn.commit()
    conn.close()


@app.route("/ingest", methods=["POST"])
def ingest():
    payload = request.get_json(force=True, silent=True) or {}
    station_id = str(payload.get("station_id", "unknown")).strip() or "unknown"
    ts = utc_now_iso()

    air_temp_c = safe_num(payload.get("air_temp_c", 0))
    humidity_pct = safe_num(payload.get("humidity_pct", 0))
    eco2_ppm = safe_num(payload.get("eco2_ppm", 0))

    soil_raw_1 = safe_num(payload.get("soil_raw_1", 65535), 65535)
    soil_raw_2 = safe_num(payload.get("soil_raw_2", 65535), 65535)
    soil_1 = safe_num(payload.get("soil_moisture_1_pct", 0), 0)
    soil_2 = safe_num(payload.get("soil_moisture_2_pct", 0), 0)

    valid = []
    if soil_raw_1 < 65535:
        valid.append(soil_1)
    if soil_raw_2 < 65535:
        valid.append(soil_2)

    soil_avg = (sum(valid) / len(valid)) if valid else safe_num(payload.get("soil_moisture_pct", 0), 0)

    conn = db()
    ensure_station_defaults(conn, station_id)
    conn.execute(
        """
        INSERT INTO readings (
            station_id, ts, air_temp_c, humidity_pct,
            soil_moisture_pct, soil_moisture_1_pct, soil_moisture_2_pct,
            soil_raw_1, soil_raw_2, eco2_ppm
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            station_id,
            ts,
            air_temp_c,
            humidity_pct,
            soil_avg,
            soil_1,
            soil_2,
            soil_raw_1,
            soil_raw_2,
            eco2_ppm,
        ),
    )
    conn.commit()
    conn.close()
    return jsonify({"ok": True})


@app.route("/api/dashboard")
def api_dashboard():
    conn = db()
    latest_rows = conn.execute(
        """
        SELECT r1.*
        FROM readings r1
        JOIN (
            SELECT station_id, MAX(ts) AS max_ts
            FROM readings
            GROUP BY station_id
        ) r2
          ON r1.station_id = r2.station_id
         AND r1.ts = r2.max_ts
        ORDER BY r1.station_id
        """
    ).fetchall()

    results = []
    for row in latest_rows:
        station_id = row["station_id"]
        station_cfg = get_station_config(conn, station_id)
        probe_cfgs = get_probe_configs(conn, station_id)
        station_current = station_value_from_row(row)

        probes = []
        alert_count = 0
        for probe in PROBES:
            probe_cfg = probe_cfgs[probe["key"]]
            current = current_value_from_row(row, probe["key"])
            rules = {
                "danger_low": probe_cfg["danger_low"],
                "warn_low": probe_cfg["warn_low"],
                "target_low": probe_cfg["target_low"],
                "target_high": probe_cfg["target_high"],
                "warn_high": probe_cfg["warn_high"],
            }
            state = value_state(current, rules)
            if state["cls"] in ("warn", "bad"):
                alert_count += 1
            probes.append(
                {
                    "probe_key": probe["key"],
                    "raw_key": probe["raw_key"],
                    "display_name": probe_cfg["display_name"] or probe["default_name"],
                    "location_name": probe_cfg["location_name"] or "",
                    "current": current,
                    "raw": safe_num(row[probe["raw_key"]], 65535),
                    "enabled": bool(probe_cfg["enabled"]),
                    "rules": rules,
                    "state": state,
                }
            )

        results.append(
            {
                "station_id": station_id,
                "display_name": station_cfg["display_name"] or station_id,
                "description": station_cfg["description"] or "",
                "default_hours": clamp_hours(station_cfg["default_hours"]),
                "is_collapsed": bool(station_cfg["is_collapsed"]),
                "updated_at": row["ts"],
                "updated_ago": age_text(row["ts"]),
                "connectivity": connectivity_meta(row["ts"]),
                "station_state": value_state(station_current, get_base_rules(station_id)),
                "probe_count": len(probes),
                "alert_count": alert_count,
                "probes": probes,
            }
        )

    conn.close()
    return jsonify(results)


@app.route("/api/probe-metrics/<station_id>/<probe_key>")
def api_probe_metrics(station_id, probe_key):
    if probe_key not in PROBE_INDEX:
        return jsonify({"error": "Unknown probe"}), 404

    hours = clamp_hours(request.args.get("hours", DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    expr = probe_value_sql(probe_key)

    conn = db()
    stats = conn.execute(
        f"""
        SELECT COUNT({expr}) AS points,
               AVG({expr}) AS avg_value,
               MIN({expr}) AS min_value,
               MAX({expr}) AS max_value
        FROM readings
        WHERE station_id = ? AND ts >= ?
        """,
        (station_id, since),
    ).fetchone()
    conn.close()

    return jsonify(
        {
            "hours": hours,
            "points": int(stats["points"] or 0),
            "avg": None if stats["avg_value"] is None else float(stats["avg_value"]),
            "min": None if stats["min_value"] is None else float(stats["min_value"]),
            "max": None if stats["max_value"] is None else float(stats["max_value"]),
        }
    )


@app.route("/api/config/<station_id>", methods=["POST"])
def api_save_config(station_id):
    payload = request.get_json(force=True, silent=True) or {}
    station = payload.get("station", {}) or {}
    probes = payload.get("probes", {}) or {}

    conn = db()
    ensure_station_defaults(conn, station_id)
    current_station = get_station_config(conn, station_id)

    display_name = str(station.get("display_name", current_station["display_name"])).strip() or station_id
    description = str(station.get("description", current_station["description"])).strip()
    default_hours = clamp_hours(station.get("default_hours", current_station["default_hours"]))
    is_collapsed = 1 if bool(station.get("is_collapsed", current_station["is_collapsed"])) else 0

    conn.execute(
        """
        INSERT INTO station_config (station_id, display_name, description, default_hours, is_collapsed)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(station_id) DO UPDATE SET
            display_name = excluded.display_name,
            description = excluded.description,
            default_hours = excluded.default_hours,
            is_collapsed = excluded.is_collapsed
        """,
        (station_id, display_name, description, default_hours, is_collapsed),
    )

    current_probes = get_probe_configs(conn, station_id)
    for probe_key, probe_data in probes.items():
        if probe_key not in PROBE_INDEX:
            continue
        old = current_probes[probe_key]
        display_name = str(probe_data.get("display_name", old["display_name"])).strip() or PROBE_INDEX[probe_key]["default_name"]
        location_name = str(probe_data.get("location_name", old["location_name"])).strip()
        enabled = 1 if bool(probe_data.get("enabled", old["enabled"])) else 0

        danger_low = clamp_percent(probe_data.get("danger_low"), old["danger_low"])
        warn_low = clamp_percent(probe_data.get("warn_low"), old["warn_low"])
        target_low = clamp_percent(probe_data.get("target_low"), old["target_low"])
        target_high = clamp_percent(probe_data.get("target_high"), old["target_high"])
        warn_high = clamp_percent(probe_data.get("warn_high"), old["warn_high"])

        if not (danger_low <= warn_low <= target_low <= target_high <= warn_high):
            return jsonify({"error": f"Bad threshold order for {probe_key}"}), 400

        conn.execute(
            """
            INSERT INTO probe_config (
                station_id, probe_key, display_name, location_name,
                danger_low, warn_low, target_low, target_high, warn_high, enabled
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(station_id, probe_key) DO UPDATE SET
                display_name = excluded.display_name,
                location_name = excluded.location_name,
                danger_low = excluded.danger_low,
                warn_low = excluded.warn_low,
                target_low = excluded.target_low,
                target_high = excluded.target_high,
                warn_high = excluded.warn_high,
                enabled = excluded.enabled
            """,
            (
                station_id,
                probe_key,
                display_name,
                location_name,
                danger_low,
                warn_low,
                target_low,
                target_high,
                warn_high,
                enabled,
            ),
        )

    conn.commit()
    conn.close()
    return jsonify({"ok": True})


@app.route("/api/history/<series_key>")
def api_history(series_key):
    cfg = SERIES_CONFIG.get(series_key)
    if not cfg:
        return jsonify({"error": "Unknown series"}), 404

    hours = clamp_hours(request.args.get("hours", 24, type=int))
    bucket_s = clamp_bucket_s(request.args.get("bucket_s", 60, type=int), hours)
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    bucket_expr = f"""
        strftime(
            '%Y-%m-%dT%H:%M:%SZ',
            (CAST(strftime('%s', ts) AS INTEGER) / {bucket_s}) * {bucket_s},
            'unixepoch'
        )
    """

    value_col = cfg["value_col"]

    conn = db()
    rows = conn.execute(
        f"""
        SELECT
            {bucket_expr} AS ts,
            AVG({value_col}) AS value,
            MIN({value_col}) AS min_value,
            MAX({value_col}) AS max_value,
            COUNT({value_col}) AS samples
        FROM {cfg['table']}
        WHERE ts >= ?
          AND {value_col} IS NOT NULL
        GROUP BY 1
        ORDER BY 1 ASC
        """,
        (since,),
    ).fetchall()
    conn.close()

    return jsonify({
        "series": series_key,
        "hours": hours,
        "bucket_s": bucket_s,
        "points": [
            {
                "ts": row["ts"],
                "value": None if row["value"] is None else float(row["value"]),
                "min": None if row["min_value"] is None else float(row["min_value"]),
                "max": None if row["max_value"] is None else float(row["max_value"]),
                "samples": int(row["samples"] or 0),
            }
            for row in rows
        ],
    })


@app.route("/api/ph-live")
def api_ph_live():
    payload = dict(_ph_last_live)
    payload["calibration"] = get_ph_calibration()
    return jsonify(payload)


@app.route("/api/ph-collect-enabled", methods=["GET", "POST"])
def api_ph_collect_enabled():
    global _ph_last_live, _ph_last_logged

    if request.method == "GET":
        return jsonify({"enabled": get_ph_collect_enabled()})

    payload = request.get_json(force=True, silent=True) or {}
    enabled = bool(payload.get("enabled", True))

    conn = db()
    bench_setting_set(conn, "ph_collect_enabled", "1" if enabled else "0")
    conn.commit()
    conn.close()

    if not enabled:
        _ph_last_live = {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": "Paused by user",
            "state": {"cls": "nodata", "text": "Paused"},
            "updated_at": _ph_last_live.get("updated_at"),
            "collecting_enabled": False,
            "quality": "Paused",
        }
    else:
        _ph_last_logged = None

    return jsonify({"ok": True, "enabled": enabled})


@app.route("/api/ph-calibration", methods=["GET", "POST"])
def api_ph_calibration():
    if request.method == "GET":
        return jsonify(get_ph_calibration())

    payload = request.get_json(force=True, silent=True) or {}
    mode = str(payload.get("mode", "single_offset")).strip()

    conn = db()
    try:
        if mode == "single_offset":
            target_ph = safe_num(payload.get("target_ph"), math.nan)
            observed_voltage = payload.get("observed_voltage", _ph_last_live.get("voltage"))
            observed_voltage = safe_num(observed_voltage, math.nan)
            if not math.isfinite(target_ph) or not math.isfinite(observed_voltage):
                return jsonify({"error": "Need target_ph and observed_voltage"}), 400

            raw_ph = (PH_SLOPE * observed_voltage) + PH_INTERCEPT
            new_offset = float(target_ph) - raw_ph
            bench_setting_set(conn, "ph_cal_scale", "1.0")
            bench_setting_set(conn, "ph_cal_offset", f"{new_offset:.8f}")
            bench_setting_set(conn, "ph_cal_mode", "single_offset")
            bench_setting_set(conn, "ph_cal_last_ts", utc_now_iso())
            bench_setting_set(conn, "ph_cal_last_target", f"{target_ph:.4f}")
            conn.commit()
            return jsonify({"ok": True, "calibration": get_ph_calibration()})

        if mode == "reset":
            bench_setting_set(conn, "ph_cal_scale", str(PH_CAL_SCALE))
            bench_setting_set(conn, "ph_cal_offset", str(PH_CAL_OFFSET))
            bench_setting_set(conn, "ph_cal_mode", "factory")
            bench_setting_set(conn, "ph_cal_last_ts", utc_now_iso())
            bench_setting_set(conn, "ph_cal_last_target", "")
            conn.commit()
            return jsonify({"ok": True, "calibration": get_ph_calibration()})

        return jsonify({"error": "Unsupported calibration mode"}), 400
    finally:
        conn.close()


@app.route("/api/ph-metrics")
def api_ph_metrics():
    hours = clamp_hours(request.args.get("hours", PH_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()
    stats = conn.execute(
        """
        SELECT COUNT(ph_value) AS points,
               AVG(ph_value) AS avg_value,
               MIN(ph_value) AS min_value,
               MAX(ph_value) AS max_value,
               AVG(ph_voltage) AS avg_voltage,
               MAX(ts) AS last_ts
        FROM ph_readings
        WHERE ts >= ?
        """,
        (since,),
    ).fetchone()
    conn.close()

    return jsonify(
        {
            "hours": hours,
            "points": int(stats["points"] or 0),
            "avg": None if stats["avg_value"] is None else float(stats["avg_value"]),
            "min": None if stats["min_value"] is None else float(stats["min_value"]),
            "max": None if stats["max_value"] is None else float(stats["max_value"]),
            "avg_voltage": None if stats["avg_voltage"] is None else float(stats["avg_voltage"]),
            "last_ts": stats["last_ts"],
        }
    )


@app.route("/api/ph-recent")
def api_ph_recent():
    limit = max(1, min(100, request.args.get("limit", PH_RECENT_LIMIT, type=int)))
    conn = db()
    rows = conn.execute(
        """
        SELECT ts, ph_voltage, ph_value
        FROM ph_readings
        WHERE ph_value IS NOT NULL
        ORDER BY ts DESC
        LIMIT 250
        """
    ).fetchall()
    conn.close()

    recent = []
    last_value = None
    for row in rows:
        val = safe_num(row["ph_value"], math.nan)
        if not math.isfinite(val):
            continue
        if last_value is None or abs(val - last_value) >= PH_CHANGE_EPSILON:
            recent.append(
                {
                    "ts": row["ts"],
                    "ph": round(val, 2),
                    "voltage": None if row["ph_voltage"] is None else round(float(row["ph_voltage"]), 4),
                }
            )
            last_value = val
        if len(recent) >= limit:
            break
    return jsonify(recent)


@app.route("/api/ph-reset", methods=["POST"])
def api_ph_reset():
    global _ph_last_logged
    conn = db()
    conn.execute("DELETE FROM ph_readings")
    conn.commit()
    conn.close()
    _ph_last_logged = None
    return jsonify({"ok": True})


@app.route("/api/temp-live")
def api_temp_live():
    return jsonify(_temp_last_live)


@app.route("/api/temp-metrics")
def api_temp_metrics():
    hours = clamp_hours(request.args.get("hours", TEMP_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    stats = conn.execute(
        """
        SELECT COUNT(temp_c) AS points,
               AVG(temp_c) AS avg_value,
               MIN(temp_c) AS min_value,
               MAX(temp_c) AS max_value,
               MAX(ts) AS last_ts
        FROM temp_readings
        WHERE ts >= ?
        """,
        (since,),
    ).fetchone()
    conn.close()
    avg_c = None if stats["avg_value"] is None else float(stats["avg_value"])
    min_c = None if stats["min_value"] is None else float(stats["min_value"])
    max_c = None if stats["max_value"] is None else float(stats["max_value"])
    return jsonify(
        {
            "hours": hours,
            "points": int(stats["points"] or 0),
            "avg": avg_c,
            "avg_f": None if avg_c is None else temp_c_to_f(avg_c),
            "avg_k": None if avg_c is None else temp_c_to_k(avg_c),
            "min": min_c,
            "max": max_c,
            "last_ts": stats["last_ts"],
        }
    )


@app.route("/api/temp-recent")
def api_temp_recent():
    limit = max(1, min(100, request.args.get("limit", TEMP_RECENT_LIMIT, type=int)))
    conn = db()
    rows = conn.execute(
        """
        SELECT ts, temp_c
        FROM temp_readings
        WHERE temp_c IS NOT NULL
        ORDER BY ts DESC
        LIMIT 250
        """
    ).fetchall()
    conn.close()

    recent = []
    last_value = None
    for row in rows:
        val = safe_num(row["temp_c"], math.nan)
        if not math.isfinite(val):
            continue
        if last_value is None or abs(val - last_value) >= TEMP_CHANGE_EPSILON:
            recent.append({"ts": row["ts"], "temp_c": round(val, 2)})
            last_value = val
        if len(recent) >= limit:
            break
    return jsonify(recent)


@app.route("/api/temp-reset", methods=["POST"])
def api_temp_reset():
    global _temp_last_logged
    conn = db()
    conn.execute("DELETE FROM temp_readings")
    conn.commit()
    conn.close()
    _temp_last_logged = None
    return jsonify({"ok": True})


@app.route("/api/tds-live")
def api_tds_live():
    return jsonify(_tds_last_live)


@app.route("/api/tds-metrics")
def api_tds_metrics():
    hours = clamp_hours(request.args.get("hours", TDS_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    stats = conn.execute(
        """
        SELECT COUNT(tds_ppm) AS points,
               AVG(tds_ppm) AS avg_value,
               MIN(tds_ppm) AS min_value,
               MAX(tds_ppm) AS max_value,
               AVG(tds_voltage) AS avg_voltage,
               AVG(comp_temp_c) AS avg_comp_temp_c,
               MAX(ts) AS last_ts
        FROM tds_readings
        WHERE ts >= ?
        """,
        (since,),
    ).fetchone()
    conn.close()
    return jsonify(
        {
            "hours": hours,
            "points": int(stats["points"] or 0),
            "avg": None if stats["avg_value"] is None else float(stats["avg_value"]),
            "min": None if stats["min_value"] is None else float(stats["min_value"]),
            "max": None if stats["max_value"] is None else float(stats["max_value"]),
            "avg_voltage": None if stats["avg_voltage"] is None else float(stats["avg_voltage"]),
            "avg_comp_temp_c": None if stats["avg_comp_temp_c"] is None else float(stats["avg_comp_temp_c"]),
            "last_ts": stats["last_ts"],
        }
    )


@app.route("/api/tds-recent")
def api_tds_recent():
    limit = max(1, min(100, request.args.get("limit", TDS_RECENT_LIMIT, type=int)))
    conn = db()
    rows = conn.execute(
        """
        SELECT ts, tds_voltage, tds_ppm, comp_temp_c
        FROM tds_readings
        WHERE tds_ppm IS NOT NULL
        ORDER BY ts DESC
        LIMIT 250
        """
    ).fetchall()
    conn.close()

    recent = []
    last_value = None
    for row in rows:
        val = safe_num(row["tds_ppm"], math.nan)
        if not math.isfinite(val):
            continue
        if last_value is None or abs(val - last_value) >= TDS_CHANGE_EPSILON:
            recent.append(
                {
                    "ts": row["ts"],
                    "tds_ppm": round(val, 1),
                    "voltage": None if row["tds_voltage"] is None else round(float(row["tds_voltage"]), 4),
                    "comp_temp_c": None if row["comp_temp_c"] is None else round(float(row["comp_temp_c"]), 2),
                }
            )
            last_value = val
        if len(recent) >= limit:
            break
    return jsonify(recent)


@app.route("/api/tds-reset", methods=["POST"])
def api_tds_reset():
    global _tds_last_logged
    conn = db()
    conn.execute("DELETE FROM tds_readings")
    conn.commit()
    conn.close()
    _tds_last_logged = None
    return jsonify({"ok": True})


@app.route("/api/voc-live")
def api_voc_live():
    return jsonify(_voc_last_live)


@app.route("/api/voc-metrics")
def api_voc_metrics():
    hours = clamp_hours(request.args.get("hours", VOC_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    stats = conn.execute(
        """
        SELECT COUNT(eco2_ppm) AS points,
               AVG(eco2_ppm) AS avg_eco2,
               MIN(eco2_ppm) AS min_eco2,
               MAX(eco2_ppm) AS max_eco2,
               AVG(tvoc_ppb) AS avg_tvoc,
               MIN(tvoc_ppb) AS min_tvoc,
               MAX(tvoc_ppb) AS max_tvoc,
               MAX(ts) AS last_ts
        FROM voc_readings
        WHERE ts >= ?
        """,
        (since,),
    ).fetchone()
    conn.close()
    return jsonify({
        "hours": hours,
        "points": int(stats["points"] or 0),
        "avg_eco2": None if stats["avg_eco2"] is None else float(stats["avg_eco2"]),
        "min_eco2": None if stats["min_eco2"] is None else float(stats["min_eco2"]),
        "max_eco2": None if stats["max_eco2"] is None else float(stats["max_eco2"]),
        "avg_tvoc": None if stats["avg_tvoc"] is None else float(stats["avg_tvoc"]),
        "min_tvoc": None if stats["min_tvoc"] is None else float(stats["min_tvoc"]),
        "max_tvoc": None if stats["max_tvoc"] is None else float(stats["max_tvoc"]),
        "last_ts": stats["last_ts"],
    })


@app.route("/api/voc-recent")
def api_voc_recent():
    limit = max(1, min(100, request.args.get("limit", VOC_RECENT_LIMIT, type=int)))
    conn = db()
    rows = conn.execute(
        """
        SELECT ts, eco2_ppm, tvoc_ppb
        FROM voc_readings
        WHERE eco2_ppm IS NOT NULL OR tvoc_ppb IS NOT NULL
        ORDER BY ts DESC
        LIMIT 250
        """
    ).fetchall()
    conn.close()

    recent = []
    last_eco2 = None
    last_tvoc = None
    for row in rows:
        eco2 = None if row["eco2_ppm"] is None else float(row["eco2_ppm"])
        tvoc = None if row["tvoc_ppb"] is None else float(row["tvoc_ppb"])
        changed = False
        if eco2 is not None and (last_eco2 is None or abs(eco2 - last_eco2) >= VOC_CHANGE_ECO2_EPSILON):
            changed = True
        if tvoc is not None and (last_tvoc is None or abs(tvoc - last_tvoc) >= VOC_CHANGE_TVOC_EPSILON):
            changed = True
        if changed:
            recent.append({
                "ts": row["ts"],
                "eco2_ppm": eco2,
                "tvoc_ppb": tvoc,
            })
            last_eco2 = eco2
            last_tvoc = tvoc
        if len(recent) >= limit:
            break
    return jsonify(recent)


@app.route("/api/voc-reset", methods=["POST"])
def api_voc_reset():
    global _voc_last_logged
    conn = db()
    conn.execute("DELETE FROM voc_readings")
    conn.commit()
    conn.close()
    _voc_last_logged = None
    return jsonify({"ok": True})


def render_series_plot(rows, parse_value, title, y_label, hours, y_min=None, y_max=None):
    fig, ax = plt.subplots(figsize=(10, 3.3))
    times = []
    values = []
    for row in rows:
        times.append(parse_iso(row["ts"]))
        values.append(parse_value(row))

    plot_values = [math.nan if v is None else v for v in values]
    valid_points = sum(0 if math.isnan(v) else 1 for v in plot_values)

    if valid_points:
        ax.plot(times, plot_values, linewidth=2.2)
        if y_min is not None or y_max is not None:
            ax.set_ylim(y_min, y_max)
        ax.set_ylabel(y_label)
        ax.grid(True, alpha=0.28)

        if hours <= 1:
            locator = mdates.MinuteLocator(interval=10)
        elif hours <= 24:
            locator = mdates.HourLocator(interval=2)
        else:
            locator = mdates.DayLocator(interval=1)

        ax.xaxis.set_major_locator(locator)
        ax.xaxis.set_major_formatter(mdates.ConciseDateFormatter(locator))
    else:
        ax.text(0.5, 0.54, "No valid data in selected window", ha="center", va="center", transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_visible(False)

    ax.set_title(f"{title} · last {hours}h")
    fig.tight_layout()

    buf = io.StringIO()
    fig.savefig(buf, format="svg", bbox_inches="tight")
    plt.close(fig)
    return Response(buf.getvalue(), mimetype="image/svg+xml")


@app.route("/plot/ph.svg")
def plot_ph():
    hours = clamp_hours(request.args.get("hours", PH_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    rows = conn.execute("SELECT ts, ph_value FROM ph_readings WHERE ts >= ? ORDER BY ts ASC", (since,)).fetchall()
    conn.close()
    return render_series_plot(
        rows=rows,
        parse_value=lambda row: None if row["ph_value"] is None else float(row["ph_value"]),
        title="Bench pH Probe",
        y_label="pH",
        hours=hours,
        y_min=0,
        y_max=14,
    )


@app.route("/plot/temp.svg")
def plot_temp():
    hours = clamp_hours(request.args.get("hours", TEMP_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    rows = conn.execute("SELECT ts, temp_c FROM temp_readings WHERE ts >= ? ORDER BY ts ASC", (since,)).fetchall()
    conn.close()
    return render_series_plot(
        rows=rows,
        parse_value=lambda row: None if row["temp_c"] is None else float(row["temp_c"]),
        title="Bench Temperature Probe",
        y_label="°C",
        hours=hours,
    )


@app.route("/plot/tds.svg")
def plot_tds():
    hours = clamp_hours(request.args.get("hours", TDS_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    rows = conn.execute("SELECT ts, tds_ppm FROM tds_readings WHERE ts >= ? ORDER BY ts ASC", (since,)).fetchall()
    conn.close()
    return render_series_plot(
        rows=rows,
        parse_value=lambda row: None if row["tds_ppm"] is None else float(row["tds_ppm"]),
        title="Bench TDS Probe",
        y_label="ppm",
        hours=hours,
    )


@app.route("/plot/voc_eco2.svg")
def plot_voc_eco2():
    hours = clamp_hours(request.args.get("hours", VOC_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    rows = conn.execute("SELECT ts, eco2_ppm FROM voc_readings WHERE ts >= ? ORDER BY ts ASC", (since,)).fetchall()
    conn.close()
    return render_series_plot(
        rows=rows,
        parse_value=lambda row: None if row["eco2_ppm"] is None else float(row["eco2_ppm"]),
        title="Bench eCO₂",
        y_label="ppm",
        hours=hours,
    )


@app.route("/plot/voc_tvoc.svg")
def plot_voc_tvoc():
    hours = clamp_hours(request.args.get("hours", VOC_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    conn = db()
    rows = conn.execute("SELECT ts, tvoc_ppb FROM voc_readings WHERE ts >= ? ORDER BY ts ASC", (since,)).fetchall()
    conn.close()
    return render_series_plot(
        rows=rows,
        parse_value=lambda row: None if row["tvoc_ppb"] is None else float(row["tvoc_ppb"]),
        title="Bench TVOC",
        y_label="ppb",
        hours=hours,
    )


@app.route("/plot/<station_id>/<probe_key>.svg")
def plot_probe(station_id, probe_key):
    if probe_key not in PROBE_INDEX:
        return Response("Unknown probe", status=404)

    hours = clamp_hours(request.args.get("hours", DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    probe = PROBE_INDEX[probe_key]

    conn = db()
    ensure_station_defaults(conn, station_id)
    probe_cfgs = get_probe_configs(conn, station_id)
    cfg = probe_cfgs[probe_key]
    rows = conn.execute(
        f"""
        SELECT ts, {probe_key} AS probe_value, {probe['raw_key']} AS raw_value
        FROM readings
        WHERE station_id = ? AND ts >= ?
        ORDER BY ts ASC
        """,
        (station_id, since),
    ).fetchall()
    conn.close()

    fig, ax = plt.subplots(figsize=(10, 3.3))
    values = []
    times = []

    for row in rows:
        times.append(parse_iso(row["ts"]))
        raw = safe_num(row["raw_value"], 65535)
        val = safe_num(row["probe_value"], 0)
        if raw >= 65535 or val < 0 or val > 100:
            values.append(math.nan)
        else:
            values.append(val)

    valid_points = sum(0 if math.isnan(v) else 1 for v in values)
    if valid_points:
        ax.axhspan(cfg["target_low"], cfg["target_high"], alpha=0.10)
        ax.axhline(cfg["warn_low"], linewidth=1.0, alpha=0.35, linestyle="--")
        ax.axhline(cfg["warn_high"], linewidth=1.0, alpha=0.35, linestyle="--")
        ax.plot(times, values, linewidth=2.2)
        ax.set_ylim(0, 100)
        ax.set_ylabel("Soil moisture %")
        ax.grid(True, alpha=0.28)
        if hours <= 1:
            locator = mdates.MinuteLocator(interval=10)
        elif hours <= 24:
            locator = mdates.HourLocator(interval=2)
        else:
            locator = mdates.DayLocator(interval=1)
        ax.xaxis.set_major_locator(locator)
        ax.xaxis.set_major_formatter(mdates.ConciseDateFormatter(locator))
    else:
        ax.text(0.5, 0.54, "No valid data in selected window", ha="center", va="center", transform=ax.transAxes)
        ax.text(0.5, 0.40, "Live status still uses the most recent reading.", ha="center", va="center", fontsize=9, transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_visible(False)

    ax.set_title(f"{cfg['display_name']} · last {hours}h")
    fig.tight_layout()

    buf = io.StringIO()
    fig.savefig(buf, format="svg", bbox_inches="tight")
    plt.close(fig)
    return Response(buf.getvalue(), mimetype="image/svg+xml")

from flask import Response
import json


def home():
    html = '''
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>Sensor Host</title>
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>
    :root {
      --bg: #eef2f5;
      --panel: #ffffff;
      --panel-soft: #f8fafc;
      --text: #16202a;
      --muted: #667281;
      --border: #d7dee6;
      --shadow: 0 12px 32px rgba(17, 28, 40, 0.08);
      --ok-bg: #eaf8ef;
      --ok-border: #8ac89d;
      --warn-bg: #fff5de;
      --warn-border: #e3b454;
      --bad-bg: #fdeaea;
      --bad-border: #de7b7b;
      --nodata-bg: #f2f5f8;
      --nodata-border: #cbd5df;
      --accent: #2d6cdf;
      --accent-soft: #e7efff;
      --online: #37b24d;
      --stale: #f59f00;
      --offline: #e03131;
      --radius: 18px;
    }

    * { box-sizing: border-box; }
    body {
      margin: 0;
      font-family: Arial, sans-serif;
      background: linear-gradient(180deg, #f6f8fb 0%, #eef2f5 100%);
      color: var(--text);
    }
    .wrap {
      max-width: 1380px;
      margin: 0 auto;
      padding: 20px;
    }
    .topbar {
      display: flex;
      align-items: end;
      justify-content: space-between;
      gap: 16px;
      flex-wrap: wrap;
      margin-bottom: 20px;
    }
    h1 {
      margin: 0 0 6px;
      font-size: 2.1rem;
      line-height: 1.05;
    }
    .subhead {
      color: var(--muted);
      font-size: 1rem;
    }
    .global-note {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px 14px;
      box-shadow: var(--shadow);
      color: var(--muted);
      font-size: 0.95rem;
      max-width: 520px;
    }
    .empty, .loading {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: var(--radius);
      padding: 24px;
      box-shadow: var(--shadow);
    }
    #bench-slot { margin-bottom: 18px; }

    .station {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 22px;
      box-shadow: var(--shadow);
      margin-bottom: 18px;
      overflow: hidden;
    }
    .station summary {
      list-style: none;
      cursor: pointer;
      padding: 16px 18px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 14px;
      background: linear-gradient(180deg, #ffffff 0%, #fbfcfd 100%);
    }
    .station summary::-webkit-details-marker { display: none; }
    .summary-left {
      min-width: 0;
      display: flex;
      align-items: center;
      gap: 12px;
      flex: 1;
    }
    .status-dot {
      width: 12px;
      height: 12px;
      border-radius: 999px;
      flex: 0 0 12px;
      box-shadow: 0 0 0 3px rgba(0,0,0,0.04);
    }
    .status-dot.online { background: var(--online); }
    .status-dot.stale { background: var(--stale); }
    .status-dot.offline { background: var(--offline); }
    .summary-text {
      min-width: 0;
      flex: 1;
    }
    .station-name {
      font-size: 1.2rem;
      font-weight: 800;
      margin: 0 0 3px;
      line-height: 1.15;
    }
    .station-meta {
      color: var(--muted);
      font-size: 0.95rem;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }
    .summary-right {
      display: flex;
      align-items: center;
      gap: 10px;
      flex-wrap: wrap;
      justify-content: flex-end;
    }
    .pill {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      border-radius: 999px;
      padding: 8px 12px;
      border: 1px solid var(--border);
      background: var(--panel-soft);
      font-size: 0.92rem;
      font-weight: 700;
    }
    .pill.ok { background: var(--ok-bg); border-color: var(--ok-border); }
    .pill.warn { background: var(--warn-bg); border-color: var(--warn-border); }
    .pill.bad { background: var(--bad-bg); border-color: var(--bad-border); }
    .pill.nodata { background: var(--nodata-bg); border-color: var(--nodata-border); }
    .count-badge { background: var(--accent-soft); color: var(--accent); border-color: #cddcff; }
    .station-body {
      padding: 0 18px 18px;
      border-top: 1px solid var(--border);
      background: #fbfcfd;
    }
    .station-info {
      display: flex;
      flex-wrap: wrap;
      justify-content: space-between;
      gap: 10px 16px;
      padding: 14px 0 8px;
      color: var(--muted);
      font-size: 0.95rem;
    }
    .section-card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 14px;
    }
    .settings { margin: 8px 0 16px; }
    .settings summary {
      padding: 0;
      background: transparent;
      border: none;
      box-shadow: none;
      display: inline-flex;
      justify-content: flex-start;
      gap: 8px;
      font-weight: 700;
      color: var(--accent);
    }
    .settings summary::-webkit-details-marker { display: none; }
    .settings-wrap { margin-top: 14px; display: grid; gap: 14px; }
    .fields {
      display: grid;
      gap: 12px;
      grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
    }
    .field { display: grid; gap: 6px; }
    .field span {
      color: var(--muted);
      font-size: 0.84rem;
      font-weight: 700;
      text-transform: uppercase;
      letter-spacing: 0.03em;
    }
    .field input, .field select {
      width: 100%;
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 10px 12px;
      background: #fff;
      font-size: 0.95rem;
      color: var(--text);
    }
    .probe-settings { display: grid; gap: 12px; }
    .probe-settings-card {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px;
      background: #fcfdff;
    }
    .probe-settings-title {
      margin: 0 0 10px;
      font-size: 1rem;
      font-weight: 800;
    }
    .settings-actions,
    .button-row {
      display: flex;
      justify-content: flex-end;
      align-items: center;
      gap: 12px;
      flex-wrap: wrap;
    }
    .save-msg {
      color: var(--muted);
      font-size: 0.92rem;
      min-height: 1.2em;
    }
    button {
      border: 0;
      border-radius: 12px;
      background: var(--accent);
      color: white;
      padding: 10px 14px;
      font-size: 0.95rem;
      font-weight: 700;
      cursor: pointer;
      line-height: 1.2;
    }
    button.secondary {
      background: #eef4ff;
      color: var(--accent);
      border: 1px solid #d5e2ff;
    }
    button.ghost {
      background: #fff;
      color: var(--text);
      border: 1px solid var(--border);
    }
    .probe-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
      gap: 14px;
      align-items: start;
    }
    .probe-card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 14px;
      display: grid;
      gap: 12px;
      align-self: start;
    }
    .probe-card.ok { border-color: var(--ok-border); background: linear-gradient(180deg, #ffffff 0%, #f7fcf9 100%); }
    .probe-card.warn { border-color: var(--warn-border); background: linear-gradient(180deg, #ffffff 0%, #fffaf0 100%); }
    .probe-card.bad { border-color: var(--bad-border); background: linear-gradient(180deg, #ffffff 0%, #fff5f5 100%); }
    .probe-card.nodata { border-color: var(--nodata-border); background: linear-gradient(180deg, #ffffff 0%, #f7f9fb 100%); }
    .probe-head {
      display: flex;
      justify-content: space-between;
      gap: 10px;
      align-items: start;
      flex-wrap: wrap;
    }
    .probe-name {
      margin: 0 0 4px;
      font-size: 1.12rem;
      font-weight: 800;
    }
    .probe-sub { color: var(--muted); font-size: 0.95rem; }
    .range-wrap {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      background: #f7f9fb;
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 8px 10px;
    }
    .range-wrap label {
      color: var(--muted);
      font-size: 0.88rem;
      font-weight: 700;
    }
    .range-wrap select {
      border: 0;
      background: transparent;
      font-size: 0.95rem;
      color: var(--text);
      outline: none;
    }
    .metrics {
      display: grid;
      grid-template-columns: repeat(3, minmax(0, 1fr));
      gap: 10px;
    }
    .metrics.two { grid-template-columns: repeat(2, minmax(0, 1fr)); }
    .metric {
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 12px;
      background: #fcfdff;
      min-width: 0;
    }
    .metric-label,
    .section-label {
      color: var(--muted);
      font-size: 0.80rem;
      margin-bottom: 6px;
      text-transform: uppercase;
      letter-spacing: 0.04em;
      font-weight: 800;
    }
    .metric-value {
      font-size: 1.18rem;
      font-weight: 800;
      line-height: 1.1;
    }
    .metric-note {
      margin-top: 4px;
      color: var(--muted);
      font-size: 0.82rem;
    }
    .plot-box {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 10px;
      background: #fbfcfe;
      min-height: 180px;
    }
    .plot-box img {
      width: 100%;
      display: block;
      border-radius: 10px;
    }
    .plot-controls {
      margin-top: 10px;
      display: flex;
      justify-content: space-between;
      align-items: center;
      gap: 10px;
      flex-wrap: wrap;
    }
    .plot-summary {
      color: var(--muted);
      font-size: 0.84rem;
    }
    .recent-table {
      width: 100%;
      border-collapse: collapse;
      font-size: 0.94rem;
    }
    .recent-table th,
    .recent-table td {
      text-align: left;
      padding: 10px 8px;
      border-bottom: 1px solid var(--border);
      vertical-align: top;
    }
    .recent-table th {
      color: var(--muted);
      font-size: 0.82rem;
      text-transform: uppercase;
      letter-spacing: 0.04em;
    }
    .recent-empty {
      color: var(--muted);
      font-size: 0.92rem;
    }
    .tech summary,
    .plot-section summary {
      padding: 0;
      background: transparent;
      border: none;
      box-shadow: none;
      font-weight: 700;
      color: var(--muted);
      display: inline-flex;
      gap: 8px;
      justify-content: flex-start;
      cursor: pointer;
    }
    .tech summary::-webkit-details-marker,
    .plot-section summary::-webkit-details-marker { display: none; }
    .tech-grid {
      margin-top: 10px;
      display: grid;
      gap: 10px;
      grid-template-columns: repeat(auto-fit, minmax(130px, 1fr));
    }
    .tech-item {
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 10px;
      background: #fcfdff;
    }
    .tiny {
      color: var(--muted);
      font-size: 0.82rem;
    }
    .segmented {
      display: inline-flex;
      border: 1px solid var(--border);
      border-radius: 12px;
      overflow: hidden;
      background: #fff;
    }
    .segmented button {
      border-radius: 0;
      border: 0;
      background: transparent;
      color: var(--muted);
      padding: 8px 12px;
    }
    .segmented button.active {
      background: var(--accent-soft);
      color: var(--accent);
    }

    .bench-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(330px, 1fr));
      gap: 14px;
      align-items: start;
    }
    .bench-card {
      border: 1px solid var(--border);
      border-radius: 20px;
      background: var(--panel);
      overflow: hidden;
      box-shadow: inset 0 1px 0 rgba(255,255,255,0.7);
      align-self: start;
    }
    .bench-card.ok { border-color: var(--ok-border); background: linear-gradient(180deg, #ffffff 0%, #f7fcf9 100%); }
    .bench-card.warn { border-color: var(--warn-border); background: linear-gradient(180deg, #ffffff 0%, #fffaf0 100%); }
    .bench-card.bad { border-color: var(--bad-border); background: linear-gradient(180deg, #ffffff 0%, #fff5f5 100%); }
    .bench-card.nodata { border-color: var(--nodata-border); background: linear-gradient(180deg, #ffffff 0%, #f7f9fb 100%); }
    .bench-card > summary {
      list-style: none;
      cursor: pointer;
      padding: 16px;
      display: grid;
      grid-template-columns: minmax(0, 1fr) auto;
      gap: 14px;
      align-items: center;
      background: transparent;
    }
    .bench-card > summary::-webkit-details-marker { display: none; }
    .bench-head {
      min-width: 0;
      display: grid;
      gap: 8px;
    }
    .bench-head-top {
      display: flex;
      gap: 10px;
      align-items: center;
      justify-content: space-between;
      flex-wrap: wrap;
    }
    .bench-title-wrap {
      min-width: 0;
      display: flex;
      align-items: center;
      gap: 10px;
      flex: 1;
    }
    .bench-title {
      font-size: 1.12rem;
      font-weight: 800;
      line-height: 1.15;
      min-width: 0;
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
    }
    .bench-sub {
      color: var(--muted);
      font-size: 0.92rem;
      line-height: 1.3;
    }
    .bench-kicker {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      align-items: center;
    }
    .mini-chip {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      padding: 6px 10px;
      border-radius: 999px;
      font-size: 0.82rem;
      font-weight: 700;
      color: var(--muted);
      background: rgba(255,255,255,0.78);
      border: 1px solid var(--border);
    }
    .bench-reading {
      min-width: 175px;
      text-align: right;
      display: grid;
      gap: 4px;
    }
    .bench-reading-value {
      font-size: 1.9rem;
      font-weight: 800;
      line-height: 0.96;
      letter-spacing: -0.03em;
    }
    .bench-reading-note {
      color: var(--muted);
      font-size: 0.84rem;
      line-height: 1.25;
    }
    .bench-body {
      padding: 0 16px 16px;
      border-top: 1px solid var(--border);
      background: rgba(255,255,255,0.35);
      display: grid;
      gap: 12px;
    }
    .bench-toolbar {
      display: flex;
      justify-content: space-between;
      gap: 12px;
      align-items: center;
      flex-wrap: wrap;
      padding-top: 12px;
    }
    .bench-updated {
      color: var(--muted);
      font-size: 0.86rem;
    }
    .hero-metrics {
      display: grid;
      grid-template-columns: repeat(2, minmax(0, 1fr));
      gap: 10px;
    }
    .detail-section {
      border: 1px solid var(--border);
      border-radius: 18px;
      background: rgba(255,255,255,0.86);
      overflow: hidden;
    }
    .detail-section > summary {
      list-style: none;
      cursor: pointer;
      padding: 12px 14px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      background: linear-gradient(180deg, rgba(255,255,255,0.92) 0%, rgba(248,250,252,0.95) 100%);
    }
    .detail-section > summary::-webkit-details-marker { display: none; }
    .detail-title {
      font-size: 0.95rem;
      font-weight: 800;
      color: var(--text);
    }
    .detail-sub {
      color: var(--muted);
      font-size: 0.82rem;
    }
    .detail-body {
      padding: 14px;
      border-top: 1px solid var(--border);
      display: grid;
      gap: 12px;
      background: rgba(255,255,255,0.5);
    }
    .temp-strip,
    .quality-grid,
    .voc-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
      gap: 10px;
    }
    .unit-pill,
    .quality-card {
      border: 1px solid var(--border);
      background: #fcfdff;
      border-radius: 14px;
      padding: 12px;
      min-width: 0;
    }
    .unit-pill strong,
    .quality-card .metric-value { display: block; }
    .ph-gauge-box {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px;
      background: #fbfcfe;
    }
    .ph-gauge {
      width: 100%;
      display: block;
    }
    .table-wrap {
      border: 1px solid var(--border);
      border-radius: 16px;
      background: #fcfdff;
      overflow: auto;
    }
    .empty-section {
      color: var(--muted);
      font-size: 0.92rem;
      padding: 12px;
    }

    @media (max-width: 900px) {
      .bench-grid { grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); }
      .bench-reading-value { font-size: 1.65rem; }
    }

    @media (max-width: 760px) {
      .wrap { padding: 14px; }
      h1 { font-size: 1.65rem; }
      .metrics, .metrics.two, .hero-metrics, .temp-strip, .quality-grid, .voc-grid { grid-template-columns: 1fr; }
      .station summary { padding: 14px; align-items: flex-start; }
      .summary-right { justify-content: flex-start; }
      .probe-grid, .bench-grid { grid-template-columns: 1fr; }
      .bench-card > summary { grid-template-columns: 1fr; }
      .bench-reading { text-align: left; min-width: 0; }
      .station-meta, .bench-sub { white-space: normal; }
      .global-note { max-width: none; }
      .recent-table { font-size: 0.88rem; }
      .button-row, .settings-actions { justify-content: flex-start; }
      .bench-title { white-space: normal; }
    }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="topbar">
      <div>
        <h1>Sensor Host</h1>
        <div class="subhead">Field stations refresh every 60 seconds · bench sensors refresh from cached background reads every 5 seconds</div>
      </div>
      <div class="global-note">Desktop stays lab-style and information rich. Collapsed cards stay compact, long sections toggle independently, graph range stays with the graph, and temperature unit controls only appear on the RTD card.</div>
    </div>

    <div id="bench-slot"></div>
    <div id="content" class="loading">Loading dashboard…</div>
  </div>

  <script>
    const DEFAULT_HOURS = __DEFAULT_HOURS__;
    const ALLOWED_WINDOWS = __ALLOWED_WINDOWS__;

    function escapeHtml(value) {
      return String(value ?? "")
        .replaceAll("&", "&amp;")
        .replaceAll("<", "&lt;")
        .replaceAll(">", "&gt;")
        .replaceAll('"', "&quot;")
        .replaceAll("'", "&#39;");
    }

    function isCompactView() {
      return window.innerWidth <= 760;
    }

    function fmtPct(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(1) + " %";
    }
    function fmtPH(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(2) + " pH";
    }
    function fmtVoltage(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(3) + " V";
    }
    function fmtTemp(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(2) + " °C";
    }
    function fmtTempF(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(2) + " °F";
    }
    function fmtTempK(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(2) + " K";
    }
    function fmtPPM(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(1) + " ppm";
    }
    function fmtPPB(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(0) + " ppb";
    }
    function fmtRaw(value) {
      if (value === null || value === undefined) return "—";
      const n = Number(value);
      if (!Number.isFinite(n) || n >= 65535) return "No reading";
      return n.toFixed(0);
    }
    function fmtRange(rules) {
      return `${Number(rules.target_low).toFixed(0)}%–${Number(rules.target_high).toFixed(0)}%`;
    }
    function formatWindow(hours) {
      if (Number(hours) === 1) return "1h";
      if (Number(hours) === 24) return "24h";
      return "7d";
    }
    function stateClass(state) {
      return state?.cls || "nodata";
    }
    function fmtDateTime(ts) {
      if (!ts) return "—";
      try {
        const d = new Date(ts);
        if (Number.isNaN(d.getTime())) return ts;
        return d.toLocaleString();
      } catch {
        return ts;
      }
    }
    function clamp(n, min, max) {
      return Math.max(min, Math.min(max, n));
    }
    function polar(cx, cy, r, deg) {
      const rad = (deg - 90) * Math.PI / 180;
      return { x: cx + r * Math.cos(rad), y: cy + r * Math.sin(rad) };
    }
    function arcPath(cx, cy, r, startDeg, endDeg) {
      const start = polar(cx, cy, r, endDeg);
      const end = polar(cx, cy, r, startDeg);
      const large = Math.abs(endDeg - startDeg) > 180 ? 1 : 0;
      return `M ${start.x} ${start.y} A ${r} ${r} 0 ${large} 0 ${end.x} ${end.y}`;
    }
    function renderPhGauge(ph) {
      const value = Number(ph);
      if (!Number.isFinite(value)) return `<div class="empty-section">No live pH gauge yet.</div>`;
      const clamped = clamp(value, 0, 14);
      const angle = -140 + (clamped / 14) * 280;
      const needle = polar(90, 92, 58, angle);
      return `
        <div class="ph-gauge-box">
          <svg viewBox="0 0 180 120" class="ph-gauge" aria-label="pH gauge">
            <path d="${arcPath(90, 92, 58, -140, -20)}" stroke="#e3b454" stroke-width="12" fill="none" stroke-linecap="round"></path>
            <path d="${arcPath(90, 92, 58, -20, 20)}" stroke="#8ac89d" stroke-width="12" fill="none" stroke-linecap="round"></path>
            <path d="${arcPath(90, 92, 58, 20, 140)}" stroke="#7fb0ff" stroke-width="12" fill="none" stroke-linecap="round"></path>
            <line x1="90" y1="92" x2="${needle.x}" y2="${needle.y}" stroke="#16202a" stroke-width="4" stroke-linecap="round"></line>
            <circle cx="90" cy="92" r="6" fill="#16202a"></circle>
            <text x="20" y="112" font-size="11" fill="#667281">Acidic</text>
            <text x="84" y="18" font-size="11" fill="#667281">7</text>
            <text x="128" y="112" font-size="11" fill="#667281">Basic</text>
          </svg>
          <div class="metric-note">0–6.99 acidic · 7 neutral · 7.01–14 basic</div>
        </div>
      `;
    }

    function loadExpandedState(stationId, fallbackCollapsed) {
      const key = `station-open:${stationId}`;
      const saved = localStorage.getItem(key);
      if (saved !== null) return saved === "1";
      return !fallbackCollapsed;
    }
    function saveExpandedState(stationId, open) {
      localStorage.setItem(`station-open:${stationId}`, open ? "1" : "0");
    }
    function getProbeHours(stationId, probeKey, fallback) {
      const key = `probe-hours:${stationId}:${probeKey}`;
      const saved = Number(localStorage.getItem(key));
      if (ALLOWED_WINDOWS.includes(saved)) return saved;
      return fallback;
    }
    function setProbeHours(stationId, probeKey, hours) {
      localStorage.setItem(`probe-hours:${stationId}:${probeKey}`, String(hours));
    }
    function getBenchHours(kind, fallback = 24) {
      const key = `bench-hours:${kind}`;
      const saved = Number(localStorage.getItem(key));
      if (ALLOWED_WINDOWS.includes(saved)) return saved;
      return fallback;
    }
    function setBenchHours(kind, hours) {
      localStorage.setItem(`bench-hours:${kind}`, String(hours));
    }
    function getBenchCardOpen(kind) {
      const key = `bench-card-open:${kind}`;
      const saved = localStorage.getItem(key);
      if (saved !== null) return saved === "1";
      return !isCompactView();
    }
    function setBenchCardOpen(kind, open) {
      localStorage.setItem(`bench-card-open:${kind}`, open ? "1" : "0");
    }
    function getBenchSectionOpen(kind, section, fallback) {
      const key = `bench-section-open:${kind}:${section}`;
      const saved = localStorage.getItem(key);
      if (saved !== null) return saved === "1";
      return fallback;
    }
    function setBenchSectionOpen(kind, section, open) {
      localStorage.setItem(`bench-section-open:${kind}:${section}`, open ? "1" : "0");
    }
    function getTempPrimaryUnit() {
      const saved = localStorage.getItem("temp-primary-unit");
      if (saved === "f" || saved === "c") return saved;
      return isCompactView() ? "f" : "c";
    }
    function setTempPrimaryUnit(unit) {
      localStorage.setItem("temp-primary-unit", unit);
    }

    function renderProbeSettings(station) {
      return station.probes.map((probe) => `
        <div class="probe-settings-card">
          <div class="probe-settings-title">${escapeHtml(probe.display_name || probe.probe_key)}</div>
          <div class="fields">
            <label class="field">
              <span>Probe name</span>
              <input type="text" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="display_name" value="${escapeHtml(probe.display_name)}">
            </label>
            <label class="field">
              <span>Location / note</span>
              <input type="text" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="location_name" value="${escapeHtml(probe.location_name || "")}">
            </label>
            <label class="field">
              <span>Danger low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="danger_low" value="${escapeHtml(probe.rules.danger_low)}">
            </label>
            <label class="field">
              <span>Warn low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="warn_low" value="${escapeHtml(probe.rules.warn_low)}">
            </label>
            <label class="field">
              <span>Target low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="target_low" value="${escapeHtml(probe.rules.target_low)}">
            </label>
            <label class="field">
              <span>Target high</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="target_high" value="${escapeHtml(probe.rules.target_high)}">
            </label>
            <label class="field">
              <span>Warn high</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="warn_high" value="${escapeHtml(probe.rules.warn_high)}">
            </label>
            <label class="field">
              <span>Enabled</span>
              <select data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="enabled">
                <option value="true" ${probe.enabled ? "selected" : ""}>Visible</option>
                <option value="false" ${probe.enabled ? "" : "selected"}>Hidden</option>
              </select>
            </label>
          </div>
        </div>
      `).join("");
    }

    function renderProbeCard(station, probe) {
      const hours = getProbeHours(station.station_id, probe.probe_key, station.default_hours || DEFAULT_HOURS);
      return `
        <div class="probe-card ${escapeHtml(stateClass(probe.state))}" data-station-id="${escapeHtml(station.station_id)}" data-probe-key="${escapeHtml(probe.probe_key)}">
          <div class="probe-head">
            <div>
              <h3 class="probe-name">${escapeHtml(probe.display_name)}</h3>
              <div class="probe-sub">${escapeHtml(probe.location_name || "No location label yet")} · target ${escapeHtml(fmtRange(probe.rules))}</div>
            </div>
            <div class="pill ${escapeHtml(stateClass(probe.state))}">${escapeHtml(probe.state?.text || "No data")}</div>
          </div>

          <div class="metrics">
            <div class="metric">
              <div class="metric-label">Current</div>
              <div class="metric-value">${escapeHtml(fmtPct(probe.current))}</div>
              <div class="metric-note">Live reading</div>
            </div>
            <div class="metric">
              <div class="metric-label">Average</div>
              <div class="metric-value js-avg">Loading…</div>
              <div class="metric-note js-window-label">Window ${escapeHtml(formatWindow(hours))}</div>
            </div>
            <div class="metric">
              <div class="metric-label">Target band</div>
              <div class="metric-value">${escapeHtml(fmtRange(probe.rules))}</div>
              <div class="metric-note">Editable in settings</div>
            </div>
          </div>

          <div class="plot-box">
            <img class="probe-plot" alt="Graph for ${escapeHtml(probe.display_name)}">
            <div class="plot-controls">
              <div class="plot-summary">Window for the historical graph only.</div>
              <div class="range-wrap">
                <label>Window</label>
                <select class="probe-range">
                  <option value="1" ${hours === 1 ? "selected" : ""}>Last 1 hour</option>
                  <option value="24" ${hours === 24 ? "selected" : ""}>Last 24 hours</option>
                  <option value="168" ${hours === 168 ? "selected" : ""}>Last 7 days</option>
                </select>
              </div>
            </div>
          </div>

          <details class="tech">
            <summary>Technical data</summary>
            <div class="tech-grid">
              <div class="tech-item"><div class="tiny">Raw</div><div><strong>${escapeHtml(fmtRaw(probe.raw))}</strong></div></div>
              <div class="tech-item"><div class="tiny">Valid points</div><div><strong class="js-points">Loading…</strong></div></div>
              <div class="tech-item"><div class="tiny">Minimum</div><div><strong class="js-min">Loading…</strong></div></div>
              <div class="tech-item"><div class="tiny">Maximum</div><div><strong class="js-max">Loading…</strong></div></div>
            </div>
          </details>
        </div>
      `;
    }

    function renderStation(station) {
      const open = loadExpandedState(station.station_id, station.is_collapsed);
      const shownProbes = station.probes.filter(p => p.enabled);
      return `
        <details class="station" data-station-id="${escapeHtml(station.station_id)}" ${open ? "open" : ""}>
          <summary>
            <div class="summary-left">
              <span class="status-dot ${escapeHtml(station.connectivity.state)}"></span>
              <div class="summary-text">
                <div class="station-name">${escapeHtml(station.display_name)}</div>
                <div class="station-meta">${escapeHtml(station.description || "No unit description")} · ${escapeHtml(station.connectivity.label)} · updated ${escapeHtml(station.updated_ago)}</div>
              </div>
            </div>
            <div class="summary-right">
              <div class="pill ${escapeHtml(stateClass(station.station_state))}">${escapeHtml(station.station_state.text)}</div>
              <div class="pill count-badge">${shownProbes.length} probes${station.alert_count ? ` · ${station.alert_count} alert${station.alert_count > 1 ? "s" : ""}` : ""}</div>
            </div>
          </summary>
          <div class="station-body">
            <div class="station-info">
              <div><strong>Station ID:</strong> ${escapeHtml(station.station_id)}</div>
              <div><strong>Updated:</strong> ${escapeHtml(station.updated_at)}</div>
            </div>

            <details class="settings section-card">
              <summary>Edit names and thresholds</summary>
              <div class="settings-wrap" data-config-station="${escapeHtml(station.station_id)}">
                <div class="fields">
                  <label class="field"><span>Unit name</span><input type="text" data-station-field="display_name" value="${escapeHtml(station.display_name)}"></label>
                  <label class="field"><span>Unit description</span><input type="text" data-station-field="description" value="${escapeHtml(station.description || "")}"></label>
                  <label class="field"><span>Default graph range</span>
                    <select data-station-field="default_hours">
                      <option value="1" ${Number(station.default_hours) === 1 ? "selected" : ""}>Last 1 hour</option>
                      <option value="24" ${Number(station.default_hours) === 24 ? "selected" : ""}>Last 24 hours</option>
                      <option value="168" ${Number(station.default_hours) === 168 ? "selected" : ""}>Last 7 days</option>
                    </select>
                  </label>
                  <label class="field"><span>Collapsed by default</span>
                    <select data-station-field="is_collapsed">
                      <option value="false" ${station.is_collapsed ? "" : "selected"}>Expanded</option>
                      <option value="true" ${station.is_collapsed ? "selected" : ""}>Collapsed</option>
                    </select>
                  </label>
                </div>

                <div class="probe-settings">${renderProbeSettings(station)}</div>

                <div class="settings-actions">
                  <div class="save-msg" data-save-msg="${escapeHtml(station.station_id)}"></div>
                  <button type="button" data-save-station="${escapeHtml(station.station_id)}">Save settings</button>
                </div>
              </div>
            </details>

            <div class="probe-grid">${shownProbes.map(probe => renderProbeCard(station, probe)).join("")}</div>
          </div>
        </details>
      `;
    }

    async function refreshProbeCard(card) {
      const stationId = card.dataset.stationId;
      const probeKey = card.dataset.probeKey;
      const hours = Number(card.querySelector(".probe-range").value || DEFAULT_HOURS);
      setProbeHours(stationId, probeKey, hours);

      const data = await safeFetchJson(`/api/probe-metrics/${encodeURIComponent(stationId)}/${encodeURIComponent(probeKey)}?hours=${hours}`);
      card.querySelector(".js-avg").textContent = data.avg === null ? "—" : fmtPct(data.avg);
      card.querySelector(".js-window-label").textContent = `Window ${formatWindow(hours)}`;
      card.querySelector(".js-points").textContent = String(Number(data.points || 0));
      card.querySelector(".js-min").textContent = data.min === null ? "—" : fmtPct(data.min);
      card.querySelector(".js-max").textContent = data.max === null ? "—" : fmtPct(data.max);
      card.querySelector(".probe-plot").src = `/plot/${encodeURIComponent(stationId)}/${encodeURIComponent(probeKey)}.svg?hours=${hours}&_=${Date.now()}`;
    }

    function gatherStationPayload(stationId) {
      const root = document.querySelector(`[data-config-station="${CSS.escape(stationId)}"]`);
      const station = {};
      root.querySelectorAll("[data-station-field]").forEach(el => {
        const field = el.dataset.stationField;
        let value = el.value;
        if (field === "default_hours") value = Number(value);
        if (field === "is_collapsed") value = value === "true";
        station[field] = value;
      });

      const probes = {};
      root.querySelectorAll("[data-probe-key]").forEach(el => {
        const probeKey = el.dataset.probeKey;
        const field = el.dataset.probeField;
        if (!probes[probeKey]) probes[probeKey] = {};
        let value = el.value;
        if (["danger_low", "warn_low", "target_low", "target_high", "warn_high"].includes(field)) value = Number(value);
        if (field === "enabled") value = value === "true";
        probes[probeKey][field] = value;
      });
      return { station, probes };
    }

    async function saveStationConfig(stationId) {
      const msg = document.querySelector(`[data-save-msg="${CSS.escape(stationId)}"]`);
      msg.textContent = "Saving…";
      const payload = gatherStationPayload(stationId);
      const res = await fetch(`/api/config/${encodeURIComponent(stationId)}`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload)
      });
      const data = await res.json();
      if (!res.ok) {
        msg.textContent = data.error || "Save failed";
        return;
      }
      msg.textContent = "Saved";
      await loadDashboard();
    }

    async function safeFetchJson(url, timeoutMs = 6000, fetchOptions = {}) {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(), timeoutMs);
      try {
        const res = await fetch(url, { cache: "no-store", ...fetchOptions, signal: controller.signal });
        const text = await res.text();
        const data = text ? JSON.parse(text) : {};
        if (!res.ok) throw new Error(data.error || `HTTP ${res.status}`);
        return data;
      } finally {
        clearTimeout(timer);
      }
    }

    function benchCardConfig(kind) {
      return {
        ph: {
          title: "Bench pH Probe",
          subtitle: "Atlas Surveyor through ADS1115 A0",
          heroLabel: "pH",
          live: "/api/ph-live",
          metrics: "/api/ph-metrics",
          recent: "/api/ph-recent?limit=25",
          reset: "/api/ph-reset",
          toggle: "/api/ph-collect-enabled",
          cal: "/api/ph-calibration",
          plot: "/plot/ph.svg",
          mainValue: (live) => fmtPH(live.ph),
          mainNote: (live) => live.collecting_enabled === false ? "Logging paused" : (live.voltage === null ? "Voltage —" : `Voltage ${fmtVoltage(live.voltage)}`),
          currentMetric: (live) => fmtPH(live.ph),
          averageMetric: (metrics) => metrics.avg === null ? "—" : fmtPH(metrics.avg),
          minMetric: (metrics) => metrics.min === null ? "—" : fmtPH(metrics.min),
          maxMetric: (metrics) => metrics.max === null ? "—" : fmtPH(metrics.max),
          recentValue: (row) => fmtPH(row.ph),
          recentAux: (row) => fmtVoltage(row.voltage)
        },
        temp: {
          title: "Bench Temperature Probe",
          subtitle: "Atlas EZO RTD on UART",
          heroLabel: "RTD",
          live: "/api/temp-live",
          metrics: "/api/temp-metrics",
          recent: "/api/temp-recent?limit=25",
          reset: "/api/temp-reset",
          plot: "/plot/temp.svg",
          mainValue: (live) => formatTempPrimary(live),
          mainNote: (live) => `${fmtTempF(live.temp_f)} · ${fmtTempK(live.temp_k)}`,
          currentMetric: (live) => formatTempPrimary(live),
          averageMetric: (metrics) => formatTempPrimary(metrics, true),
          minMetric: (metrics) => metrics.min === null ? "—" : fmtTemp(metrics.min),
          maxMetric: (metrics) => metrics.max === null ? "—" : fmtTemp(metrics.max),
          recentValue: (row) => fmtTemp(row.temp_c),
          recentAux: () => "RTD"
        },
        tds: {
          title: "Bench TDS Probe",
          subtitle: "Inland TDS meter through ADS1115 A1",
          heroLabel: "TDS",
          live: "/api/tds-live",
          metrics: "/api/tds-metrics",
          recent: "/api/tds-recent?limit=25",
          reset: "/api/tds-reset",
          plot: "/plot/tds.svg",
          mainValue: (live) => fmtPPM(live.tds_ppm),
          mainNote: (live) => `${fmtVoltage(live.voltage)} · comp ${fmtTemp(live.comp_temp_c)}`,
          currentMetric: (live) => fmtPPM(live.tds_ppm),
          averageMetric: (metrics) => metrics.avg === null ? "—" : fmtPPM(metrics.avg),
          minMetric: (metrics) => metrics.min === null ? "—" : fmtPPM(metrics.min),
          maxMetric: (metrics) => metrics.max === null ? "—" : fmtPPM(metrics.max),
          recentValue: (row) => fmtPPM(row.tds_ppm),
          recentAux: (row) => `${fmtVoltage(row.voltage)} · ${fmtTemp(row.comp_temp_c)}`
        },
        voc: {
          title: "Bench VOC / eCO₂",
          subtitle: "Adafruit SGP30 on I²C",
          heroLabel: "Air quality",
          live: "/api/voc-live",
          metrics: "/api/voc-metrics",
          recent: "/api/voc-recent?limit=25",
          reset: "/api/voc-reset",
          plot: "/plot/voc_eco2.svg",
          plot2: "/plot/voc_tvoc.svg",
          mainValue: (live) => fmtPPM(live.eco2_ppm),
          mainNote: (live) => `TVOC ${fmtPPB(live.tvoc_ppb)}`,
          currentMetric: (live) => fmtPPM(live.eco2_ppm),
          averageMetric: (metrics) => metrics.avg_eco2 === null ? "—" : fmtPPM(metrics.avg_eco2),
          minMetric: (metrics) => metrics.min_eco2 === null ? "—" : fmtPPM(metrics.min_eco2),
          maxMetric: (metrics) => metrics.max_eco2 === null ? "—" : fmtPPM(metrics.max_eco2),
          recentValue: (row) => `${fmtPPM(row.eco2_ppm)} · ${fmtPPB(row.tvoc_ppb)}`,
          recentAux: () => "eCO₂ · TVOC"
        }
      }[kind];
    }

    function renderDetailSection(kind, sectionKey, title, subtitle, bodyHtml, defaultOpen) {
      const open = getBenchSectionOpen(kind, sectionKey, defaultOpen);
      return `
        <details class="detail-section" data-kind="${escapeHtml(kind)}" data-section="${escapeHtml(sectionKey)}" ${open ? "open" : ""}>
          <summary>
            <div>
              <div class="detail-title">${escapeHtml(title)}</div>
              <div class="detail-sub">${escapeHtml(subtitle)}</div>
            </div>
            <div class="mini-chip">Toggle</div>
          </summary>
          <div class="detail-body">${bodyHtml}</div>
        </details>
      `;
    }

    function renderBenchSensorCard(kind) {
      const cfg = benchCardConfig(kind);
      const open = getBenchCardOpen(kind);
      const hours = getBenchHours(kind, 24);
      const graphDefault = !isCompactView();
      const recentDefault = false;
      const controlsDefault = kind === "ph" && !isCompactView();

      const unitToggle = kind === "temp" ? `
        <div class="segmented js-temp-unit-toggle">
          <button type="button" data-temp-unit="c">°C main</button>
          <button type="button" data-temp-unit="f">°F main</button>
        </div>
      ` : "";

      const heroExtras = kind === "temp" ? `
        <div class="temp-strip">
          <div class="unit-pill"><span class="tiny">Current °C</span><strong class="js-temp-c">—</strong></div>
          <div class="unit-pill"><span class="tiny">Current °F</span><strong class="js-temp-f">—</strong></div>
          <div class="unit-pill"><span class="tiny">Current K</span><strong class="js-temp-k">—</strong></div>
        </div>
      ` : kind === "ph" ? `
        <div class="js-ph-gauge-wrap"><div class="js-ph-gauge"></div></div>
      ` : kind === "voc" ? `
        <div class="voc-grid">
          <div class="quality-card"><div class="metric-label">Current eCO₂</div><div class="metric-value js-voc-current-eco2">—</div><div class="metric-note">Equivalent CO₂</div></div>
          <div class="quality-card"><div class="metric-label">Current TVOC</div><div class="metric-value js-voc-current-tvoc">—</div><div class="metric-note">Total VOC</div></div>
          <div class="quality-card"><div class="metric-label">Average eCO₂</div><div class="metric-value js-voc-avg-eco2">—</div><div class="metric-note js-voc-window">Window ${formatWindow(hours)}</div></div>
          <div class="quality-card"><div class="metric-label">Average TVOC</div><div class="metric-value js-voc-avg-tvoc">—</div><div class="metric-note">Rolling history</div></div>
        </div>
      ` : "";

      const graphSection = renderDetailSection(kind, "graph", "History graph", "Time window only affects the graph below.", `
        <div class="plot-box">
          <img class="js-bench-plot" data-kind="${escapeHtml(kind)}" alt="${escapeHtml(cfg.title)} graph">
          <div class="plot-controls">
            <div class="plot-summary">Choose how much history to visualize.</div>
            <div class="range-wrap">
              <label>Window</label>
              <select class="js-bench-range" data-kind="${escapeHtml(kind)}">
                <option value="1" ${hours === 1 ? "selected" : ""}>Last 1 hour</option>
                <option value="24" ${hours === 24 ? "selected" : ""}>Last 24 hours</option>
                <option value="168" ${hours === 168 ? "selected" : ""}>Last 7 days</option>
              </select>
            </div>
          </div>
        </div>
        ${kind === "voc" ? `<div class="plot-box"><img class="js-bench-plot-2" data-kind="${escapeHtml(kind)}" alt="${escapeHtml(cfg.title)} secondary graph"></div>` : ""}
      `, graphDefault);

      const recentSection = renderDetailSection(kind, "recent", "Recent logged changes", "Collapse this when you want a clean dashboard.", `
        <div class="table-wrap">
          <div class="empty-section js-bench-recent-empty" data-kind="${escapeHtml(kind)}">Loading…</div>
          <table class="recent-table js-bench-recent-table" data-kind="${escapeHtml(kind)}" hidden>
            <thead><tr><th>Time</th><th>Value</th><th>Aux</th></tr></thead>
            <tbody class="js-bench-recent-body" data-kind="${escapeHtml(kind)}"></tbody>
          </table>
        </div>
      `, recentDefault);

      const controlsSection = renderDetailSection(kind, "controls", "Lab controls and quality", "Calibration, history reset, and data quality live here.", `
        <div class="button-row">
          ${kind === "ph" ? '<button type="button" class="ghost js-bench-toggle-ph">Pause pH</button>' : ''}
          ${kind === "ph" ? '<button type="button" class="ghost js-ph-cal-btn">Trim pH…</button>' : ''}
          ${kind === "ph" ? '<button type="button" class="ghost js-ph-cal-reset">Reset cal</button>' : ''}
          <button type="button" class="secondary js-bench-reset" data-kind="${escapeHtml(kind)}">Reset history</button>
          <div class="save-msg js-bench-error" data-kind="${escapeHtml(kind)}"></div>
        </div>
        <div class="quality-grid">
          <div class="quality-card"><div class="tiny">Samples / read</div><div class="metric-value js-bench-samples" data-kind="${escapeHtml(kind)}">—</div></div>
          <div class="quality-card"><div class="tiny">Valid points</div><div class="metric-value js-bench-points" data-kind="${escapeHtml(kind)}">—</div></div>
          <div class="quality-card"><div class="tiny">Minimum</div><div class="metric-value js-bench-min" data-kind="${escapeHtml(kind)}">—</div></div>
          <div class="quality-card"><div class="tiny">Maximum</div><div class="metric-value js-bench-max" data-kind="${escapeHtml(kind)}">—</div></div>
          <div class="quality-card"><div class="tiny">Quality</div><div class="metric-value js-bench-quality" data-kind="${escapeHtml(kind)}">—</div></div>
          <div class="quality-card"><div class="tiny">Calibration</div><div class="metric-value js-ph-cal-summary" data-kind="${escapeHtml(kind)}">—</div></div>
        </div>
      `, controlsDefault);

      return `
        <details class="bench-card nodata js-bench-card" data-kind="${escapeHtml(kind)}" ${open ? "open" : ""}>
          <summary>
            <div class="bench-head">
              <div class="bench-head-top">
                <div class="bench-title-wrap">
                  <span class="status-dot offline js-bench-dot" data-kind="${escapeHtml(kind)}"></span>
                  <div class="bench-title">${escapeHtml(cfg.title)}</div>
                </div>
                <div class="pill nodata js-bench-state" data-kind="${escapeHtml(kind)}">Starting…</div>
              </div>
              <div class="bench-sub">${escapeHtml(cfg.subtitle)}</div>
              <div class="bench-kicker">
                <div class="mini-chip">${escapeHtml(cfg.heroLabel)}</div>
                <div class="mini-chip js-bench-updated" data-kind="${escapeHtml(kind)}">Waiting for first sample…</div>
              </div>
            </div>
            <div class="bench-reading">
              <div class="bench-reading-value js-bench-summary-value" data-kind="${escapeHtml(kind)}">Loading…</div>
              <div class="bench-reading-note js-bench-summary-note" data-kind="${escapeHtml(kind)}">Waiting for first sample…</div>
            </div>
          </summary>

          <div class="bench-body">
            <div class="bench-toolbar">
              ${unitToggle}
            </div>

            <div class="hero-metrics">
              <div class="metric">
                <div class="metric-label">Current</div>
                <div class="metric-value js-bench-current" data-kind="${escapeHtml(kind)}">Loading…</div>
                <div class="metric-note js-bench-secondary" data-kind="${escapeHtml(kind)}">—</div>
              </div>
              <div class="metric">
                <div class="metric-label">Average</div>
                <div class="metric-value js-bench-avg" data-kind="${escapeHtml(kind)}">Loading…</div>
                <div class="metric-note js-bench-window" data-kind="${escapeHtml(kind)}">Window ${formatWindow(hours)}</div>
              </div>
            </div>

            ${heroExtras}
            ${graphSection}
            ${recentSection}
            ${controlsSection}
          </div>
        </details>
      `;
    }

    function renderBenchPanel() {
      const open = loadExpandedState("bench_suite", false);
      return `
        <details class="station" data-station-id="bench_suite" ${open ? "open" : ""}>
          <summary>
            <div class="summary-left">
              <span class="status-dot online"></span>
              <div class="summary-text">
                <div class="station-name">Bench Sensors</div>
                <div class="station-meta">Card collapse controls the full sensor. Graphs, tables, and controls each have their own toggles so the layout stays compact when you want a dashboard view.</div>
              </div>
            </div>
            <div class="summary-right"><div class="pill count-badge">Bench module</div></div>
          </summary>
          <div class="station-body">
            <div class="bench-grid">
              ${renderBenchSensorCard("ph")}
              ${renderBenchSensorCard("temp")}
              ${renderBenchSensorCard("tds")}
              ${renderBenchSensorCard("voc")}
            </div>
          </div>
        </details>
      `;
    }

    function setBenchUnavailable(kind, message) {
      const card = document.querySelector(`.js-bench-card[data-kind="${CSS.escape(kind)}"]`);
      if (!card) return;
      card.classList.remove("ok", "warn", "bad", "nodata");
      card.classList.add("nodata");
      const dot = card.querySelector(`.js-bench-dot[data-kind="${CSS.escape(kind)}"]`);
      if (dot) dot.className = "status-dot offline js-bench-dot";
      const state = card.querySelector(`.js-bench-state[data-kind="${CSS.escape(kind)}"]`);
      if (state) {
        state.className = "pill nodata js-bench-state";
        state.textContent = "Unavailable";
      }
      const err = card.querySelector(`.js-bench-error[data-kind="${CSS.escape(kind)}"]`);
      if (err) err.textContent = message || "";
    }

    function updateTempUnitButtons(root = document) {
      const active = getTempPrimaryUnit();
      root.querySelectorAll("[data-temp-unit]").forEach(btn => {
        btn.classList.toggle("active", btn.dataset.tempUnit === active);
      });
    }

    function formatTempPrimary(liveOrMetrics, useAvg = false) {
      const unit = getTempPrimaryUnit();
      const c = useAvg ? liveOrMetrics.avg : liveOrMetrics.temp_c;
      const f = useAvg ? liveOrMetrics.avg_f : liveOrMetrics.temp_f;
      return unit === "f" ? fmtTempF(f) : fmtTemp(c);
    }

    async function refreshBenchCard(kind, full = false) {
      const cfg = benchCardConfig(kind);
      const live = await safeFetchJson(cfg.live);
      const card = document.querySelector(`.js-bench-card[data-kind="${CSS.escape(kind)}"]`);
      if (!card) return;

      const cls = stateClass(live.state);
      card.classList.remove("ok", "warn", "bad", "nodata");
      card.classList.add(cls);

      const dot = card.querySelector(`.js-bench-dot[data-kind="${CSS.escape(kind)}"]`);
      if (dot) dot.className = `status-dot ${live.ok ? "online" : "offline"} js-bench-dot`;

      const state = card.querySelector(`.js-bench-state[data-kind="${CSS.escape(kind)}"]`);
      if (state) {
        state.className = `pill ${cls} js-bench-state`;
        state.textContent = live.state?.text || "Unavailable";
      }

      const mainValue = cfg.mainValue(live);
      const mainNote = cfg.mainNote(live);
      card.querySelector(`.js-bench-summary-value[data-kind="${CSS.escape(kind)}"]`).textContent = mainValue;
      card.querySelector(`.js-bench-summary-note[data-kind="${CSS.escape(kind)}"]`).textContent = mainNote;
      card.querySelector(`.js-bench-current[data-kind="${CSS.escape(kind)}"]`).textContent = cfg.currentMetric(live);
      card.querySelector(`.js-bench-secondary[data-kind="${CSS.escape(kind)}"]`).textContent = mainNote;
      card.querySelector(`.js-bench-updated[data-kind="${CSS.escape(kind)}"]`).textContent = live.updated_at ? `Updated ${fmtDateTime(live.updated_at)}` : "Waiting for first sample…";

      const err = card.querySelector(`.js-bench-error[data-kind="${CSS.escape(kind)}"]`);
      if (err) err.textContent = live.error || "";

      if (kind === "temp") {
        card.querySelector(".js-temp-c").textContent = fmtTemp(live.temp_c);
        card.querySelector(".js-temp-f").textContent = fmtTempF(live.temp_f);
        card.querySelector(".js-temp-k").textContent = fmtTempK(live.temp_k);
        updateTempUnitButtons(card);
      }

      if (kind === "ph") {
        card.querySelector(".js-ph-gauge").innerHTML = renderPhGauge(live.ph);
        const btn = card.querySelector(".js-bench-toggle-ph");
        if (btn) btn.textContent = live.collecting_enabled === false ? "Resume pH" : "Pause pH";
        const cal = live.calibration || {};
        let calText = cal.mode || "factory";
        if (cal.last_target !== null && cal.last_target !== undefined && !Number.isNaN(Number(cal.last_target))) {
          calText += ` · target ${Number(cal.last_target).toFixed(2)}`;
        }
        if (cal.last_ts) calText += ` · ${fmtDateTime(cal.last_ts)}`;
        card.querySelector(`.js-ph-cal-summary[data-kind="${CSS.escape(kind)}"]`).textContent = calText;
      } else if (kind === "voc") {
        card.querySelector(`.js-ph-cal-summary[data-kind="${CSS.escape(kind)}"]`).textContent = live.baseline_ready ? "Baseline learned" : "Warm-up";
        card.querySelector(".js-voc-current-eco2").textContent = fmtPPM(live.eco2_ppm);
        card.querySelector(".js-voc-current-tvoc").textContent = fmtPPB(live.tvoc_ppb);
      } else if (kind === "temp") {
        card.querySelector(`.js-ph-cal-summary[data-kind="${CSS.escape(kind)}"]`).textContent = "RTD direct";
      } else {
        card.querySelector(`.js-ph-cal-summary[data-kind="${CSS.escape(kind)}"]`).textContent = "No trim applied";
      }

      if (!full) return;

      const hours = getBenchHours(kind, 24);
      const metrics = await safeFetchJson(`${cfg.metrics}?hours=${hours}`);
      card.querySelector(`.js-bench-avg[data-kind="${CSS.escape(kind)}"]`).textContent = cfg.averageMetric(metrics);
      card.querySelector(`.js-bench-window[data-kind="${CSS.escape(kind)}"]`).textContent = `Window ${formatWindow(hours)}`;
      card.querySelector(`.js-bench-samples[data-kind="${CSS.escape(kind)}"]`).textContent = String(Number(live.samples || 0));
      card.querySelector(`.js-bench-points[data-kind="${CSS.escape(kind)}"]`).textContent = String(Number(metrics.points || 0));
      card.querySelector(`.js-bench-min[data-kind="${CSS.escape(kind)}"]`).textContent = cfg.minMetric(metrics);
      card.querySelector(`.js-bench-max[data-kind="${CSS.escape(kind)}"]`).textContent = cfg.maxMetric(metrics);
      card.querySelector(`.js-bench-quality[data-kind="${CSS.escape(kind)}"]`).textContent = live.quality || "—";

      if (kind === "voc") {
        card.querySelector(".js-voc-avg-eco2").textContent = metrics.avg_eco2 === null ? "—" : fmtPPM(metrics.avg_eco2);
        card.querySelector(".js-voc-avg-tvoc").textContent = metrics.avg_tvoc === null ? "—" : fmtPPB(metrics.avg_tvoc);
        card.querySelector(".js-voc-window").textContent = `Window ${formatWindow(hours)}`;
      }

      const graphSection = card.querySelector(`.detail-section[data-kind="${CSS.escape(kind)}"][data-section="graph"]`);
      const plot = card.querySelector(`.js-bench-plot[data-kind="${CSS.escape(kind)}"]`);
      if (cfg.plot && plot && graphSection && graphSection.open) {
        plot.src = `${cfg.plot}?hours=${hours}&_=${Date.now()}`;
      }
      if (kind === "voc") {
        const plot2 = card.querySelector(`.js-bench-plot-2[data-kind="${CSS.escape(kind)}"]`);
        if (cfg.plot2 && plot2 && graphSection && graphSection.open) {
          plot2.src = `${cfg.plot2}?hours=${hours}&_=${Date.now()}`;
        }
      }

      const recentSection = card.querySelector(`.detail-section[data-kind="${CSS.escape(kind)}"][data-section="recent"]`);
      if (recentSection && recentSection.open) {
        const recent = await safeFetchJson(cfg.recent);
        const empty = card.querySelector(`.js-bench-recent-empty[data-kind="${CSS.escape(kind)}"]`);
        const table = card.querySelector(`.js-bench-recent-table[data-kind="${CSS.escape(kind)}"]`);
        const body = card.querySelector(`.js-bench-recent-body[data-kind="${CSS.escape(kind)}"]`);
        if (!recent.length) {
          empty.hidden = false;
          table.hidden = true;
          empty.textContent = "No logged changes yet.";
        } else {
          empty.hidden = true;
          table.hidden = false;
          body.innerHTML = recent.map(row => `
            <tr>
              <td>${escapeHtml(fmtDateTime(row.ts))}</td>
              <td>${escapeHtml(cfg.recentValue(row))}</td>
              <td>${escapeHtml(cfg.recentAux(row))}</td>
            </tr>
          `).join("");
        }
      }
    }

    async function refreshBenchPanel(full = false) {
      for (const kind of ["ph", "temp", "tds", "voc"]) {
        try {
          await refreshBenchCard(kind, full);
        } catch (err) {
          setBenchUnavailable(kind, err.message || String(err));
        }
      }
    }

    function mountBenchPanel() {
      const slot = document.getElementById("bench-slot");
      if (!slot) return;
      slot.innerHTML = renderBenchPanel();

      const details = slot.querySelector('.station[data-station-id="bench_suite"]');
      if (details) {
        details.addEventListener("toggle", () => saveExpandedState("bench_suite", details.open));
      }

      slot.querySelectorAll('.js-bench-card').forEach(card => {
        card.addEventListener('toggle', () => setBenchCardOpen(card.dataset.kind, card.open));
      });

      slot.querySelectorAll('.detail-section').forEach(section => {
        section.addEventListener('toggle', async () => {
          setBenchSectionOpen(section.dataset.kind, section.dataset.section, section.open);
          if (section.open) await refreshBenchCard(section.dataset.kind, true);
        });
      });

      slot.addEventListener("change", async (event) => {
        if (event.target.matches(".js-bench-range")) {
          const kind = event.target.dataset.kind;
          const hours = Number(event.target.value);
          setBenchHours(kind, hours);
          await refreshBenchCard(kind, true);
        }
      });

      slot.addEventListener("click", async (event) => {
        if (event.target.matches(".js-bench-reset")) {
          const kind = event.target.dataset.kind;
          await safeFetchJson(benchCardConfig(kind).reset, 6000, { method: "POST" });
          await refreshBenchCard(kind, true);
        }

        if (event.target.matches(".js-bench-toggle-ph")) {
          const current = await safeFetchJson("/api/ph-live");
          const enabled = current.collecting_enabled === false ? true : false;
          await safeFetchJson("/api/ph-collect-enabled", 6000, {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ enabled })
          });
          await refreshBenchCard("ph", true);
        }

        if (event.target.matches(".js-ph-cal-btn")) {
          const current = await safeFetchJson("/api/ph-live");
          const target = window.prompt("Trim current pH reading to what buffer value?", "4.00");
          if (target === null) return;
          await safeFetchJson("/api/ph-calibration", 6000, {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ mode: "single_offset", target_ph: Number(target), observed_voltage: current.voltage })
          });
          await refreshBenchCard("ph", true);
        }

        if (event.target.matches(".js-ph-cal-reset")) {
          await safeFetchJson("/api/ph-calibration", 6000, {
            method: "POST",
            headers: { "Content-Type": "application/json" },
            body: JSON.stringify({ mode: "reset" })
          });
          await refreshBenchCard("ph", true);
        }

        if (event.target.matches("[data-temp-unit]")) {
          setTempPrimaryUnit(event.target.dataset.tempUnit);
          updateTempUnitButtons(slot);
          refreshBenchCard("temp", true);
        }
      });

      updateTempUnitButtons(slot);
    }

    async function attachDynamicHandlers() {
      document.querySelectorAll('.station[data-station-id]:not([data-station-id="bench_suite"])').forEach(stationEl => {
        stationEl.addEventListener("toggle", () => saveExpandedState(stationEl.dataset.stationId, stationEl.open));
      });
      document.querySelectorAll(".probe-range").forEach(select => {
        select.addEventListener("change", async (event) => {
          const card = event.target.closest(".probe-card");
          await refreshProbeCard(card);
        });
      });
      document.querySelectorAll("[data-save-station]").forEach(btn => {
        btn.addEventListener("click", async () => {
          await saveStationConfig(btn.dataset.saveStation);
        });
      });
      for (const card of document.querySelectorAll(".probe-card[data-station-id]")) {
        await refreshProbeCard(card);
      }
    }

    async function loadDashboard() {
      const content = document.getElementById("content");
      try {
        const stations = await safeFetchJson("/api/dashboard");
        if (!stations.length) {
          content.className = "empty";
          content.innerHTML = "No station data received yet.";
          return;
        }
        content.className = "";
        content.innerHTML = stations.map(renderStation).join("");
        await attachDynamicHandlers();
      } catch (err) {
        content.className = "empty";
        content.innerHTML = `Dashboard load failed: ${escapeHtml(err.message || String(err))}`;
      }
    }

    mountBenchPanel();
    refreshBenchPanel(true);
    loadDashboard();
    setInterval(loadDashboard, 60000);
    setInterval(() => refreshBenchPanel(false), 5000);
    setInterval(() => refreshBenchPanel(true), 30000);
  </script>
</body>
</html>
'''
    html = html.replace("__DEFAULT_HOURS__", json.dumps(DEFAULT_HOURS))
    html = html.replace("__ALLOWED_WINDOWS__", json.dumps(ALLOWED_WINDOWS))
    return Response(html, mimetype="text/html")


if __name__ == "__main__":
    init_db()
    init_ads_hardware()
    init_temp_hardware()
    init_voc_hardware()
    start_bench_logger()
    app.run(host="0.0.0.0", port=5000, debug=False)
