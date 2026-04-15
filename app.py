import re
import os
import json
import yaml
import calendar
import requests
import streamlit as st
from datetime import datetime, date, timedelta, time as dtime
from io import BytesIO

# PDF (ReportLab Platypus)
from reportlab.lib.pagesizes import A4
from reportlab.lib import colors
from reportlab.lib.units import mm
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, Image as RLImage
)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle

# Email (SMTP)
import smtplib
from email.message import EmailMessage


# -------------------- Paths / Config --------------------
CATALOGUE_PATH = "vaccine_catalogue.yml"
CLINIC_CFG_PATH = "clinic_config.yml"
BATCH_HISTORY_PATH = "batch_history.json"
MAX_BATCHES_PER_PRODUCT = 10

LOGO_PATH = "assets/logo.png"

SITE_OPTIONS = ["Left deltoid", "Right deltoid", "Left thigh", "Right thigh", "Oral"]
SITE_OPTIONS_WITH_BLANK = [""] + SITE_OPTIONS

st.set_page_config(page_title="Vaccination Record", layout="centered")
st.caption("APP VERSION: 2026-02-26 — PRO PDF + GMAIL SMTP + AQL SMS_GW SCHEDULING (10:00 fixed)")


# -------------------- Helpers --------------------
def load_yaml(path: str):
    with open(path, "r", encoding="utf-8") as f:
        return yaml.safe_load(f) or {}


def fmt_uk(d: date) -> str:
    return d.strftime("%d/%m/%Y")


def parse_uk(s: str):
    s = (s or "").strip()
    if not s:
        return None
    try:
        return datetime.strptime(s, "%d/%m/%Y").date()
    except Exception:
        return None


def add_months(d: date, m: int) -> date:
    y = d.year + (d.month - 1 + m) // 12
    mo = (d.month - 1 + m) % 12 + 1
    day = min(d.day, calendar.monthrange(y, mo)[1])
    return date(y, mo, day)


def add_years(d: date, y: int) -> date:
    try:
        return d.replace(year=d.year + y)
    except ValueError:
        return d + timedelta(days=365 * y)


def calc_date(start: date, offset_days=None, offset_months=None) -> date:
    out = start
    if offset_months is not None:
        out = add_months(out, int(offset_months))
    if offset_days is not None:
        out = out + timedelta(days=int(offset_days))
    return out


def calc_effective_until_date(vacc_date: date, validity_years=None, validity_months=None, validity_days=None) -> str:
    if vacc_date is None:
        return ""
    if validity_years is None and validity_months is None and validity_days is None:
        return ""
    eff = vacc_date
    if validity_days is not None:
        eff = eff + timedelta(days=int(validity_days))
    if validity_months is not None:
        eff = add_months(eff, int(validity_months))
    if validity_years is not None:
        eff = add_years(eff, int(validity_years))
    return fmt_uk(eff)


def _offset_int(dose_meta: dict, key: str) -> int:
    v = dose_meta.get(key, None)
    if v is None:
        return 0
    try:
        return int(v)
    except Exception:
        return 0


def effective_until_final_dose(vacc_date: date, dose_meta: dict) -> str:
    vt = (dose_meta.get("validity_text") or "").strip()
    if vt:
        low = vt.lower()
        if "lifetime" in low:
            return "Lifetime"
        if low in {"n/a", "na", "not applicable", "not applicable."}:
            return "Not applicable"
        return vt

    return calc_effective_until_date(
        vacc_date=vacc_date,
        validity_years=dose_meta.get("validity_years"),
        validity_months=dose_meta.get("validity_months"),
        validity_days=dose_meta.get("validity_days"),
    )


def effective_until_display(vacc_date: date, doses: list, dose_idx: int) -> str:
    """
    Non-final dose -> next dose due date (based on deltas).
    Final dose -> validity (validity_text OR computed date).
    """
    if vacc_date is None:
        return ""
    if not doses or dose_idx < 0 or dose_idx >= len(doses):
        return ""

    # Non-final dose -> next dose due date
    if dose_idx < len(doses) - 1:
        cur = doses[dose_idx]
        nxt = doses[dose_idx + 1]

        delta_months = _offset_int(nxt, "offset_months") - _offset_int(cur, "offset_months")
        delta_days = _offset_int(nxt, "offset_days") - _offset_int(cur, "offset_days")

        next_due = vacc_date
        if delta_months:
            next_due = add_months(next_due, delta_months)
        if delta_days:
            next_due = next_due + timedelta(days=delta_days)

        return fmt_uk(next_due)

    # Final dose -> validity
    return effective_until_final_dose(vacc_date, doses[dose_idx])


def slug(s: str) -> str:
    s = (s or "").strip().lower()
    s = re.sub(r"[^a-z0-9]+", "_", s)
    return s.strip("_") or "item"


# -------------------- Preferred anchor dose rules --------------------
def _highest_numbered_dose_index(dose_labels: list) -> int:
    best_idx = None
    best_num = -1
    for i, lab in enumerate(dose_labels):
        s = (lab or "").lower()
        m = re.search(r"\bdose\s*(\d+)\b", s)
        if m:
            try:
                n = int(m.group(1))
                if n > best_num:
                    best_num = n
                    best_idx = i
            except Exception:
                pass
    if best_idx is not None:
        return best_idx
    return max(0, len(dose_labels) - 1)


def preferred_anchor_index(vkey: str, plan_name: str, dose_labels: list) -> int:
    vkey = (vkey or "").strip()

    if vkey == "hep_b":
        for i, lab in enumerate(dose_labels):
            if (lab or "").strip().lower() == "dose 3":
                return i
        return _highest_numbered_dose_index(dose_labels)

    if vkey == "japanese_encephalitis":
        for i, lab in enumerate(dose_labels):
            if (lab or "").strip().lower() == "dose 2":
                return i
        return _highest_numbered_dose_index(dose_labels)

    if vkey == "rabies":
        return _highest_numbered_dose_index(dose_labels)

    return _highest_numbered_dose_index(dose_labels)


# -------------------- Grouped date sorting (courses stay together) --------------------
def _dose_rank(label: str) -> int:
    s = (label or "").strip().lower()
    m = re.search(r"(\d+)", s)
    if m:
        try:
            return int(m.group(1))
        except Exception:
            pass
    if "booster" in s:
        return 999
    return 500


def sort_rows_grouped(rows: list) -> list:
    groups = {}
    for r in rows:
        gk = (
            (r.get("vaccine_display") or "").strip(),
            (r.get("plan_name") or "").strip(),
            (r.get("product_name") or "").strip(),
        )
        groups.setdefault(gk, []).append(r)

    def group_start_date(grows: list) -> date:
        ds = [parse_uk(x.get("vacc_date", "")) for x in grows]
        ds = [d for d in ds if d is not None]
        return min(ds) if ds else date(1900, 1, 1)

    group_items = list(groups.items())
    group_items.sort(
        key=lambda kv: (
            group_start_date(kv[1]),
            kv[0][0].lower(),
            kv[0][2].lower(),
            kv[0][1].lower(),
        )
    )

    out = []
    for _, grows in group_items:
        grows.sort(
            key=lambda r: (
                _dose_rank(r.get("dose_label", "")),
                parse_uk(r.get("vacc_date", "")) or date(1900, 1, 1),
            )
        )
        out.extend(grows)

    return out


# -------------------- Batch history --------------------
def load_batches() -> dict:
    if not os.path.exists(BATCH_HISTORY_PATH):
        return {}
    try:
        with open(BATCH_HISTORY_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_batches(b: dict):
    try:
        with open(BATCH_HISTORY_PATH, "w", encoding="utf-8") as f:
            json.dump(b, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def update_batch_history(batch_history: dict, product_name: str, new_batch: str):
    new_batch = (new_batch or "").strip()
    if not new_batch:
        return
    current = batch_history.get(product_name, [])
    if not isinstance(current, list):
        current = []
    current = [b for b in current if (b or "").strip() and (b or "").strip() != new_batch]
    current.insert(0, new_batch)
    batch_history[product_name] = current[:MAX_BATCHES_PER_PRODUCT]


def batch_selector(product_name: str, key_prefix: str, batch_history: dict, remember: bool) -> str:
    saved = batch_history.get(product_name, [])
    if not isinstance(saved, list):
        saved = []
    saved = [(b or "").strip() for b in saved if (b or "").strip()]
    options = [""] + saved

    a, b = st.columns([1.0, 1.0])
    chosen_saved = a.selectbox("Saved batch (optional)", options=options, index=0, key=f"{key_prefix}_saved")
    typed_new = b.text_input("Or type new batch", key=f"{key_prefix}_new")

    typed_new = (typed_new or "").strip()
    chosen_saved = (chosen_saved or "").strip()
    final_batch = typed_new if typed_new else chosen_saved

    if remember and typed_new:
        update_batch_history(batch_history, product_name, typed_new)
        save_batches(batch_history)

    return final_batch


# -------------------- Preview gating --------------------
def reset_preview_flags():
    st.session_state["pdf_preview_ready"] = False
    st.session_state["pdf_preview_bytes"] = None
    st.session_state["pdf_preview_name"] = None


def ensure_preview_state():
    if "pdf_preview_ready" not in st.session_state:
        reset_preview_flags()


# -------------------- PDF (Professional header + NO footer disclaimer) --------------------
def build_pdf_professional(clinic_cfg: dict, patient_name: str, patient_dob: str, rows: list) -> bytes:
    buffer = BytesIO()

    doc = SimpleDocTemplate(
        buffer,
        pagesize=A4,
        leftMargin=16 * mm,
        rightMargin=16 * mm,
        topMargin=14 * mm,
        bottomMargin=14 * mm,
        title="Vaccination Record",
        author=clinic_cfg.get("clinic_name", "Clinic"),
    )

    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name="ETC_Title", fontSize=16, leading=18, spaceAfter=6))
    styles.add(ParagraphStyle(name="ETC_H2", fontSize=12, leading=14, spaceAfter=4))
    styles.add(ParagraphStyle(name="ETC_Small", fontSize=9.5, leading=12))
    styles.add(ParagraphStyle(name="ETC_Grey", fontSize=8.5, leading=10.5, textColor=colors.grey))

    story = []

    clinic_name = clinic_cfg.get("clinic_name", "HealthClinic2You")
    clinic_website = (clinic_cfg.get("website", "www.healthclinic2you.com") or "").strip()
    clinic_phone = (clinic_cfg.get("phone", "02085670982") or "").strip()
    clinic_address = (clinic_cfg.get("address", "") or "").strip()

    website_href = clinic_website
    if website_href and not website_href.lower().startswith(("http://", "https://")):
        website_href = "https://" + website_href

    phone_digits = re.sub(r"\s+", "", clinic_phone)
    phone_href = f"tel:{phone_digits}" if phone_digits else ""

    link_colour = "#1a73e8"

    right_lines = [f"<b>{clinic_name}</b>"]
    if clinic_address:
        right_lines.append(clinic_address)

    if clinic_website:
        right_lines.append(
            f'<link href="{website_href}"><font color="{link_colour}"><u>{clinic_website}</u> ↗</font></link>'
        )

    if clinic_phone:
        if phone_href:
            right_lines.append(
                f'Tel: <link href="{phone_href}"><font color="{link_colour}"><u>{clinic_phone}</u></font></link>'
            )
        else:
            right_lines.append(f"Tel: {clinic_phone}")

    right_para = Paragraph("<br/>".join(right_lines), styles["ETC_Small"])

    logo_cell = ""
    if os.path.exists(LOGO_PATH):
        try:
            logo = RLImage(LOGO_PATH)

            target_h = 18 * mm
            max_w = 60 * mm

            iw = float(getattr(logo, "imageWidth", 0) or 0)
            ih = float(getattr(logo, "imageHeight", 0) or 0)

            if iw > 0 and ih > 0:
                scale = target_h / ih
                new_w = iw * scale
                new_h = ih * scale

                if new_w > max_w:
                    scale = max_w / iw
                    new_w = iw * scale
                    new_h = ih * scale

                logo.drawWidth = new_w
                logo.drawHeight = new_h
            else:
                logo.drawHeight = target_h

            logo_cell = logo
        except Exception:
            logo_cell = ""

    header_tbl = Table(
        [[logo_cell, right_para]],
        colWidths=[70 * mm, 110 * mm],
    )
    header_tbl.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("ALIGN", (1, 0), (1, 0), "RIGHT"),
        ("LEFTPADDING", (0, 0), (-1, -1), 0),
        ("RIGHTPADDING", (0, 0), (-1, -1), 0),
        ("TOPPADDING", (0, 0), (-1, -1), 0),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 0),
    ]))
    story.append(header_tbl)

    divider = Table([[""]], colWidths=[180 * mm], rowHeights=[1])
    divider.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), colors.lightgrey),
        ("LEFTPADDING", (0, 0), (-1, -1), 0),
        ("RIGHTPADDING", (0, 0), (-1, -1), 0),
        ("TOPPADDING", (0, 0), (-1, -1), 6),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 6),
    ]))
    story.append(divider)
    story.append(Spacer(1, 8))

    story.append(Paragraph("Vaccination Record", styles["ETC_Title"]))
    story.append(Paragraph(f"<b>Patient:</b> {patient_name}", styles["ETC_H2"]))
    story.append(Paragraph(f"<b>Date of birth:</b> {patient_dob if patient_dob else '—'}", styles["ETC_Small"]))
    story.append(Spacer(1, 10))

    table_header = ["Vaccine", "Product", "Course plan", "Dose", "Date", "Batch", "Effective until", "Site"]
    data = [table_header]

    for r in rows:
        data.append([
            Paragraph(r.get("vaccine_display", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("product_name", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("plan_name", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("dose_label", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("vacc_date", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("batch", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("effective_until", "") or "", styles["ETC_Small"]),
            Paragraph(r.get("site", "") or "", styles["ETC_Small"]),
        ])

    col_widths = [
        30 * mm,  # Vaccine
        25 * mm,  # Product
        30 * mm,  # Course plan
        14 * mm,  # Dose
        22 * mm,  # Date
        18 * mm,  # Batch
        26 * mm,  # Effective until
        15 * mm,  # Site
    ]

    tbl = Table(data, colWidths=col_widths, repeatRows=1)
    tbl.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1f4e79")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, 0), 9),
        ("ALIGN", (0, 0), (-1, 0), "CENTER"),

        ("GRID", (0, 0), (-1, -1), 0.25, colors.lightgrey),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.HexColor("#f7f9fc"), colors.white]),

        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),

        ("ALIGN", (0, 1), (2, -1), "LEFT"),
        ("ALIGN", (3, 1), (3, -1), "CENTER"),
        ("ALIGN", (4, 1), (4, -1), "CENTER"),
        ("ALIGN", (5, 1), (5, -1), "CENTER"),
        ("ALIGN", (6, 1), (6, -1), "CENTER"),
        ("ALIGN", (7, 1), (7, -1), "CENTER"),
    ]))

    story.append(tbl)
    story.append(Spacer(1, 10))

    generated_str = datetime.now().strftime("%d/%m/%Y %H:%M")
    story.append(Paragraph(f"Generated: {generated_str}", styles["ETC_Grey"]))

    doc.build(story)
    pdf_bytes = buffer.getvalue()
    buffer.close()
    return pdf_bytes


# -------------------- Email (SMTP) --------------------
def smtp_config_ok():
    return all([
        st.secrets.get("SMTP_HOST", ""),
        st.secrets.get("SMTP_PORT", ""),
        st.secrets.get("SMTP_USER", ""),
        st.secrets.get("SMTP_PASS", ""),
    ])


def send_email_with_pdf(to_email: str, subject: str, body: str, pdf_bytes: bytes, filename: str):
    host = st.secrets["SMTP_HOST"]
    port = int(st.secrets["SMTP_PORT"])
    user = st.secrets["SMTP_USER"]
    pw = st.secrets["SMTP_PASS"]
    from_name = st.secrets.get("SMTP_FROM_NAME", "Ealing Travel Clinic")

    msg = EmailMessage()
    msg["From"] = f"{from_name} <{user}>"
    msg["To"] = to_email
    msg["Subject"] = subject
    msg.set_content(body)
    msg.add_attachment(pdf_bytes, maintype="application", subtype="pdf", filename=filename)

    with smtplib.SMTP(host, port, timeout=30) as server:
        server.ehlo()
        server.starttls()
        server.login(user, pw)
        server.send_message(msg)


# -------------------- AQL SMS (sms_gw.php) helpers --------------------
def normalise_uk_mobile_to_aql(msisdn: str) -> str:
    m = (msisdn or "").strip().replace(" ", "")
    if not m:
        return ""
    if m.startswith("+"):
        m = m[1:]
    if m.startswith("00"):
        m = m[2:]
    if m.startswith("0"):
        m = "44" + m[1:]
    m = re.sub(r"\D", "", m)
    return m


def dt_to_aql_sendtime(dt: datetime) -> str:
    # AQL gateway commonly accepts: YYYY-MM-DD HH:MM:SS
    return dt.strftime("%Y-%m-%d %H:%M:%S")


def aql_sms_gw_send(user: str, pw: str, destination: str, message: str, originator: str, send_dt: datetime, gw_url: str):
    """
    Uses AQL HTTP gateway sms_gw.php which returns text like:
      0:1 SMS successfully queued
    Scheduling is done via sendtime parameter.
    """
    params = {
        "username": user,
        "password": pw,
        "destination": destination,     # e.g. 4477...
        "message": message,
        "originator": originator,       # up to 11 chars
        "sendtime": dt_to_aql_sendtime(send_dt),
    }

    resp = requests.get(gw_url, params=params, timeout=30)
    return resp.status_code, resp.text, params


def aql_sms_config_ok():
    return all([
        st.secrets.get("AQL_SOAP_USER", ""),
        st.secrets.get("AQL_SOAP_PASS", ""),
        st.secrets.get("AQL_SMS_FROM", ""),
    ])


# -------------------- Load data --------------------
clinic_cfg = load_yaml(CLINIC_CFG_PATH)
catalogue = load_yaml(CATALOGUE_PATH)
batch_history = load_batches()

product_entries = []
for vkey, vmeta in (catalogue or {}).items():
    for p in (vmeta.get("products", []) or []):
        pname = (p.get("name") or "").strip() if isinstance(p, dict) else str(p).strip()
        if pname:
            product_entries.append((pname, vkey))

product_entries.sort(key=lambda x: x[0].lower())
product_labels = [p[0] for p in product_entries]
product_to_vkey = {p[0]: p[1] for p in product_entries}


# -------------------- UI --------------------
ensure_preview_state()

if not os.path.exists(LOGO_PATH):
    st.warning("Logo not found at assets/logo.png. Upload it to GitHub to show on the PDF.")

with st.sidebar:
    st.subheader("Clinic convenience")
    remember_batches = st.toggle("Remember batches per product", value=True)
    if st.button("Clear saved batch history"):
        batch_history = {}
        save_batches(batch_history)
        st.success("Saved batch history cleared.")

today_uk = fmt_uk(date.today())

st.subheader("Patient details")
patient_name = st.text_input("Full name", key="patient_name", on_change=reset_preview_flags)
patient_email = st.text_input("Email address (used for sending only)", key="patient_email", on_change=reset_preview_flags)
patient_dob = st.text_input("DOB (optional, DD/MM/YYYY)", key="patient_dob", on_change=reset_preview_flags)

st.subheader("Vaccines administered")
chosen_products = st.multiselect(
    "Search and select product(s)",
    options=product_labels,
    key="chosen_products",
    on_change=reset_preview_flags,
)

rows_preview = []

for prod_name in chosen_products:
    vkey = product_to_vkey[prod_name]
    vmeta = (catalogue or {}).get(vkey, {})
    vdisplay = vmeta.get("display", vkey)

    plans = vmeta.get("course_plans", []) or [
        {"name": "Single dose", "doses": [{"label": "Dose 1", "offset_days": 0}]}
    ]
    plan_names = [p.get("name", "Plan") for p in plans]
    pid = f"{vkey}__{slug(prod_name)}"

    st.markdown(f"### {prod_name}\n*Vaccine:* {vdisplay}")

    if len(plan_names) == 1:
        plan_name = plan_names[0]
        st.markdown(f"*Course plan:* {plan_name}")
    else:
        plan_name = st.selectbox("Course plan", plan_names, key=f"plan_{pid}", on_change=reset_preview_flags)

    plan = plans[plan_names.index(plan_name)]
    doses = plan.get("doses", []) or []
    dose_labels = [d.get("label", f"Dose {i+1}") for i, d in enumerate(doses)]

    # ---------------- Single-dose ----------------
    if len(doses) == 1:
        date_str = st.text_input("Date given (DD/MM/YYYY)", value=today_uk, key=f"date_{pid}_0", on_change=reset_preview_flags)
        date_val = parse_uk(date_str) or date.today()

        batch_val = batch_selector(prod_name, f"batch_{pid}_0", batch_history, remember_batches)
        site_val = st.selectbox("Site", SITE_OPTIONS, index=0, key=f"site_{pid}_0", on_change=reset_preview_flags)

        eff_val = effective_until_display(date_val, doses, 0)
        st.text(f"Effective until: {eff_val}")

        rows_preview.append({
            "vaccine_display": vdisplay,
            "product_name": prod_name,
            "plan_name": plan_name,
            "dose_label": dose_labels[0],
            "vacc_date": fmt_uk(date_val),
            "batch": batch_val,
            "effective_until": eff_val,
            "site": site_val,
        })
        continue

    # ---------------- Multi-dose (default anchor per vaccine) ----------------
    default_anchor_idx = preferred_anchor_index(vkey=vkey, plan_name=plan_name, dose_labels=dose_labels)

    c1, c2 = st.columns([1.2, 1.0])
    anchor_label = c1.selectbox(
        "Dose administered today",
        dose_labels,
        index=min(max(default_anchor_idx, 0), len(dose_labels) - 1),
        key=f"anchor_{pid}",
        on_change=reset_preview_flags
    )
    anchor_date_str = c2.text_input(
        "Today’s dose date (DD/MM/YYYY)",
        value=today_uk,
        key=f"anchor_date_{pid}",
        on_change=reset_preview_flags
    )

    anchor_date = parse_uk(anchor_date_str)
    if not anchor_date:
        st.warning("Enter a valid date for today’s dose (DD/MM/YYYY).")
        continue

    include_all = st.toggle("Include full course doses", value=False, key=f"include_all_{pid}", on_change=reset_preview_flags)
    anchor_idx = dose_labels.index(anchor_label)

    anchor_meta = doses[anchor_idx]
    start_date = anchor_date
    if anchor_meta.get("offset_months") is not None:
        start_date = add_months(start_date, -int(anchor_meta["offset_months"]))
    if anchor_meta.get("offset_days") is not None:
        start_date = start_date - timedelta(days=int(anchor_meta["offset_days"]))

    seed = f"{plan_name}||{anchor_label}||{anchor_date_str}"
    seed_key = f"seed_{pid}"
    if st.session_state.get(seed_key) != seed:
        st.session_state[seed_key] = seed
        for j, dj in enumerate(doses):
            scheduled = calc_date(start_date, dj.get("offset_days", None), dj.get("offset_months", None))
            default_j = anchor_date if j == anchor_idx else scheduled
            st.session_state[f"date_{pid}_{j}"] = fmt_uk(default_j)

    # ---- TODAY DOSE ----
    st.markdown("---")
    st.subheader("Today’s dose details")
    st.caption(f"{anchor_label} date: {fmt_uk(anchor_date)}")

    batch_today = batch_selector(prod_name, f"batch_{pid}_{anchor_idx}", batch_history, remember_batches)
    site_today = st.selectbox("Site", SITE_OPTIONS, index=0, key=f"site_{pid}_{anchor_idx}", on_change=reset_preview_flags)

    eff_today = effective_until_display(anchor_date, doses, anchor_idx)
    st.text(f"Effective until: {eff_today}")

    rows_preview.append({
        "vaccine_display": vdisplay,
        "product_name": prod_name,
        "plan_name": plan_name,
        "dose_label": dose_labels[anchor_idx],
        "vacc_date": fmt_uk(anchor_date),
        "batch": batch_today,
        "effective_until": eff_today,
        "site": site_today,
    })

    # ---- OTHER DOSES ----
    if include_all:
        st.markdown("---")
        st.subheader("Other doses (optional)")

        for i, d in enumerate(doses):
            if i == anchor_idx:
                continue

            dose_label = dose_labels[i]
            inc = st.checkbox(f"Include {dose_label}", value=True, key=f"inc_{pid}_{i}", on_change=reset_preview_flags)
            if not inc:
                continue

            default_str = st.session_state.get(f"date_{pid}_{i}", today_uk)
            date_str = st.text_input(f"{dose_label} date (DD/MM/YYYY)", value=default_str, key=f"date_{pid}_{i}", on_change=reset_preview_flags)
            date_val = parse_uk(date_str) or parse_uk(default_str) or anchor_date

            batch_val = ""
            site_val = ""
            with st.expander(f"{dose_label} batch/site (optional)", expanded=False):
                batch_val = batch_selector(prod_name, f"batch_{pid}_{i}", batch_history, remember_batches)
                site_val = st.selectbox("Site (optional)", SITE_OPTIONS_WITH_BLANK, index=0, key=f"site_{pid}_{i}", on_change=reset_preview_flags)

            eff_val = effective_until_display(date_val, doses, i)
            st.text(f"Effective until: {eff_val}")

            rows_preview.append({
                "vaccine_display": vdisplay,
                "product_name": prod_name,
                "plan_name": plan_name,
                "dose_label": dose_label,
                "vacc_date": fmt_uk(date_val),
                "batch": batch_val,
                "effective_until": eff_val,
                "site": site_val,
            })

st.divider()

# -------------------- Preview / Download PDF --------------------
cA, cB = st.columns([1, 1])

with cA:
    if st.button("Preview vaccination record (PDF)", type="primary"):
        if not (patient_name or "").strip():
            st.error("Please enter patient name.")
            st.stop()
        if not rows_preview:
            st.error("No doses included. Select products and include at least one dose.")
            st.stop()

        rows_sorted = sort_rows_grouped(rows_preview)

        pdf_bytes = build_pdf_professional(
            clinic_cfg=clinic_cfg,
            patient_name=patient_name.strip(),
            patient_dob=(patient_dob or "").strip(),
            rows=rows_sorted,
        )

        st.session_state["pdf_preview_ready"] = True
        st.session_state["pdf_preview_bytes"] = pdf_bytes
        st.session_state["pdf_preview_name"] = f"vaccination_record_{date.today().isoformat()}.pdf"
        st.success("Preview generated. Download and check before sending.")

with cB:
    if st.session_state.get("pdf_preview_ready") and st.session_state.get("pdf_preview_bytes"):
        st.download_button(
            "Download preview PDF",
            data=st.session_state["pdf_preview_bytes"],
            file_name=st.session_state.get("pdf_preview_name", "vaccination_record.pdf"),
            mime="application/pdf",
        )
    else:
        st.caption("Preview first to enable download and sending.")

st.divider()

# -------------------- Email sending (gated by preview) --------------------
st.subheader("Send vaccination record (Email)")

if not st.session_state.get("pdf_preview_ready"):
    st.warning("Preview the PDF above first. Then you can send the email.")
else:
    subject = st.text_input("Email subject", value="Your Vaccination Record – Ealing Travel Clinic")
    body = st.text_area(
        "Email message",
        value=(
            f"Dear {patient_name.strip() or 'Patient'},\n\n"
            "Please find attached your vaccination record from Ealing Travel Clinic.\n\n"
            "Kind regards,\nEaling Travel Clinic"
        ),
        height=130,
    )

    if not patient_email.strip():
        st.info("Enter the patient email above to enable sending.")
        st.button("Confirm & send email", disabled=True)
    elif not smtp_config_ok():
        st.warning("Email sending is not configured yet (SMTP secrets missing).")
        st.button("Confirm & send email", disabled=True)
    else:
        if st.button("Confirm & send email", type="secondary"):
            try:
                send_email_with_pdf(
                    to_email=patient_email.strip(),
                    subject=subject.strip(),
                    body=body.strip(),
                    pdf_bytes=st.session_state["pdf_preview_bytes"],
                    filename=st.session_state.get("pdf_preview_name", "vaccination_record.pdf"),
                )
                st.success("Email sent successfully.")
            except Exception as e:
                st.error(f"Email failed: {e}")

st.divider()

# -------------------- SMS reminders (AQL sms_gw.php scheduled) --------------------
st.subheader("Booster / dose reminders (SMS) — Scheduled (10:00)")

# Hide confusing fields from clinicians; admin-only diagnostics toggle:
show_admin = st.checkbox("Show admin diagnostics", value=False)

aql_user = st.secrets.get("AQL_SOAP_USER", "").strip()
aql_pass = st.secrets.get("AQL_SOAP_PASS", "").strip()
aql_from = st.secrets.get("AQL_SMS_FROM", "EalingTC").strip()
aql_gw_url = st.secrets.get("AQL_SMS_GW_URL", "http://gw.aql.com/sms/sms_gw.php").strip()

if not aql_sms_config_ok():
    st.info("To enable SMS scheduling: add AQL_SOAP_USER, AQL_SOAP_PASS, and AQL_SMS_FROM in Streamlit Secrets.")
else:
    templates = {
        "Hepatitis A booster (6 months after dose 1)": {
            "text": (
                "Ealing Travel Clinic: your Hep A booster is due. "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": 6,
            "years_offset": None,
            "ref_label": "Hep A dose 1 date (DD/MM/YYYY)",
        },
        "Hepatitis B booster (accelerated: 1 year after dose 3)": {
            "text": (
                "Ealing Travel Clinic: your Hep B booster is due (accelerated course). "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": None,
            "years_offset": 1,
            "ref_label": "Hep B dose 3 date (DD/MM/YYYY)",
        },
        "Japanese encephalitis booster (1 year after dose 2)": {
            "text": (
                "Ealing Travel Clinic: your Japanese encephalitis booster is due. "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": None,
            "years_offset": 1,
            "ref_label": "JE dose 2 date (DD/MM/YYYY)",
        },
        "TBE dose 3 reminder (5 months after dose 2)": {
            "text": (
                "Ealing Travel Clinic: your tick-borne encephalitis vaccine dose 3 is due. "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": 5,
            "years_offset": None,
            "ref_label": "TBE dose 2 date (DD/MM/YYYY)",
        },
        "HPV dose 2 reminder (6 months after dose 1)": {
            "text": (
                "Ealing Travel Clinic: your HPV vaccine dose 2 is due. "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": 6,
            "years_offset": None,
            "ref_label": "HPV dose 1 date (DD/MM/YYYY)",
        },
    "Trumenba dose 2 reminder (6 months after dose 1)": {
            "text": (
                "Ealing Travel Clinic: your Trumenba meningitis B vaccine dose 2 is now due. "
                "Book: www.ealingtravelclinic.co.uk or call 02085670982"
            ),
            "months_offset": 6,
            "years_offset": None,
            "ref_label": "Trumenba dose 1 date (DD/MM/YYYY)",
        },
        }
        
    reminder_type = st.selectbox("Reminder type", list(templates.keys()))
    sms_text = templates[reminder_type]["text"]

    st.text_area("SMS text (≤160 characters)", sms_text, height=80, disabled=True)
    st.caption(f"Character count: {len(sms_text)} / 160")

    c1, c2 = st.columns([1.2, 1.0])
    mobile = c1.text_input("Patient mobile (UK)")
    ref_date_str = c2.text_input(templates[reminder_type]["ref_label"], value=today_uk)
    ref_date = parse_uk(ref_date_str)

    scheduled_date = None
    if ref_date:
        mo = templates[reminder_type]["months_offset"]
        yr = templates[reminder_type]["years_offset"]
        scheduled_date = ref_date
        if mo is not None:
            scheduled_date = add_months(scheduled_date, int(mo))
        if yr is not None:
            scheduled_date = add_years(scheduled_date, int(yr))

    send_dt = None
    if scheduled_date:
        send_dt = datetime.combine(scheduled_date, dtime(10, 0))
        st.info(f"Will schedule for: {fmt_uk(scheduled_date)} at 10:00")
    else:
        st.warning("Enter a valid reference date (DD/MM/YYYY) to calculate reminder date.")

    consent = st.checkbox("Patient consented to receive SMS reminders", value=False)

    if not st.session_state.get("pdf_preview_ready"):
        st.warning("Preview the PDF above before scheduling an SMS reminder.")
    else:
        if st.button("Confirm & schedule SMS reminder", type="secondary"):
            if not consent:
                st.error("Please confirm the patient has consented to receive SMS reminders.")
                st.stop()

            dest = normalise_uk_mobile_to_aql(mobile)
            if not dest or not dest.isdigit() or not dest.startswith("44"):
                st.error("Enter a valid UK mobile number (07..., +447..., 447...).")
                st.stop()

            if send_dt is None:
                st.error("No scheduled time calculated. Check the reference date.")
                st.stop()

            # Avoid accidental immediate sends: if scheduled time is too soon/past, block
            now = datetime.now()
            if send_dt <= now + timedelta(minutes=5):
                st.error("Scheduled time is too soon or in the past. Check the reference date.")
                st.stop()

            try:
                status, resp_text, params_used = aql_sms_gw_send(
                    user=aql_user,
                    pw=aql_pass,
                    destination=dest,
                    message=sms_text,
                    originator=aql_from,
                    send_dt=send_dt,
                    gw_url=aql_gw_url,
                )

                ok = (status == 200) and isinstance(resp_text, str) and resp_text.strip().startswith("0:")
                if ok:
                    st.success("AQL accepted scheduling: " + resp_text.strip())
                    st.caption(f"Scheduled for {fmt_uk(scheduled_date)} at 10:00 • Patient: {mobile.strip()}")
                else:
                    st.error("AQL did not confirm success.")

                if show_admin:
                    with st.expander("AQL diagnostics (admin)", expanded=not ok):
                        masked = dict(params_used)
                        if "password" in masked:
                            masked["password"] = "********"
                        st.json({
                            "endpoint_used": aql_gw_url,
                            "http_status": status,
                            "response_text": (resp_text or "").strip(),
                            "params_sent": masked,
                        })

            except Exception as e:
                st.error(f"SMS scheduling failed: {e}")
                st.caption("If this is an SSL/HTTPS error, keep using the default HTTP gateway URL in Secrets.")
