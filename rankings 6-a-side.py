# ==========================================
# Multi-Team Ranking Image Generator
# PSMF + PKFL
# ==========================================
import os
import re
import time
import io
import unicodedata
from google.oauth2.service_account import Credentials
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

import sys
import json
import requests
from PIL import Image, ImageDraw, ImageFont, ImageFilter

import pandas as pd

from selenium import webdriver
from selenium.common.exceptions import NoSuchElementException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager


# ============================================================
# CONFIG
# ============================================================
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

CREDENTIALS_FILE = os.path.join(SCRIPT_DIR, "credentials.json")
LOGOS_FOLDER_ID = "19NNyf1trl1LoA7Tth7PFMbRAv65oXeeR"

BACKGROUNDS_FOLDER_ID = "1QPBNq9ip3d9DwwKK88I5Ff5OVmdqcqYW"

BACKGROUND_TEMPLATE_PATTERN = os.path.join(SCRIPT_DIR, "background {count}.png")
OUTPUT_DIR = os.path.join(SCRIPT_DIR, "output", "rankings")

RANKING_CONFIGS = [
    {
        "team": "6A",
        "source": "pkfl",
        "url": "https://pkfl.cz/liga/s183/s2vse/s365",
        "league_label": "PKFL",
    },
    {
        "team": "6B",
        "source": "psmf",
        "url": "https://www.psmf.cz/souteze/2026-hanspaulska-liga-podzim/6-j/",
        "league_label": "6.J",
    },
    {
        "team": "6C",
        "source": "psmf",
        "url": "https://www.psmf.cz/souteze/2026-hanspaulska-liga-podzim/8-b/",
        "league_label": "8.B",
    },
    {
        "team": "6D",
        "source": "pkfl",
        "url": "https://pkfl.cz/liga/s183/s2vse/s39",
        "league_label": "PKFL",
    },
    {
        "team": "VETs",
        "source": "psmf",
        "url": "https://www.psmf.cz/souteze/2026-veteranska-liga-podzim/3-d/",
        "league_label": "3.D",
    },
]

META_CONFIG_FILE = os.path.join(SCRIPT_DIR, "meta_config_6aside.json")

GITHUB_REPO_RAW_BASE = (
    "https://raw.githubusercontent.com/"
    "expediansunited-coder/galaksia-rankings-6-a-side/main/"
)

MANIFEST_FILE = os.path.join(OUTPUT_DIR, "ranking_groups_6aside.json")

STORY_W = 1080
STORY_H = 1920
GRAPH = "https://graph.facebook.com/v20.0"

POST_ORDER = ["6A", "6B", "6C", "6D", "VETs"]

TEXT_WHITE = (255, 255, 255)
TEXT_BLACK = (0, 0, 0)
TEXT_LIGA_GREY = (210, 210, 210)
GALAKSIA_GREEN = (55, 190, 75)

# Template was supplied as 768x960.
# These positions are scaled automatically if your local template has another size.
BASE_W = 768
BASE_H = 960

# Table cell centers based on provided template
TABLE_X_CENTERS = {
    "position": 42,
    "team": 210,
    "matches": 395,
    "wins": 467,
    "draws": 533,
    "losses": 594,
    "diff": 658,
    "points": 722,
}

FIRST_ROW_Y = 398
ROW_H = 38
MAX_ROWS = 12

TEAM_CELL_MAX_W = 285
NUM_CELL_MAX_W = 58

# League label beside "LIGA"
LEAGUE_LABEL_POS = (190, 158)

# League logo above the word LIGA
LEAGUE_LOGO_CENTER = (305, 58)
LEAGUE_LOGO_MAX_SIZE = 95

# Season text inside green ribbon under "LEAGUE STANDINGS"
SEASON_POS = (230, 326)


# ============================================================
# SELENIUM CONFIG
# ============================================================
chrome_options = Options()
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/121.0.0.0 Safari/537.36"
)
chrome_options.add_argument(f"user-agent={USER_AGENT}")
chrome_options.add_argument("--headless=new")
chrome_options.add_argument("--no-sandbox")
chrome_options.add_argument("--disable-dev-shm-usage")
chrome_options.add_argument("--disable-blink-features=AutomationControlled")


# ============================================================
# HELPERS
# ============================================================
def clean_text(text):
    if not text:
        return ""
    cleaned = text.replace("\xa0", " ").replace("\n", " ").replace("\r", "")
    return re.sub(r"\s+", " ", cleaned).strip()


def scale_xy(x, y, w, h):
    return int(x * w / BASE_W), int(y * h / BASE_H)


def scale_len(v, current, base):
    return int(v * current / base)


def score_diff(score):
    if not score:
        return ""

    m = re.search(r"(-?\d+)\s*[:\-]\s*(-?\d+)", str(score))
    if not m:
        return ""

    try:
        gf = int(m.group(1))
        ga = int(m.group(2))
        diff = gf - ga
        return str(diff)
    except Exception:
        return ""


def get_psmf_season_label():
    now = time.localtime()
    year = now.tm_year
    month = now.tm_mon

    if month >= 7:
        return f"FALL {year}"
    return f"SPRING {year}"


def get_pkfl_season_label():
    now = time.localtime()
    year = now.tm_year
    month = now.tm_mon

    if month >= 7:
        return f"{year}/{year + 1}"
    return f"{year - 1}/{year}"


def get_season_label(source):
    if source == "pkfl":
        return get_pkfl_season_label()
    return get_psmf_season_label()


def load_font(size, bold=True):
    candidates = [
        "Etna.ttf",
        "_etna.ttf",
        "DejaVuSansCondensed-Bold.ttf" if bold else "DejaVuSansCondensed.ttf",
        "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf",
    ]

    for path in candidates:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue

    return ImageFont.load_default()


def fit_font(draw, text, max_width, start_size, min_size=8):
    text = str(text)

    for size in range(start_size, min_size - 1, -1):
        font = load_font(size, bold=True)
        bbox = draw.textbbox((0, 0), text, font=font)
        width = bbox[2] - bbox[0]
        if width <= max_width:
            return font

    return load_font(min_size, bold=True)

def _norm_drive_name(s):
    if not s:
        return ""
    s = unicodedata.normalize("NFKD", str(s))
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", "", s.lower())


def get_drive_service():
    scope = ["https://www.googleapis.com/auth/drive.readonly"]
    creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scope)
    return build("drive", "v3", credentials=creds)

def sync_backgrounds_from_drive(drive):
    files = list_folder_files(drive, BACKGROUNDS_FOLDER_ID)

    for f in files:
        name = f["name"]
        stem, ext = os.path.splitext(name)

        if not re.match(r"^background\s+\d+$", stem.strip(), re.I):
            continue

        if ext.lower() not in (".png", ".jpg", ".jpeg", ".webp"):
            continue

        local_path = os.path.join(SCRIPT_DIR, stem.strip().lower() + ".png")

        raw = download_file_bytes(drive, f["id"])
        img = Image.open(io.BytesIO(raw)).convert("RGBA")
        img.save(local_path, "PNG")

        print(f"  Synced background: {name} -> {local_path}")

def download_file_bytes(drive, file_id):
    request = drive.files().get_media(fileId=file_id)
    buf = io.BytesIO()
    downloader = MediaIoBaseDownload(buf, request)
    done = False
    while not done:
        status, done = downloader.next_chunk()
    return buf.getvalue()


def list_folder_files(drive, folder_id):
    out, page = [], None
    while True:
        resp = drive.files().list(
            q=f"'{folder_id}' in parents and trashed = false",
            fields="nextPageToken, files(id,name,mimeType)",
            pageToken=page
        ).execute()
        out.extend(resp.get("files", []))
        page = resp.get("nextPageToken")
        if not page:
            break
    return out


def find_league_logo_file(logo_files, logo_label):
    target = _norm_drive_name(logo_label)

    for f in logo_files:
        stem = os.path.splitext(f["name"])[0]
        stem_norm = _norm_drive_name(stem)

        if stem_norm == target:
            return f

    for f in logo_files:
        stem = os.path.splitext(f["name"])[0]
        stem_norm = _norm_drive_name(stem)

        if target in stem_norm:
            return f

    return None


def load_league_logo(drive, logo_files, league_label):
    logo_file = find_league_logo_file(logo_files, league_label)
    if not logo_file:
        print(f"  Warning: no league logo found for '{league_label}'")
        return None

    try:
        raw = download_file_bytes(drive, logo_file["id"])
        return Image.open(io.BytesIO(raw)).convert("RGBA")
    except Exception as e:
        print(f"  Warning: could not load league logo '{logo_file['name']}': {e}")
        return None


def paste_logo_centered(base, logo, center_xy, max_size):
    if logo is None:
        return

    logo = logo.copy()
    logo.thumbnail((max_size, max_size), Image.LANCZOS)

    x = int(center_xy[0] - logo.width / 2)
    y = int(center_xy[1] - logo.height / 2)

    base.alpha_composite(logo, (x, y))

# ============================================================
# SCRAPERS
# ============================================================
def scrape_psmf_ranking_table(driver, url):
    ranking_rows = []

    try:
        print(f"[{time.strftime('%H:%M:%S')}] Scraping PSMF ranking: {url}")
        driver.get(url)

        wait = WebDriverWait(driver, 60)
        wait.until(EC.presence_of_element_located((By.CLASS_NAME, "component__inside")))
        time.sleep(2)

        tables_box = driver.find_element(By.CSS_SELECTOR, "div.ci-tables")

        vysledna_btn = None
        actions = tables_box.find_elements(By.CSS_SELECTOR, "a.tables-action")

        for btn in actions:
            title = clean_text(btn.text or btn.get_attribute("title"))
            if "výsledná" in title.lower():
                vysledna_btn = btn
                break

        if vysledna_btn:
            if "is-active" not in (vysledna_btn.get_attribute("class") or ""):
                driver.execute_script("arguments[0].scrollIntoView(true);", vysledna_btn)
                time.sleep(0.5)
                try:
                    vysledna_btn.click()
                except Exception:
                    driver.execute_script("arguments[0].click();", vysledna_btn)
                time.sleep(1.5)

        table = tables_box.find_element(By.CSS_SELECTOR, "table.tables-table")
        rows = table.find_elements(By.CSS_SELECTOR, "tbody tr")

        for row in rows:
            tds = row.find_elements(By.TAG_NAME, "td")
            if len(tds) < 8:
                continue

            position = clean_text(tds[0].get_attribute("textContent")).rstrip(".")
            team = clean_text(tds[1].get_attribute("textContent"))
            matches_played = clean_text(tds[2].get_attribute("textContent"))
            wins = clean_text(tds[3].get_attribute("textContent"))
            draws = clean_text(tds[4].get_attribute("textContent"))
            losses = clean_text(tds[5].get_attribute("textContent"))
            score = clean_text(tds[6].get_attribute("textContent"))
            points = clean_text(tds[7].get_attribute("textContent"))

            ranking_rows.append({
                "Position": int(position) if position.isdigit() else position,
                "Team": team,
                "Matches Played": int(matches_played) if matches_played.isdigit() else matches_played,
                "Wins": int(wins) if wins.isdigit() else wins,
                "Draws": int(draws) if draws.isdigit() else draws,
                "Losses": int(losses) if losses.isdigit() else losses,
                "Score": score,
                "Diff": score_diff(score),
                "Points": int(points) if points.isdigit() else points,
            })

    except Exception as e:
        print(f"  Warning: Could not extract PSMF ranking from {url} ({e})")

    return pd.DataFrame(ranking_rows)


def scrape_pkfl_ranking_table(driver, url):
    ranking_rows = []
    league_label = "PKFL"

    try:
        print(f"[{time.strftime('%H:%M:%S')}] Scraping PKFL ranking: {url}")
        driver.get(url)

        wait = WebDriverWait(driver, 30)
        wait.until(EC.presence_of_element_located((By.ID, "grounds")))
        time.sleep(1)
        league_label = extract_pkfl_league_label(driver)

        table = driver.find_element(By.ID, "grounds")
        rows = table.find_elements(By.CSS_SELECTOR, "tbody tr")

        for row in rows:
            tds = row.find_elements(By.TAG_NAME, "td")
            if len(tds) < 7:
                continue

            position = clean_text(tds[0].get_attribute("textContent")).rstrip(".")

            team_spans = tds[1].find_elements(By.TAG_NAME, "span")
            if team_spans:
                span_texts = [
                    clean_text(s.get_attribute("textContent"))
                    for s in team_spans
                    if clean_text(s.get_attribute("textContent"))
                ]
                team = max(span_texts, key=len) if span_texts else clean_text(tds[1].get_attribute("textContent"))
            else:
                team = clean_text(tds[1].get_attribute("textContent"))

            matches_played = clean_text(tds[2].get_attribute("textContent"))

            vrp_text = clean_text(tds[3].get_attribute("textContent"))
            wins, draws, losses = "", "", ""

            if "/" in vrp_text:
                parts = vrp_text.split("/")
                if len(parts) == 3:
                    wins = parts[0].strip()
                    draws = parts[1].strip()
                    losses = parts[2].strip()

            score = clean_text(tds[4].get_attribute("textContent"))
            points = clean_text(tds[6].get_attribute("textContent"))

            ranking_rows.append({
                "Position": int(position) if position.isdigit() else position,
                "Team": team,
                "Matches Played": int(matches_played) if matches_played.isdigit() else matches_played,
                "Wins": int(wins) if str(wins).isdigit() else wins,
                "Draws": int(draws) if str(draws).isdigit() else draws,
                "Losses": int(losses) if str(losses).isdigit() else losses,
                "Score": score,
                "Diff": score_diff(score),
                "Points": int(points) if str(points).isdigit() else points,
            })

    except Exception as e:
        print(f"  Warning: Could not extract PKFL ranking from {url} ({e})")

    return pd.DataFrame(ranking_rows), league_label

def extract_pkfl_league_label(driver):
    try:
        # Find the label "Ligy:" and then inspect dropdowns in the same parent block.
        league_titles = driver.find_elements(By.CSS_SELECTOR, "span.league-title")

        for title in league_titles:
            title_text = clean_text(title.get_attribute("textContent"))
            if "ligy" not in title_text.lower():
                continue

            parent = title.find_element(By.XPATH, "./parent::*")
            dropdowns = parent.find_elements(By.CSS_SELECTOR, "div.filter-dropdown")

            for dd in dropdowns:
                try:
                    strong = dd.find_element(By.CSS_SELECTOR, "button.dropbtn strong")
                    label = clean_text(strong.get_attribute("textContent"))

                    # Confirm this dropdown is the league dropdown by checking its options,
                    # not by URL and not by hardcoded league IDs.
                    options = dd.find_elements(By.CSS_SELECTOR, "div.dropdown-content a")
                    option_texts = [
                        clean_text(a.get_attribute("textContent"))
                        for a in options
                    ]

                    if not any(re.search(r"\bliga\b", opt, re.I) for opt in option_texts):
                        continue

                    # Page gives e.g. "2. liga", "4.A liga".
                    # Template already has big "LIGA", so keep only "2." / "4.A".
                    label = re.sub(r"\s*liga\s*$", "", label, flags=re.I).strip()

                    if label:
                        return label.upper()

                except Exception:
                    continue

    except Exception:
        pass

    return "PKFL"

# ============================================================
# IMAGE GENERATION
# ============================================================
def draw_centered_text(draw, xy, text, font, fill, stroke_width=0, stroke_fill=(0, 0, 0)):
    text = str(text)

    bbox = draw.textbbox((0, 0), text, font=font, stroke_width=stroke_width)
    text_w = bbox[2] - bbox[0]
    text_h = bbox[3] - bbox[1]

    x = xy[0] - text_w / 2 - bbox[0]
    y = xy[1] - text_h / 2 - bbox[1]

    draw.text(
        (x, y),
        text,
        font=font,
        fill=fill,
        stroke_width=stroke_width,
        stroke_fill=stroke_fill,
    )


def draw_ranking_image(df, cfg, league_logo=None):
    team_count = min(len(df), MAX_ROWS)
    background_path = BACKGROUND_TEMPLATE_PATTERN.format(count=team_count)

    if not os.path.exists(background_path):
        raise RuntimeError(f"Background template not found: {background_path}")

    img = Image.open(background_path).convert("RGBA")
    W, H = img.size
    draw = ImageDraw.Draw(img)

    # ---------------- League logo ----------------
    logo_x, logo_y = scale_xy(LEAGUE_LOGO_CENTER[0], LEAGUE_LOGO_CENTER[1], W, H)
    logo_max = scale_len(LEAGUE_LOGO_MAX_SIZE, W, BASE_W)
    paste_logo_centered(img, league_logo, (logo_x, logo_y), logo_max)

    # ---------------- League label beside LIGA ----------------
    league_font = load_font(scale_len(130, H, BASE_H), bold=True)
    league_x, league_y = scale_xy(LEAGUE_LABEL_POS[0], LEAGUE_LABEL_POS[1], W, H)

    draw.text(
        (league_x, league_y),
        cfg["league_label"],
        font=league_font,
        fill=TEXT_LIGA_GREY,
        anchor="rm",
        stroke_width=max(1, scale_len(2, H, BASE_H)),
        stroke_fill=(0, 0, 0),
    )

    # ---------------- VETs label between LIGA and STANDINGS ----------------
    if cfg["team"].lower() == "vets":
        vets_font = load_font(scale_len(34, H, BASE_H), bold=True)
        vets_x, vets_y = scale_xy(350, 236, W, H)

        draw.text(
            (vets_x, vets_y),
            "VETERANS",
            font=vets_font,
            fill=TEXT_LIGA_GREY,
            anchor="mm",
            stroke_width=max(1, scale_len(2, H, BASE_H)),
            stroke_fill=(0, 0, 0),
        )

    # ---------------- Season label in green ribbon ----------------
    season_label = get_season_label(cfg["source"])
    season_font = load_font(scale_len(36, H, BASE_H), bold=True)
    season_x, season_y = scale_xy(SEASON_POS[0], SEASON_POS[1], W, H)

    draw.text(
        (season_x, season_y),
        season_label,
        font=season_font,
        fill=TEXT_BLACK,
        anchor="mm",
    )

    # ---------------- Table rows ----------------
    num_start_size = scale_len(24, H, BASE_H)
    team_start_size = scale_len(22, H, BASE_H)

    for i in range(team_count):
        if i >= len(df):
            break

        row = df.iloc[i]
        y = scale_len(FIRST_ROW_Y + i * ROW_H, H, BASE_H)

        team_name = row.get("Team", "")
        is_galaksia = (
            "galaksia" in str(team_name).lower()
            or "gp23" in str(team_name).lower()
        )
        row_color = GALAKSIA_GREEN if is_galaksia else TEXT_WHITE

        values = {
            "position": row.get("Position", ""),
            "team": team_name,
            "matches": row.get("Matches Played", ""),
            "wins": row.get("Wins", ""),
            "draws": row.get("Draws", ""),
            "losses": row.get("Losses", ""),
            "diff": row.get("Diff", ""),
            "points": row.get("Points", ""),
        }

        for key, value in values.items():
            # Template already contains ranking numbers 1-12.
            # Do not draw Position again.
            if key == "position":
                continue

            x = scale_len(TABLE_X_CENTERS[key], W, BASE_W)

            if key == "team":
                max_w = scale_len(TEAM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, team_start_size, min_size=9)
            else:
                max_w = scale_len(NUM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, num_start_size, min_size=8)

            draw_centered_text(
                draw,
                (x, y),
                value,
                font,
                row_color,
                stroke_width=max(1, scale_len(1, H, BASE_H)),
                stroke_fill=(0, 0, 0),
            )

    return img.convert("RGB")

def make_story_version(feed_img_path):
    feed = Image.open(feed_img_path).convert("RGB")

    bg = feed.copy()
    scale = max(STORY_W / bg.width, STORY_H / bg.height)
    bg = bg.resize((int(bg.width * scale), int(bg.height * scale)), Image.LANCZOS)

    left = (bg.width - STORY_W) // 2
    top = (bg.height - STORY_H) // 2
    bg = bg.crop((left, top, left + STORY_W, top + STORY_H))
    bg = bg.filter(ImageFilter.GaussianBlur(40))

    fg = feed.copy()
    fscale = min(STORY_W / fg.width, STORY_H / fg.height) * 0.92
    fg = fg.resize((int(fg.width * fscale), int(fg.height * fscale)), Image.LANCZOS)

    bg.paste(fg, ((STORY_W - fg.width) // 2, (STORY_H - fg.height) // 2))

    out = feed_img_path.replace(".png", "_story.png")
    bg.save(out, "PNG", quality=95)
    return out


def github_raw_url(local_path):
    rel = os.path.relpath(local_path, SCRIPT_DIR).replace("\\", "/")
    return GITHUB_REPO_RAW_BASE + rel


def load_meta_config():
    with open(META_CONFIG_FILE, "r", encoding="utf-8") as f:
        return json.load(f)


def _get_page_token(page_id, user_token):
    r = requests.get(
        "%s/me/accounts" % GRAPH,
        params={"access_token": user_token, "limit": 200},
    )
    r.raise_for_status()

    for p in r.json().get("data", []):
        if str(p.get("id")) == str(page_id):
            return p["access_token"]

    raise RuntimeError("Page %s not found in me/accounts" % page_id)


def _fb_page_photo(page_id, token, image_url, caption, published=True):
    r = requests.post(
        "%s/%s/photos" % (GRAPH, page_id),
        data={
            "url": image_url,
            "caption": caption,
            "published": "true" if published else "false",
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()


def _fb_story(page_id, token, photo_id):
    r = requests.post(
        "%s/%s/photo_stories" % (GRAPH, page_id),
        data={"photo_id": photo_id, "access_token": token},
    )
    r.raise_for_status()
    return r.json()


def _ig_publish(ig_id, token, image_url, is_story=True):
    data = {
        "image_url": image_url,
        "access_token": token,
        "media_type": "STORIES",
    }

    c = requests.post("%s/%s/media" % (GRAPH, ig_id), data=data)
    c.raise_for_status()
    creation_id = c.json()["id"]

    for _ in range(10):
        st = requests.get(
            "%s/%s" % (GRAPH, creation_id),
            params={"fields": "status_code", "access_token": token},
        )
        code = st.json().get("status_code")

        if code == "FINISHED":
            break
        if code == "ERROR":
            raise RuntimeError("IG container error: %s" % st.text)

        time.sleep(3)

    p = requests.post(
        "%s/%s/media_publish" % (GRAPH, ig_id),
        data={"creation_id": creation_id, "access_token": token},
    )
    p.raise_for_status()
    return p.json()


def post_story_to_meta(story_url, caption=""):
    cfg = load_meta_config()
    page_id = cfg["page_id"]
    ig_id = cfg["ig_user_id"]
    user_token = cfg["page_access_token"]

    if not story_url:
        raise RuntimeError("no story url; cannot post.")

    try:
        token = _get_page_token(page_id, user_token)
    except Exception as e:
        print("    [meta] could not derive Page token: %s" % e)
        token = user_token

    fb_ok = False
    ig_ok = False

    try:
        photo = _fb_page_photo(page_id, token, story_url, caption, published=False)
        _fb_story(page_id, token, photo["id"])
        print("    [meta] FB story OK")
        fb_ok = True
    except Exception as e:
        print("    [meta] FB story FAILED: %s" % e)

    try:
        _ig_publish(ig_id, user_token, story_url, is_story=True)
        print("    [meta] IG story OK")
        ig_ok = True
    except Exception as e:
        print("    [meta] IG story FAILED: %s" % e)

    return fb_ok, ig_ok


def _fb_upload_unpublished_photo(page_id, token, image_url):
    r = requests.post(
        "%s/%s/photos" % (GRAPH, page_id),
        data={
            "url": image_url,
            "published": "false",
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()["id"]


def _fb_carousel_post(page_id, token, image_urls, caption=""):
    media_ids = [
        _fb_upload_unpublished_photo(page_id, token, url)
        for url in image_urls
    ]

    attached_media = [{"media_fbid": mid} for mid in media_ids]

    r = requests.post(
        "%s/%s/feed" % (GRAPH, page_id),
        data={
            "message": caption,
            "attached_media": json.dumps(attached_media),
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()


def _ig_carousel_child(ig_id, token, image_url):
    r = requests.post(
        "%s/%s/media" % (GRAPH, ig_id),
        data={
            "image_url": image_url,
            "is_carousel_item": "true",
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()["id"]


def _ig_carousel_post(ig_id, token, image_urls, caption=""):
    child_ids = [_ig_carousel_child(ig_id, token, url) for url in image_urls]

    c = requests.post(
        "%s/%s/media" % (GRAPH, ig_id),
        data={
            "media_type": "CAROUSEL",
            "children": ",".join(child_ids),
            "caption": caption,
            "access_token": token,
        },
    )
    c.raise_for_status()
    creation_id = c.json()["id"]

    for _ in range(10):
        st = requests.get(
            "%s/%s" % (GRAPH, creation_id),
            params={"fields": "status_code", "access_token": token},
        )
        code = st.json().get("status_code")

        if code == "FINISHED":
            break
        if code == "ERROR":
            raise RuntimeError("IG carousel container error: %s" % st.text)

        time.sleep(3)

    p = requests.post(
        "%s/%s/media_publish" % (GRAPH, ig_id),
        data={"creation_id": creation_id, "access_token": token},
    )
    p.raise_for_status()
    return p.json()


def post_carousel_to_meta(image_urls, caption=""):
    cfg = load_meta_config()
    page_id = cfg["page_id"]
    ig_id = cfg["ig_user_id"]
    user_token = cfg["page_access_token"]

    if not image_urls:
        raise RuntimeError("no image urls; cannot post carousel.")

    try:
        token = _get_page_token(page_id, user_token)
    except Exception as e:
        print("    [meta] could not derive Page token: %s" % e)
        token = user_token

    fb_ok = False
    ig_ok = False

    try:
        _fb_carousel_post(page_id, token, image_urls, caption)
        print("    [meta] FB carousel OK")
        fb_ok = True
    except Exception as e:
        print("    [meta] FB carousel FAILED: %s" % e)

    try:
        _ig_carousel_post(ig_id, user_token, image_urls, caption)
        print("    [meta] IG carousel OK")
        ig_ok = True
    except Exception as e:
        print("    [meta] IG carousel FAILED: %s" % e)

    return fb_ok, ig_ok

# ---------------- VETs label between LIGA and STANDINGS ----------------
    if cfg["team"].lower() == "vets":
        vets_font = load_font(scale_len(34, H, BASE_H), bold=True)
        vets_x, vets_y = scale_xy(350, 236, W, H)

        draw.text(
            (vets_x, vets_y),
            "VETERANS",
            font=vets_font,
            fill=TEXT_LIGA_GREY,
            anchor="mm",
            stroke_width=max(1, scale_len(2, H, BASE_H)),
            stroke_fill=(0, 0, 0),
        )

    # ---------------- Season label in green ribbon ----------------
    season_label = get_season_label(cfg["source"])
    season_font = load_font(scale_len(36, H, BASE_H), bold=True)
    season_x, season_y = scale_xy(SEASON_POS[0], SEASON_POS[1], W, H)

    draw.text(
        (season_x, season_y),
        season_label,
        font=season_font,
        fill=TEXT_BLACK,
        anchor="mm",
    )

    # ---------------- Table rows ----------------
    num_start_size = scale_len(24, H, BASE_H)
    team_start_size = scale_len(22, H, BASE_H)

    for i in range(team_count):
        if i >= len(df):
            break

        row = df.iloc[i]

        y = scale_len(FIRST_ROW_Y + i * ROW_H, H, BASE_H)

        team_name = row.get("Team", "")
        is_galaksia = "galaksia" in str(team_name).lower() or "gp23" in str(team_name).lower()
        row_color = GALAKSIA_GREEN if is_galaksia else TEXT_WHITE

        values = {
            "position": row.get("Position", ""),
            "team": team_name,
            "matches": row.get("Matches Played", ""),
            "wins": row.get("Wins", ""),
            "draws": row.get("Draws", ""),
            "losses": row.get("Losses", ""),
            "diff": row.get("Diff", ""),
            "points": row.get("Points", ""),
        }

        for key, value in values.items():
            # The template already contains the ranking numbers 1-12.
            # Do not draw Position again.
            if key == "position":
                continue

            x = scale_len(TABLE_X_CENTERS[key], W, BASE_W)

            if key == "team":
                max_w = scale_len(TEAM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, team_start_size, min_size=9)
            else:
                max_w = scale_len(NUM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, num_start_size, min_size=8)

            draw_centered_text(
                draw,
                (x, y),
                value,
                font,
                row_color,
                stroke_width=max(1, scale_len(1, H, BASE_H)),
                stroke_fill=(0, 0, 0),
            )

    return img.convert("RGB")


# ============================================================
# MAIN
# ============================================================
def run_ranking_image_generator():
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    drive = get_drive_service()
    logo_files = list_folder_files(drive, LOGOS_FOLDER_ID)
    sync_backgrounds_from_drive(drive)

    print(f"[{time.strftime('%H:%M:%S')}] Initializing Chrome...")
    driver = webdriver.Chrome(
        service=Service(ChromeDriverManager().install()),
        options=chrome_options,
    )

    try:
        generated = []

        for cfg in RANKING_CONFIGS:
            print("\n" + "=" * 50)
            print(f"[{time.strftime('%H:%M:%S')}] Processing {cfg['team']} ranking")

            if cfg["source"] == "pkfl":
                df, league_label = scrape_pkfl_ranking_table(driver, cfg["url"])
                cfg["league_label"] = league_label
            else:
                df = scrape_psmf_ranking_table(driver, cfg["url"])

            if df.empty:
                print(f"  Warning: No ranking data found for {cfg['team']}")
                continue

            logo_label = "PKFL" if cfg["source"] == "pkfl" else "PSMF"
            league_logo = load_league_logo(drive, logo_files, logo_label)

            img = draw_ranking_image(df, cfg, league_logo=league_logo)

            out_name = f"{cfg['team']}_ranking.png".replace(" ", "_")
            out_path = os.path.join(OUTPUT_DIR, out_name)
            img.save(out_path, "PNG", quality=95)

            story_path = make_story_version(out_path)

            generated.append({
                "team": cfg["team"],
                "path": out_path,
                "story_path": story_path,
            })

            print(f"  ✓ Saved: {out_path}")
            print(f"  ✓ Saved story: {story_path}")

        # Enforce exact posting order
        by_team = {g["team"]: g for g in generated}
        ordered = [by_team[t] for t in POST_ORDER if t in by_team]

        with open(MANIFEST_FILE, "w", encoding="utf-8") as f:
            json.dump(ordered, f, ensure_ascii=False, indent=2)

        print("\n" + "=" * 50)
        print(f"[{time.strftime('%H:%M:%S')}] Generation complete. {len(ordered)} ranking image(s) ready.")
        for g in ordered:
            print(f"  - {g['team']}: {g['path']}")

    finally:
        driver.quit()
        print(f"[{time.strftime('%H:%M:%S')}] Session closed.")

def post_rankings_from_manifest():
    if not os.path.exists(MANIFEST_FILE):
        raise RuntimeError(f"Manifest not found: {MANIFEST_FILE}. Run --generate-only first.")

    with open(MANIFEST_FILE, "r", encoding="utf-8") as f:
        items = json.load(f)

    by_team = {item["team"]: item for item in items}
    ordered = [by_team[t] for t in POST_ORDER if t in by_team]

    if not ordered:
        print("No ranking images found in manifest.")
        return

    for item in ordered:
        if not os.path.exists(item["path"]):
            raise RuntimeError(f"Missing ranking image: {item['path']}")
        if not os.path.exists(item["story_path"]):
            raise RuntimeError(f"Missing ranking story image: {item['story_path']}")

    print("Posting rankings in order:")
    for item in ordered:
        print(f"  - {item['team']}")

    carousel_urls = [github_raw_url(item["path"]) for item in ordered]

    caption = "League Standings"

    reel_fb_ok, reel_ig_ok = post_carousel_to_meta(carousel_urls, caption=caption)

    story_results = []

    for item in ordered:
        print(f"--- Posting story {item['team']} ---")
        story_url = github_raw_url(item["story_path"])
        fb_ok, ig_ok = post_story_to_meta(story_url)
        story_results.append((fb_ok, ig_ok))

    all_fb_ok = reel_fb_ok and all(r[0] for r in story_results)
    all_ig_ok = reel_ig_ok and all(r[1] for r in story_results)
    fully_sent = all_fb_ok and all_ig_ok

    if fully_sent:
        print("Rankings posted successfully to FB and IG.")
    else:
        print(f"Rankings NOT fully posted (FB ok={all_fb_ok}, IG ok={all_ig_ok}).")

    # Cleanup local files regardless of success, same as match results script
    for item in ordered:
        for p in (item.get("path"), item.get("story_path")):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except Exception as e:
                    print(f"  [cleanup] could not remove {p}: {e}")

    print("Posting complete.")


GENERATE_ONLY = "--generate-only" in sys.argv
POST_ONLY = "--post-only" in sys.argv

if not GENERATE_ONLY and not POST_ONLY:
    print("ERROR: pass either --generate-only or --post-only.")
    sys.exit(1)

if __name__ == "__main__":
    if GENERATE_ONLY:
        run_ranking_image_generator()
    elif POST_ONLY:
        post_rankings_from_manifest()
