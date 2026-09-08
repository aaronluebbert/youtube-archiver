#!/usr/bin/env python3
"""
youtube archive tool - gui with queue, cancel, robust url parsing,
fast metadata via the youtube data api, edge-case handling, a
source-video link prepended to the description, and clean numeric
progress reporting for both download and upload
"""

import os
import pickle
import queue
import re
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import parse_qs, urlparse

import tkinter as tk
from tkinter import ttk, messagebox

import requests
import yt_dlp
from google.auth.transport.requests import Request
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from googleapiclient.http import MediaFileUpload

SCOPES = [
    "https://www.googleapis.com/auth/youtube.upload",
    "https://www.googleapis.com/auth/youtube",
]
CLIENT_SECRETS_FILE = "credentials.json"
TOKEN_FILE = "token.pickle"
DOWNLOAD_DIR = "downloads"
MAX_UPLOAD_RETRIES = 5
YOUTUBE_DESCRIPTION_LIMIT = 5000  # youtube's hard cap on description length
UPLOAD_CHUNK_SIZE = 10 * 1024 * 1024  # 10mb - a real chunk size is required for incremental progress at all


class JobCancelled(Exception):
    # raised internally to unwind a job's pipeline early
    pass


# ---------- shared auth cache (not per-job) ----------

creds_lock = threading.Lock()
_cached_creds = None


def get_credentials():
    global _cached_creds
    with creds_lock:
        if _cached_creds and _cached_creds.valid:
            return _cached_creds

        creds = None
        if os.path.exists(TOKEN_FILE):
            with open(TOKEN_FILE, "rb") as f:
                creds = pickle.load(f)

        if not creds or not creds.valid:
            if creds and creds.expired and creds.refresh_token:
                creds.refresh(Request())
            else:
                flow = InstalledAppFlow.from_client_secrets_file(CLIENT_SECRETS_FILE, SCOPES)
                creds = flow.run_local_server(port=0)
            with open(TOKEN_FILE, "wb") as f:
                pickle.dump(creds, f)

        _cached_creds = creds
        return creds


def get_youtube_service():
    creds = get_credentials()
    return build("youtube", "v3", credentials=creds)


# ---------- url parsing ----------

VIDEO_ID_PATTERN = re.compile(r"[0-9A-Za-z_-]{11}")


def extract_video_id(raw_url):
    # handles every shape a pasted youtube link tends to come in:
    # watch urls with extra params in any order (list=, t=, si=,
    # index=), youtu.be short links (with or without a trailing
    # timestamp/tracking param), shorts/embed/live paths, and a
    # bare 11-character id pasted with no url at all
    text = raw_url.strip()

    if VIDEO_ID_PATTERN.fullmatch(text):
        return text

    parsed = urlparse(text if "://" in text else f"https://{text}")
    host = (parsed.netloc or "").lower()

    if "youtu.be" in host:
        first_segment = parsed.path.strip("/").split("/")[0]
        if VIDEO_ID_PATTERN.fullmatch(first_segment):
            return first_segment

    query = parse_qs(parsed.query)
    if "v" in query and VIDEO_ID_PATTERN.fullmatch(query["v"][0]):
        return query["v"][0]

    path_match = re.search(r"/(?:shorts|embed|live)/([0-9A-Za-z_-]{11})", parsed.path)
    if path_match:
        return path_match.group(1)

    raise ValueError(
        f"could not find a video id in: {raw_url}\n"
        "paste a single video link (not a playlist-only link) or just the 11-character video id"
    )


# ---------- core pipeline ----------

def fetch_metadata(youtube, video_id):
    # request contentDetails alongside snippet so the video's duration
    # is available too, not just title/description/tags
    resp = youtube.videos().list(part="snippet,contentDetails", id=video_id).execute()
    items = resp.get("items", [])
    if not items:
        raise ValueError("video not found, private, deleted, or not accessible with this account")
    snippet = items[0]["snippet"]
    snippet["duration_minutes"] = parse_duration_minutes(items[0]["contentDetails"]["duration"])
    return snippet

DURATION_PATTERN = re.compile(r"PT(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?")

def parse_duration_minutes(iso_duration):
    # youtube returns duration in iso 8601 format like "PT1H2M10S" -
    # this pulls out hours/minutes/seconds and returns the total in minutes
    match = DURATION_PATTERN.fullmatch(iso_duration or "")
    if not match:
        return None
    hours, minutes, seconds = (int(g) if g else 0 for g in match.groups())
    return hours * 60 + minutes + seconds / 60


def check_archivable(snippet):
    # a currently-live or not-yet-started broadcast has no finished
    # file to download yet - catch this up front with a clear message
    live_status = snippet.get("liveBroadcastContent", "none")
    if live_status == "live":
        raise ValueError("this video is currently live - wait until the broadcast ends and becomes a normal upload")
    if live_status == "upcoming":
        raise ValueError("this video is a scheduled premiere/stream that hasn't started yet")


def build_description(video_id, original_description):
    # prepend the source link, then fit as much of the original
    # description as still fits under youtube's 5000-char limit
    prefix = f"Original video: https://youtu.be/{video_id}\n\n"
    available = YOUTUBE_DESCRIPTION_LIMIT - len(prefix)
    if available <= 0:
        return prefix[:YOUTUBE_DESCRIPTION_LIMIT]
    return prefix + original_description[:available]


def download_thumbnail(snippet, video_id, out_dir):
    thumbnails = snippet.get("thumbnails", {})
    thumb_url = None
    for size in ("maxres", "standard", "high", "medium", "default"):
        if size in thumbnails:
            thumb_url = thumbnails[size]["url"]
            break
    if not thumb_url:
        return None
    resp = requests.get(thumb_url, timeout=30)
    resp.raise_for_status()
    path = os.path.join(out_dir, f"{video_id}_thumb.jpg")
    with open(path, "wb") as f:
        f.write(resp.content)
    return path


def download_video(video_id, out_dir, progress_hook):
    # build a clean canonical url from the id itself rather than
    # trusting the user's raw pasted url - this guarantees no stray
    # &list=, &si=, or &t= param can send yt-dlp down the playlist/tab
    # extraction path instead of the single-video path
    clean_url = f"https://www.youtube.com/watch?v={video_id}"

    ydl_opts = {
        "format": "bestvideo+bestaudio/best",
        "merge_output_format": "mkv",  # holds any codec combo without re-encoding
        "outtmpl": os.path.join(out_dir, f"{video_id}.%(ext)s"),
        "progress_hooks": [progress_hook],
        "noplaylist": True,
        "socket_timeout": 30,
        "retries": 10,
        "fragment_retries": 10,
        "quiet": True,
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        ydl.download([clean_url])
    merged = os.path.join(out_dir, f"{video_id}.mkv")
    if not os.path.exists(merged):
        raise FileNotFoundError(f"expected merged file not found: {merged}")
    return merged


def upload_video(youtube, video_path, video_id, snippet, thumb_path, log, status, cancel_event):
    body_snippet = {
        "title": snippet.get("title", "Untitled"),
        "description": build_description(video_id, snippet.get("description", "") or ""),
        "tags": snippet.get("tags", []) or [],
        "categoryId": snippet.get("categoryId", "22"),
    }

    if snippet.get("defaultLanguage"):
        body_snippet["defaultLanguage"] = snippet["defaultLanguage"]
        body_snippet["defaultAudioLanguage"] = snippet["defaultLanguage"]

    body = {
        "snippet": body_snippet,
        "status": {
            "privacyStatus": "private",
            "selfDeclaredMadeForKids": False,
        },
    }

    # a real chunk size (not -1) is required to get any incremental
    # progress at all - chunksize=-1 sends the whole file in one
    # request, so there was nothing to report until it was already done
    media = MediaFileUpload(video_path, chunksize=UPLOAD_CHUNK_SIZE, resumable=True, mimetype="video/x-matroska")
    request = youtube.videos().insert(part="snippet,status", body=body, media_body=media)

    response = None
    retry_count = 0
    upload_start = time.time()
    while response is None:
        if cancel_event.is_set():
            raise JobCancelled("cancelled during upload")
        try:
            chunk_status, response = request.next_chunk()
            if chunk_status:
                elapsed_min = (time.time() - upload_start) / 60
                percent = chunk_status.progress() * 100
                status(f"Uploading - {elapsed_min:.1f} min - {percent:.2f}%")
            retry_count = 0
        except HttpError as e:
            # 5xx errors are usually transient - a brief backoff and
            # retry clears most of them without any input needed
            if e.resp.status in (500, 502, 503, 504) and retry_count < MAX_UPLOAD_RETRIES:
                retry_count += 1
                wait = 2 ** retry_count
                log(f"transient upload error (status {e.resp.status}), retrying in {wait}s...")
                time.sleep(wait)
                continue
            raise

    video_id_result = response["id"]
    log(f"uploaded as https://youtu.be/{video_id_result} (category: {body_snippet['categoryId']})")

    if cancel_event.is_set():
        raise JobCancelled("cancelled after upload finished, before thumbnail")

    if thumb_path:
        youtube.thumbnails().set(videoId=video_id_result, media_body=MediaFileUpload(thumb_path)).execute()
        log("thumbnail set")

    return video_id_result


def process_job(job_id, video_id, gui_queue, cancel_event):
    def log(msg):
        gui_queue.put(("log", job_id, msg))

    def status(s):
        gui_queue.put(("status", job_id, s))

    def check_cancel():
        if cancel_event.is_set():
            raise JobCancelled()

    video_path = None
    thumb_path = None

    try:
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
        check_cancel()

        status("Authenticating")
        youtube = get_youtube_service()
        check_cancel()

        status("Fetching metadata")
        snippet = fetch_metadata(youtube, video_id)
        check_archivable(snippet)
        duration = snippet.get("duration_minutes")
        if duration is not None:
            log(f"video length: {duration:.2f} min")
        check_cancel()

        status("Fetching thumbnail")
        thumb_path = download_thumbnail(snippet, video_id, DOWNLOAD_DIR)
        check_cancel()

        def hook(d):
            if cancel_event.is_set():
                raise JobCancelled("cancelled during download")
            if d["status"] == "downloading":
                # compute from raw numbers instead of yt-dlp's
                # pre-formatted _percent_str, which can carry
                # terminal-only control characters
                downloaded = d.get("downloaded_bytes", 0)
                total = d.get("total_bytes") or d.get("total_bytes_estimate")
                elapsed_min = d.get("elapsed", 0) / 60
                if total:
                    percent = (downloaded / total) * 100
                    status(f"Downloading - {elapsed_min:.1f} min - {percent:.2f}%")
                else:
                    status(f"Downloading - {elapsed_min:.1f} min")
            elif d["status"] == "finished":
                status("Merging")

        status("Downloading")
        video_path = download_video(video_id, DOWNLOAD_DIR, hook)
        check_cancel()

        status("Uploading")
        upload_video(youtube, video_path, video_id, snippet, thumb_path, log, status, cancel_event)

        status("Cleaning up")
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                os.remove(p)

        status("Done")

    except JobCancelled:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        status("Cancelled")
        log("job cancelled by user")

    except HttpError as e:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        # surface quota exhaustion as its own distinct status rather
        # than a generic error, since the fix is "wait," not "debug"
        if e.resp.status == 403 and "quota" in str(e).lower():
            status("Quota Exceeded")
            log("daily youtube upload quota hit - resets at midnight pacific time")
        else:
            status("Error")
            log(f"error: {e}")

    except Exception as e:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        status("Error")
        log(f"error: {e}")

        def hook(d):
            if cancel_event.is_set():
                raise JobCancelled("cancelled during download")
            if d["status"] == "downloading":
                # compute from raw numbers instead of yt-dlp's
                # pre-formatted _percent_str, which can carry
                # terminal-only control characters
                downloaded = d.get("downloaded_bytes", 0)
                total = d.get("total_bytes") or d.get("total_bytes_estimate")
                elapsed_min = d.get("elapsed", 0) / 60
                if total:
                    percent = (downloaded / total) * 100
                    status(f"Downloading - {elapsed_min:.1f} min - {percent:.2f}%")
                else:
                    status(f"Downloading - {elapsed_min:.1f} min")
            elif d["status"] == "finished":
                status("Merging")

        status("Downloading")
        video_path = download_video(video_id, DOWNLOAD_DIR, hook)
        check_cancel()

        status("Uploading")
        upload_video(youtube, video_path, video_id, snippet, thumb_path, log, status, cancel_event)

        status("Cleaning up")
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                os.remove(p)

        status("Done")

    except JobCancelled:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        status("Cancelled")
        log("job cancelled by user")

    except HttpError as e:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        # surface quota exhaustion as its own distinct status rather
        # than a generic error, since the fix is "wait," not "debug"
        if e.resp.status == 403 and "quota" in str(e).lower():
            status("Quota Exceeded")
            log("daily youtube upload quota hit - resets at midnight pacific time")
        else:
            status("Error")
            log(f"error: {e}")

    except Exception as e:
        for p in (video_path, thumb_path):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except OSError:
                    pass
        status("Error")
        log(f"error: {e}")


# ---------- gui ----------

class ArchiveApp:
    def __init__(self, root):
        self.root = root
        root.title("youtube archiver")
        root.geometry("700x480")

        frame = ttk.Frame(root, padding=12)
        frame.pack(fill="both", expand=True)

        top = ttk.Frame(frame)
        top.pack(fill="x")
        ttk.Label(top, text="YouTube URL:").pack(anchor="w")
        entry_row = ttk.Frame(top)
        entry_row.pack(fill="x", pady=(2, 0))
        self.url_entry = ttk.Entry(entry_row)
        self.url_entry.pack(side="left", fill="x", expand=True)
        self.url_entry.bind("<Return>", lambda e: self.add_to_queue())
        ttk.Button(entry_row, text="Add to Queue", command=self.add_to_queue).pack(side="left", padx=(6, 0))

        conc_row = ttk.Frame(top)
        conc_row.pack(fill="x", pady=(6, 0))
        ttk.Label(conc_row, text="Concurrent workers:").pack(side="left")
        self.worker_var = tk.IntVar(value=2)
        ttk.Spinbox(conc_row, from_=1, to=5, width=4, textvariable=self.worker_var).pack(side="left", padx=(6, 0))
        ttk.Label(
            conc_row,
            text="(set before adding your first video - upload quota caps you around 6/day regardless)",
            foreground="gray",
        ).pack(side="left", padx=(8, 0))

        ttk.Label(frame, text="Queue:").pack(anchor="w", pady=(10, 2))
        table_frame = ttk.Frame(frame)
        table_frame.pack(fill="both", expand=True)

        self.tree = ttk.Treeview(table_frame, columns=("url", "status", "action"), show="headings", height=8)
        self.tree.heading("url", text="URL")
        self.tree.heading("status", text="Status")
        self.tree.heading("action", text="")
        self.tree.column("url", width=380)
        self.tree.column("status", width=180)
        self.tree.column("action", width=80, anchor="center")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.bind("<Button-1>", self.on_tree_click)

        scroll = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        scroll.pack(side="left", fill="y")
        self.tree.configure(yscrollcommand=scroll.set)

        ttk.Label(frame, text="Log:").pack(anchor="w", pady=(10, 2))
        self.log_box = tk.Text(frame, height=10, state="disabled", wrap="word")
        self.log_box.pack(fill="both", expand=True)

        self.gui_queue = queue.Queue()
        self.executor = None
        self.jobs = {}  # job_id -> {"cancel_event", "future", "url", "video_id"}
        self.active_video_ids = set()  # guards against queuing the same video twice
        self.root.after(100, self.poll_gui_queue)

    def log(self, msg):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", msg + "\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def poll_gui_queue(self):
        try:
            while True:
                kind, job_id, payload = self.gui_queue.get_nowait()
                if kind == "status":
                    self.tree.set(job_id, "status", payload)
                    if payload in ("Done", "Error", "Cancelled", "Quota Exceeded"):
                        self.tree.set(job_id, "action", "-")
                        job = self.jobs.get(job_id)
                        if job:
                            self.active_video_ids.discard(job["video_id"])
                elif kind == "log":
                    url = self.tree.set(job_id, "url")
                    self.log(f"[{url[-25:]}] {payload}")
        except queue.Empty:
            pass
        self.root.after(100, self.poll_gui_queue)

    def on_tree_click(self, event):
        region = self.tree.identify("region", event.x, event.y)
        if region != "cell":
            return
        col = self.tree.identify_column(event.x)
        row = self.tree.identify_row(event.y)
        if not row:
            return
        if col == "#3":  # action column
            self.cancel_job(row)

    def cancel_job(self, job_id):
        job = self.jobs.get(job_id)
        if not job or job["cancel_event"].is_set():
            return

        current_status = self.tree.set(job_id, "status")
        if current_status in ("Done", "Error", "Cancelled", "Quota Exceeded"):
            return

        job["cancel_event"].set()

        if job["future"].cancel():
            self.tree.set(job_id, "status", "Cancelled")
            self.tree.set(job_id, "action", "-")
            self.active_video_ids.discard(job["video_id"])
            self.log(f"cancelled queued job before it started: {job['url']}")
        else:
            self.tree.set(job_id, "status", "Cancelling")
            self.tree.set(job_id, "action", "-")
            self.log(f"cancel requested: {job['url']} (stopping at next checkpoint)")

    def add_to_queue(self):
        url = self.url_entry.get().strip()
        if not url:
            messagebox.showwarning("Missing URL", "Paste a YouTube URL first.")
            return

        try:
            video_id = extract_video_id(url)
        except ValueError as e:
            messagebox.showerror("Invalid URL", str(e))
            return

        if video_id in self.active_video_ids:
            messagebox.showwarning("Already Queued", "This video is already queued or processing.")
            return

        if self.executor is None:
            workers = max(1, self.worker_var.get())
            self.executor = ThreadPoolExecutor(max_workers=workers)
            self.log(f"queue started with {workers} concurrent worker(s)")

        job_id = str(uuid.uuid4())
        self.tree.insert("", "end", iid=job_id, values=(url, "Queued", "Cancel"))
        self.url_entry.delete(0, "end")

        self.active_video_ids.add(video_id)
        cancel_event = threading.Event()
        future = self.executor.submit(process_job, job_id, video_id, self.gui_queue, cancel_event)
        self.jobs[job_id] = {"cancel_event": cancel_event, "future": future, "url": url, "video_id": video_id}


if __name__ == "__main__":
    root = tk.Tk()
    app = ArchiveApp(root)
    root.mainloop()
    