import os
import re
import sys
import json
import time
import math
import queue
import shutil
import string
import logging
import threading
import hashlib, tempfile, os
if getattr(sys, 'frozen', False):  # running from PyInstaller .exe
    ffmpeg_path = os.path.join(sys._MEIPASS, "ffmpeg.exe")
    os.environ["PATH"] = ffmpeg_path + os.pathsep + os.environ["PATH"]
    
try:
    from PIL import Image, ImageTk
    from io import BytesIO
    import requests
    THUMB_OK = True
except Exception:
    THUMB_OK = False

import subprocess
import webbrowser
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from concurrent.futures import ThreadPoolExecutor, as_completed

try:
    from yt_dlp import YoutubeDL
except Exception as e:
    raise SystemExit("yt-dlp is required. Install with: pip install yt-dlp\n" + str(e))

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    DND_AVAILABLE = True
except Exception:
    TkinterDnD = None
    DND_FILES = None
    DND_AVAILABLE = False

try:
    from plyer import notification
    PLYER_AVAILABLE = True
except Exception:
    PLYER_AVAILABLE = False

try:
    from PIL import Image, ImageTk
    from io import BytesIO
    import requests
    PIL_AVAILABLE = True
except Exception:
    PIL_AVAILABLE = False

APP_NAME = "Viora By Khaled ( Monkey Ð Luffy )"
APP_VERSION = "v1.1"
CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".ytdl_gui_settings.json")
HISTORY_FILE = os.path.join(os.path.expanduser("~"), ".ytdl_gui_history.json")
LOG_FILE = os.path.join(os.path.expanduser("~"), ".ytdl_gui.log")

DEFAULT_SETTINGS = {
    "download_folder": os.path.join(os.path.expanduser("~"), "Downloads"),
    "dark_mode": False,
    "enable_subtitles": False,
    "subtitle_langs": ["en"],
    "burn_subtitles": False,
    "audio_only": False,
    "audio_format": "mp3",
    "filename_template": "%(title)s.%(ext)s",
    "concurrent_downloads": 1,
    "clipboard_autofill": True,
    "max_download_speed": 0,
    "enable_playlist": False,
}

TASK_NEW = "NEW"
TASK_QUEUED = "QUEUED"
TASK_RUNNING = "RUNNING"
TASK_PAUSED = "PAUSED"
TASK_DONE = "DONE"
TASK_FAILED = "FAILED"
TASK_CANCELED = "CANCELED"

USER_CANCEL_SIGNAL = "__USER_CANCEL__"
USER_PAUSE_SIGNAL = "__USER_PAUSE__"

logging.basicConfig(
    filename=LOG_FILE,
    filemode="a",
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(threadName)s: %(message)s",
)
logger = logging.getLogger(APP_NAME)

def sanitize_filename(name: str) -> str:
    allowed = f"-_.()[] %s%s" % (string.ascii_letters, string.digits)
    return "".join(c for c in name if c in allowed)

YDL_URL_RE = re.compile(r"https?://")
def is_valid_url(url: str) -> bool:
    return bool(YDL_URL_RE.match(url or ""))

def human_bytes(n):
    try:
        n = float(n)
    except Exception:
        return "-"
    units = ["B", "KB", "MB", "GB", "TB"]
    i = 0
    while n >= 1024 and i < len(units) - 1:
        n /= 1024.0
        i += 1
    return f"{n:.1f} {units[i]}"

def human_eta(seconds):
    if not seconds or seconds < 0:
        return "-"
    seconds = int(seconds)
    h, m = divmod(seconds, 3600)
    m, s = divmod(m, 60)
    return f"{h}h {m}m {s}s" if h else f"{m}m {s}s" if m else f"{s}s"

def notify(title, message):
    if PLYER_AVAILABLE:
        try:
            notification.notify(title=title, message=message, app_name=APP_NAME, timeout=5)
        except Exception:
            pass

class Persistence:
    @staticmethod
    def load_settings():
        data = DEFAULT_SETTINGS.copy()
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    data.update(json.load(f) or {})
            except Exception as e:
                logger.exception("Failed to load settings: %s", e)
        return data

    @staticmethod
    def save_settings(settings: dict):
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(settings, f, indent=2)
        except Exception as e:
            logger.exception("Failed to save settings: %s", e)

    @staticmethod
    def append_history(entry: dict):
        try:
            history = []
            if os.path.exists(HISTORY_FILE):
                with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                    history = json.load(f)
            history.append(entry)
            with open(HISTORY_FILE, "w", encoding="utf-8") as f:
                json.dump(history[-1000:], f, indent=2)
        except Exception as e:
            logger.exception("Failed to write history: %s", e)

    @staticmethod
    def read_history():
        try:
            if os.path.exists(HISTORY_FILE):
                with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                    return json.load(f)
        except Exception as e:
            logger.exception("Failed to read history: %s", e)
        return []

class DownloadTask:
    _id_counter = 0

    def __init__(self, url: str, audio_only=False, format_id: str = None):
        DownloadTask._id_counter += 1
        self.id = DownloadTask._id_counter
        self.url = url.strip()
        self.audio_only = bool(audio_only)
        self.format_id = format_id
        self.title = "-"
        self.filename = None
        self.status = TASK_NEW
        self.progress = 0.0
        self.speed = "-"
        self.eta = "-"
        self.size = "-"
        self.error = None
        self.thumb_path = None          
        self.created = time.time()
        self.cancel_flag = threading.Event()
        self.pause_flag = threading.Event()
        self.retry_count = 0

class DownloadWorker(threading.Thread):
    def __init__(self, task_queue: queue.Queue, gui_callback, settings_provider):
        super().__init__(daemon=True, name=f"Downloader-{threading.get_ident()}")
        self.task_queue = task_queue
        self.gui_callback = gui_callback
        self.settings_provider = settings_provider
        self._stop = threading.Event()
        self.current_task = None

    def stop(self):
        self._stop.set()
        try:
            self.task_queue.put_nowait(None)
        except Exception:
            pass

    def run(self):
        """Download using yt-dlp *in-process* (no subprocess)."""
        import yt_dlp

        while not self._stop.is_set():
            try:
                task: DownloadTask = self.task_queue.get(timeout=0.2)
            except queue.Empty:
                continue
            if task is None:
                break
            if getattr(task, "status", None) == TASK_CANCELED:
                self.task_queue.task_done()
                continue

            self.current_task = task
            settings = self.settings_provider()

            # fetch title (non-blocking)
            try:
                with yt_dlp.YoutubeDL({"quiet": True}) as ydl:
                    info = ydl.extract_info(task.url, download=False)
                    task.title = info.get("title", "-")
            except Exception as e:
                logger.warning("Could not fetch metadata for %s: %s", task.url, e)

            task.status = TASK_RUNNING
            task.pause_flag.clear()
            task.cancel_flag.clear()
            self.gui_callback("update_task", task)

            # -----------------------------------------------------------------
            # Build yt-dlp options
            # -----------------------------------------------------------------
            outtmpl = os.path.abspath(
                os.path.join(settings["download_folder"], settings["filename_template"])
            )

            ydl_opts = {
                "outtmpl": outtmpl,
                "noplaylist": not settings.get("enable_playlist", False),
                "writesubtitles": settings.get("enable_subtitles", False),
                "subtitleslangs": settings.get("subtitle_langs") or ["en"],
                "embedsubtitles": settings.get("burn_subtitles", False),
                "format": task.format_id or ("bestaudio/best"
                                             if (task.audio_only or settings.get("audio_only"))
                                             else "bestvideo+bestaudio/best"),
            }

            if settings.get("max_download_speed", 0) > 0:
                ydl_opts["ratelimit"] = settings["max_download_speed"] * 1024  # KB→bytes

            if task.audio_only or settings.get("audio_only"):
                ydl_opts.update({
                    "extractaudio": True,
                    "audioformat": settings.get("audio_format", "mp3"),
                    "audioquality": "192K",
                })

            # -----------------------------------------------------------------
            # Progress / cancel / pause handling
            # -----------------------------------------------------------------
            def progress_hook(d):
                if task.cancel_flag.is_set():
                    raise yt_dlp.utils.DownloadError("__USER_CANCEL__")
                if task.pause_flag.is_set():
                    raise yt_dlp.utils.DownloadError("__USER_PAUSE__")

                if d["status"] == "downloading":
                    # extract numeric values
                    total        = d.get("total_bytes") or d.get("total_bytes_estimate", 0)
                    downloaded   = d.get("downloaded_bytes", 0)
                    speed_bps    = d.get("speed", 0) or 0
                    eta_seconds  = d.get("eta", None)

                    if total:
                        task.progress = min(100.0, downloaded * 100.0 / total)
                    else:
                        task.progress = 0.0

                    task.speed = human_bytes(speed_bps) + "/s" if speed_bps else "-"
                    task.eta   = human_eta(eta_seconds) if eta_seconds else "-"

                    self.gui_callback("update_task", task)

            ydl_opts["progress_hooks"] = [progress_hook]

            # -----------------------------------------------------------------
            # Do the download
            # -----------------------------------------------------------------
            try:
                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    ydl.download([task.url])
                task.status = TASK_DONE
                Persistence.append_history({
                    "title": task.title,
                    "url": task.url,
                    "file": ydl.prepare_filename(ydl.extract_info(task.url, download=False)),
                    "when": time.time(),
                    "audio_only": task.audio_only or settings.get("audio_only"),
                    "subs": settings.get("enable_subtitles"),
                })
            except yt_dlp.utils.DownloadError as e:
                if "__USER_CANCEL__" in str(e):
                    task.status = TASK_CANCELED
                elif "__USER_PAUSE__" in str(e):
                    task.status = TASK_PAUSED
                else:
                    task.status = TASK_FAILED
                    task.error = str(e)
            except Exception as e:
                task.status = TASK_FAILED
                task.error = str(e)
            finally:
                # remove partial file on cancel
                if task.status == TASK_CANCELED:
                    try:
                        with yt_dlp.YoutubeDL({"quiet": True}) as ydl:
                            info = ydl.extract_info(task.url, download=False)
                        real_path = ydl.prepare_filename(info)
                        if task.audio_only or settings.get("audio_only"):
                            base, _ = os.path.splitext(real_path)
                            real_path = base + "." + settings.get("audio_format", "mp3")
                        if os.path.isfile(real_path):
                            os.remove(real_path)
                            logger.info("Deleted partial file: %s", real_path)
                    except Exception as e:
                        logger.warning("Could not delete partial file: %s", e)

                self.gui_callback("update_task", task)
                self.task_queue.task_done()

class App:
    def __init__(self):
        self.settings = Persistence.load_settings()
        self.task_queue = queue.Queue()
        self.tasks = {}
        self.workers = []
        self.clipboard_cache = ""
        self._thumb_cache = {}     

        if DND_AVAILABLE and TkinterDnD is not None:
            self.root = TkinterDnD.Tk()
        else:
            self.root = tk.Tk()
        self.root.title(f"{APP_NAME} {APP_VERSION}")
        self.root.geometry("1200x700")
        self.root.minsize(1000, 500)

        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except Exception:
            pass

        self.build_menu()
        self.build_topbar()
        self.build_task_list()
        self.build_controls()
        self.apply_theme(self.settings.get("dark_mode", True))
        self.init_workers()

        if DND_AVAILABLE and TkinterDnD is not None:
            try:
                self.root.drop_target_register(DND_FILES)
                self.root.dnd_bind('<<Drop>>', self.on_drop)
            except Exception:
                pass

        if self.settings.get("clipboard_autofill", True):
            self.root.after(800, self.clipboard_watcher)

        self.update_folder_label()

    def save_settings(self):
        """Persist the current settings to disk."""
        Persistence.save_settings(self.settings)
    
    def _thumb_folder(self):
        f = os.path.join(tempfile.gettempdir(), "ytdl_thumbs")
        os.makedirs(f, exist_ok=True)
        return f

    def _fetch_thumbnail(self, url):
        if not PIL_AVAILABLE:
            return None
        try:
            with YoutubeDL({"quiet": True}) as ydl:
                info = ydl.extract_info(url, download=False)
            thumb_url = info.get("thumbnail")
            if not thumb_url:
                return None

            fname = hashlib.md5(url.encode()).hexdigest() + ".jpg"
            path = os.path.join(self._thumb_folder(), fname)

            if os.path.isfile(path):
                return path

            resp = requests.get(thumb_url, timeout=8, headers={"User-Agent": "Mozilla/5.0"})
            resp.raise_for_status()
            img = Image.open(BytesIO(resp.content)).convert("RGB").resize((90, 50), Image.LANCZOS)
            img.save(path, "JPEG", quality=90)
            return path
        except Exception as e:
            logger.debug("Thumbnail fetch failed: %s", e)
            return None

    def _set_thumb(self, task_id, path):
        """Insert image into tree cell."""
        if not os.path.isfile(path):
            return
        if str(task_id) not in self._thumb_cache:
            self._thumb_cache[str(task_id)] = ImageTk.PhotoImage(file=path)
        self.tree.set(str(task_id), "thumb", "")
        self.tree.item(str(task_id), image=self._thumb_cache[str(task_id)])

    def cancel_all(self):
        """Cancel every task and delete its partial file."""
        killed = 0

        for task in self.tasks.values():
            if task.status in (TASK_RUNNING, TASK_PAUSED, TASK_QUEUED, TASK_FAILED):
                task.cancel_flag.set()
                killed += 1

        for w in self.workers:
            task = w.current_task
            if task and task.status == TASK_RUNNING and hasattr(task, "_proc"):
                try:
                    task._proc.kill()
                    task._proc.wait(timeout=2)
                except Exception:
                    pass

        settings = self.get_settings()
        outtmpl = os.path.join(
            settings["download_folder"],
            settings["filename_template"]
        )
        for task in list(self.tasks.values()):
            try:
                from yt_dlp import YoutubeDL
                ydl = YoutubeDL({"outtmpl": outtmpl, "quiet": True})
                info = ydl.extract_info(task.url, download=False)
                real_path = ydl.prepare_filename(info)
                if task.audio_only or settings.get("audio_only"):
                    base, _ = os.path.splitext(real_path)
                    real_path = base + "." + settings.get("audio_format", "mp3")
                if os.path.isfile(real_path):
                    os.remove(real_path)
                    logger.info("Deleted: %s", real_path)
            except Exception as e:
                logger.warning("Could not delete file for task %s: %s", task.id, e)

            task.status = TASK_CANCELED
            self._update_task_row(task)

        self.status(f"Cancelled {killed} task(s) and deleted partial files.")

    def status(self, text):
        self.status_var.set(str(text))
        
    def get_settings(self):
        return dict(self.settings)
    
    def update_folder_label(self):
        self.folder_label.config(text=f"Download Folder: {self.settings.get('download_folder', os.getcwd())}")

    def toggle_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Nothing selected", "Please click a task first.")
            return
        task_id = int(sel[0])
        task = self.tasks[task_id]

        if task.status == TASK_RUNNING:
            task.pause_flag.set()
            task.status = TASK_PAUSED
            self.status(f"Paused #{task_id}")
        elif task.status == TASK_PAUSED:
            task.pause_flag.clear()
            task.status = TASK_QUEUED
            self.task_queue.put(task)
            self.status(f"Resumed #{task_id}")
        else:
            messagebox.showinfo("Cannot toggle", "Task is not running or paused.")
        self._update_task_row(task)

    def init_workers(self):
        num_workers = self.settings.get("concurrent_downloads", 1)
        for i in range(num_workers):
            worker = DownloadWorker(self.task_queue, self.gui_callback, self.get_settings)
            worker.start()
            self.workers.append(worker)

    def build_menu(self):
        menubar = tk.Menu(self.root)
        filem = tk.Menu(menubar, tearoff=0)
        filem.add_command(label="Choose Download Folder", command=self.choose_folder)
        filem.add_command(label="Open Download Folder", command=self.open_folder)
        filem.add_separator()
        filem.add_command(label="Exit", command=self.on_close)
        menubar.add_cascade(label="File", menu=filem)

        toolsm = tk.Menu(menubar, tearoff=0)
        toolsm.add_command(label="Check for Update", command=self.check_update)
        toolsm.add_command(label="View History", command=self.show_history)
        toolsm.add_command(label="Open Log File", command=lambda: self.open_path(LOG_FILE))
        menubar.add_cascade(label="Tools", menu=toolsm)

        settingsm = tk.Menu(menubar, tearoff=0)
        self.var_dark = tk.BooleanVar(value=self.settings.get("dark_mode", True))
        self.var_enable_subs = tk.BooleanVar(value=self.settings.get("enable_subtitles", True))
        self.var_burn_subs = tk.BooleanVar(value=self.settings.get("burn_subtitles", False))
        self.var_audio_global = tk.BooleanVar(value=self.settings.get("audio_only", False))
        self.var_clipboard = tk.BooleanVar(value=self.settings.get("clipboard_autofill", True))
        self.var_enable_playlist = tk.BooleanVar(value=self.settings.get("enable_playlist", False))

        settingsm.add_checkbutton(label="Dark Mode", command=self.toggle_theme, variable=self.var_dark)
        settingsm.add_checkbutton(label="Enable Subtitles", command=self.toggle_subtitles, variable=self.var_enable_subs)
        settingsm.add_checkbutton(label="Burn Subtitles (if possible)", command=self.toggle_burn_subs, variable=self.var_burn_subs)
        settingsm.add_checkbutton(label="Audio Only (global)", command=self.toggle_audio_only, variable=self.var_audio_global)
        settingsm.add_checkbutton(label="Clipboard Autofill", command=self.toggle_clipboard_autofill, variable=self.var_clipboard)
        settingsm.add_checkbutton(label="Enable Playlist Download", command=self.toggle_playlist, variable=self.var_enable_playlist)
        settingsm.add_separator()
        settingsm.add_command(label="Subtitle Languages…", command=self.edit_subtitle_langs)
        settingsm.add_command(label="Filename Template…", command=self.edit_filename_template)
        settingsm.add_command(label="Audio Format…", command=self.edit_audio_format)
        settingsm.add_command(label="Download Speed Limit…", command=self.edit_speed_limit)
        settingsm.add_command(label="Concurrent Downloads…", command=self.edit_concurrent_downloads)
        menubar.add_cascade(label="Settings", menu=settingsm)

        helpm = tk.Menu(menubar, tearoff=0)
        helpm.add_command(label="About", command=self.show_about)
        helpm.add_command(label="Documentation", command=self.show_documentation)
        menubar.add_cascade(label="Help", menu=helpm)

        self.root.config(menu=menubar)

    def build_topbar(self):
        top = ttk.Frame(self.root)
        top.pack(fill="x", padx=10, pady=8)

        self.url_var = tk.StringVar()
        ttk.Label(top, text="Video URL(s):").grid(row=0, column=0, sticky="w")
        self.url_entry = ttk.Entry(top, textvariable=self.url_var, width=90)
        self.url_entry.grid(row=1, column=0, columnspan=8, sticky="we", pady=(2, 8))

        ttk.Button(top, text="Add", command=self.add_url).grid(row=2, column=0, sticky="w")
        ttk.Button(top, text="Paste", command=self.paste_url).grid(row=2, column=1, sticky="w", padx=(6, 0))
        ttk.Button(top, text="Clear", command=lambda: self.url_var.set("")).grid(row=2, column=2, sticky="w", padx=(6, 0))
        ttk.Button(top, text="Add Multiple…", command=self.add_multiple_dialog).grid(row=2, column=3, sticky="w", padx=(6, 0))
        ttk.Button(top, text="Choose Quality", command=self.choose_quality_for_entry).grid(row=2, column=4, sticky="w", padx=(6, 0))

        self.folder_label = ttk.Label(top, text="")
        self.folder_label.grid(row=3, column=0, columnspan=8, sticky="w", pady=(8, 0))
        top.columnconfigure(7, weight=1)



    def build_task_list(self):
        container = ttk.Frame(self.root)
        container.pack(fill="both", expand=True, padx=10, pady=6)

        cols = ("id", "title", "url", "status", "progress", "speed", "eta", "actions")
        self.tree = ttk.Treeview(
            container,
            columns=cols,
            show="tree headings",          
            selectmode="browse",
            height=2
        )

        style = ttk.Style(self.root)
        style.configure("Treeview", rowheight=60) 
        self.tree["displaycolumns"] = ("id", "title", "url", "status","progress", "speed", "eta", "actions")
        self.tree.column("#0", width=120, stretch=False)
        self.tree.heading("#0", text="")
        vsb = ttk.Scrollbar(container, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)

        self.tree.heading("id", text="ID")
        self.tree.column("id", width=40, stretch=False)

        self.tree.heading("title", text="Title")
        self.tree.column("title", width=220)

        self.tree.heading("url", text="URL")
        self.tree.column("url", width=320)

        self.tree.heading("status", text="Status")
        self.tree.column("status", width=90, stretch=False)

        self.tree.heading("progress", text="Progress")
        self.tree.column("progress", width=100, stretch=False)

        self.tree.heading("speed", text="Speed")
        self.tree.column("speed", width=90, stretch=False)

        self.tree.heading("eta", text="ETA")
        self.tree.column("eta", width=70, stretch=False)

        self.tree.heading("actions", text="Actions")
        self.tree.column("actions", width=120, stretch=False)

        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", self._on_tree_dclick)



    def _add_row_for_task(self, task: DownloadTask):

        self.tree.insert(
            "", "end", iid=str(task.id),
            values=(task.id, task.title, task.url,
                    task.status, f"{task.progress:.1f}%",
                    task.speed, task.eta, "")
        )

        task.thumb_path = self._fetch_thumbnail(task.url)

        if task.thumb_path and os.path.isfile(task.thumb_path):
            try:
                img = ImageTk.PhotoImage(file=task.thumb_path)
                self._thumb_cache[str(task.id)] = img  
                self.tree.item(str(task.id), image=img)
            except Exception as e:
                logger.debug("Thumbnail attach failed: %s", e)

    def _update_task_row(self, task: DownloadTask):
        if str(task.id) in self.tree.get_children():
            self.tree.item(
                str(task.id),
                values=(task.id, task.title, task.url,
                        task.status, f"{task.progress:.1f}%",
                        task.speed, task.eta, "")
            )


 

    def _on_tree_dclick(self, event):
        item = self.tree.identify_row(event.y)
        if not item:
            return
        task_id = int(item)
        task = self.tasks[task_id]

        if task.status == TASK_RUNNING:
            task.pause_flag.set()
            self.status(f"Pausing #{task_id}")
        elif task.status == TASK_PAUSED:
            task.pause_flag.clear()
            task.status = TASK_QUEUED
            self.task_queue.put(task)
            self.status(f"Resuming #{task_id}")

    def build_controls(self):
        bottom = ttk.Frame(self.root)
        bottom.pack(fill="x", padx=10, pady=8)

        self.audio_only_var = tk.BooleanVar(value=self.settings.get("audio_only", False))
        self.chk_audio = ttk.Checkbutton(bottom, text="Audio Only (for new tasks)", variable=self.audio_only_var)
        self.chk_audio.grid(row=0, column=0, sticky="w")

        ttk.Button(bottom, text="Start Queue", command=self.start_queue).grid(row=0, column=1, padx=(10, 0))
        ttk.Button(bottom, text="Cancel Current", command=self.cancel_current).grid(row=0, column=2, padx=(10, 0))
        ttk.Button(bottom, text="Cancel All", command=self.cancel_all).grid(row=0, column=7, padx=(10, 0))
        ttk.Button(bottom, text="Clear Completed", command=self.clear_completed).grid(row=0, column=3, padx=(10, 0))
        ttk.Button(bottom, text="Pause All", command=self.pause_all).grid(row=0, column=4, padx=(10, 0))
        ttk.Button(bottom, text="Resume All", command=self.resume_all).grid(row=0, column=5, padx=(10, 0))
        ttk.Button(bottom, text="Pause / Resume Selected", command=self.toggle_selected).grid(row=0, column=6, padx=(10, 0))

        self.status_var = tk.StringVar(value="Ready.")
        self.status_label = ttk.Label(self.root, textvariable=self.status_var)
        self.status_label.pack(anchor="w", padx=12, pady=(0, 10))

    def apply_theme(self, dark: bool):
        self.settings["dark_mode"] = bool(dark)

        if dark:
            bg   = "#2e2e2e"       
            fg   = "black"         
        else:
            bg   = "SystemButtonFace"
            fg   = "black"

        try:

            self.root.configure(bg=bg)

            self.style.configure("TLabel", background=bg, foreground=fg)
            self.style.configure("TFrame", background=bg)

            self.style.configure("TButton",    background=bg, foreground=fg)
            self.style.configure("TCheckbutton", background=bg, foreground=fg)

            self.style.configure("TEntry", fieldbackground=bg, foreground=fg)

            self.style.configure("Treeview",
                                background=bg,
                                foreground=fg,
                                fieldbackground=bg)
            self.style.map("Treeview",
                        background=[("selected", "#505050")],
                        foreground=[("selected", "white")])

            self.tree.configure(style="Treeview")
        except Exception:
            pass

        Persistence.save_settings(self.settings)

    def toggle_theme(self):
        new = not self.settings.get("dark_mode", True)
        self.var_dark.set(new)
        self.apply_theme(new)

    def toggle_subtitles(self):
        self.settings["enable_subtitles"] = not self.settings.get("enable_subtitles", True)
        self.var_enable_subs.set(self.settings["enable_subtitles"])
        self.save_settings()

    def toggle_burn_subs(self):
        self.settings["burn_subtitles"] = not self.settings.get("burn_subtitles", False)
        self.var_burn_subs.set(self.settings["burn_subtitles"])
        self.save_settings()

    def toggle_audio_only(self):
        self.settings["audio_only"] = not self.settings.get("audio_only", False)
        self.audio_only_var.set(self.settings["audio_only"])
        self.var_audio_global.set(self.settings["audio_only"])
        self.save_settings()

    def toggle_clipboard_autofill(self):
        self.settings["clipboard_autofill"] = not self.settings.get("clipboard_autofill", True)
        self.var_clipboard.set(self.settings["clipboard_autofill"])
        self.save_settings()

    def toggle_playlist(self):
        self.settings["enable_playlist"] = not self.settings.get("enable_playlist", False)
        self.var_enable_playlist.set(self.settings["enable_playlist"])
        self.save_settings()

    def edit_subtitle_langs(self):
        win = tk.Toplevel(self.root)
        win.title("Subtitle Languages")
        ttk.Label(win, text="Comma-separated language codes (e.g., en,ar,fr)").pack(padx=10, pady=10)
        sv = tk.StringVar(value=",".join(self.settings.get("subtitle_langs", ["en"])))
        tk.Entry(win, textvariable=sv, width=40).pack(padx=10, pady=(0, 10))
        def save():
            langs = [x.strip() for x in sv.get().split(",") if x.strip()]
            self.settings["subtitle_langs"] = langs or ["en"]
            Persistence.save_settings(self.settings)
            win.destroy()
        ttk.Button(win, text="Save", command=save).pack(pady=10)

    def edit_filename_template(self):
        win = tk.Toplevel(self.root)
        win.title("Filename Template")
        ttk.Label(win, text="yt-dlp template (e.g., %(title)s.%(ext)s)").pack(padx=10, pady=10)
        sv = tk.StringVar(value=self.settings.get("filename_template", DEFAULT_SETTINGS["filename_template"]))
        tk.Entry(win, textvariable=sv, width=50).pack(padx=10, pady=(0, 10))
        def save():
            tpl = sv.get().strip() or DEFAULT_SETTINGS["filename_template"]
            self.settings["filename_template"] = tpl
            Persistence.save_settings(self.settings)
            win.destroy()
        ttk.Button(win, text="Save", command=save).pack(pady=10)

    def edit_audio_format(self):
        win = tk.Toplevel(self.root)
        win.title("Audio Format")
        ttk.Label(win, text="Choose audio codec").pack(padx=10, pady=10)
        codec = tk.StringVar(value=self.settings.get("audio_format", "mp3"))
        ttk.Combobox(win, textvariable=codec, values=["mp3", "wav", "aac", "m4a", "flac", "opus"], state="readonly", width=10).pack(padx=10, pady=(0, 10))
        def save():
            self.settings["audio_format"] = codec.get()
            Persistence.save_settings(self.settings)
            win.destroy()
        ttk.Button(win, text="Save", command=save).pack(pady=10)

    def edit_speed_limit(self):
        win = tk.Toplevel(self.root)
        win.title("Download Speed Limit")
        ttk.Label(win, text="Max KB/s (0 = unlimited)").pack(padx=10, pady=10)
        speed = tk.IntVar(value=self.settings.get("max_download_speed", 0))
        tk.Entry(win, textvariable=speed, width=20).pack(padx=10, pady=(0, 10))
        def save():
            self.settings["max_download_speed"] = max(0, speed.get())
            Persistence.save_settings(self.settings)
            win.destroy()
        ttk.Button(win, text="Save", command=save).pack(pady=10)

    def edit_concurrent_downloads(self):
        win = tk.Toplevel(self.root)
        win.title("Concurrent Downloads")
        ttk.Label(win, text="Simultaneous downloads (1-5)").pack(padx=10, pady=10)
        concurrent = tk.IntVar(value=self.settings.get("concurrent_downloads", 1))
        ttk.Spinbox(win, textvariable=concurrent, from_=1, to=5, width=5).pack(padx=10, pady=(0, 10))
        def save():
            new_count = max(1, min(5, concurrent.get()))
            self.settings["concurrent_downloads"] = new_count
            Persistence.save_settings(self.settings)
            for w in self.workers:
                w.stop()
            self.workers = []
            self.init_workers()
            win.destroy()
        ttk.Button(win, text="Save", command=save).pack(pady=10)

    def choose_folder(self):
        folder = filedialog.askdirectory(initialdir=self.settings.get("download_folder", os.getcwd()))
        if folder:
            self.settings["download_folder"] = folder
            self.update_folder_label()
            self.save_settings()

    def open_folder(self):
        self.open_path(self.settings.get("download_folder", os.getcwd()))

    def open_path(self, path):
        if not path:
            return
        try:
            if sys.platform.startswith("win"):
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as e:
            messagebox.showerror("Open", f"Failed to open: {e}")

    def check_update(self):
        try:
            import requests, shutil

            VERSION_URL = "https://raw.githubusercontent.com/khaled-moh4med/Viora/main/version.json"
            resp = requests.get(VERSION_URL, timeout=5)
            resp.raise_for_status()
            data = resp.json()

            latest_version = data.get("version", "").strip()
            release_notes = data.get("notes", "No release notes available.")
            download_url = data.get("download_url")
            repo_url = data.get("url", "https://github.com/khaled-moh4med/Viora")

            if latest_version and latest_version != APP_VERSION:
                if messagebox.askyesno(
                    "Update Available",
                    f"A new version ({latest_version}) is available!\n"
                    f"You are running {APP_VERSION}.\n\n"
                    f"Changes:\n{release_notes}\n\n"
                    "Do you want to update automatically?"
                ):
                    if download_url:
                        new_code = requests.get(download_url, timeout=10)
                        new_code.raise_for_status()

                        current_file = os.path.abspath(sys.argv[0])

                        # Save new exe as temporary file
                        temp_file = current_file + ".new"
                        with open(temp_file, "wb") as f:
                            f.write(new_code.content)

                        messagebox.showinfo(
                            "Update Ready",
                            f"Version {latest_version} downloaded.\nThe app will restart now to install it."
                        )

                        # Launch updater script (it will run AFTER this process exits)
                        subprocess.Popen([sys.executable, "updater.py", current_file, temp_file])

                        # Make sure the current app closes completely
                        self.root.destroy()
                        sys.exit(0)
                    else:
                        webbrowser.open(repo_url)
            else:
                messagebox.showinfo(
                    "Check for Updates",
                    f"You are running the latest version ({APP_VERSION})."
                )

        except Exception as e:
            messagebox.showerror("Check for Updates", f"Could not check GitHub:\n{e}")

    def detect_update(self):
        try:
            import requests
            VERSION_URL = "https://raw.githubusercontent.com/khaled-moh4med/Viora/main/version.json"

            resp = requests.get(VERSION_URL, timeout=5)
            resp.raise_for_status()
            data = resp.json()

            latest_version = data.get("version", "").strip()
            release_notes = data.get("notes", "No release notes available.")

            if latest_version and latest_version != APP_VERSION:
                if messagebox.askyesno(
                    "Update Available",
                    f"A new version ({latest_version}) is available!\n"
                    f"You are running {APP_VERSION}.\n\n"
                    f"Changes:\n{release_notes}\n\n"
                    "Do you want to update now?"
                ):
                    self.check_update()  # reuse updater with restart
        except Exception as e:
            # Fail silently at startup (don’t annoy the user with errors)
            print("Update check failed:", e)        

    def show_history(self):
        hist = Persistence.read_history()
        win = tk.Toplevel(self.root)
        win.title("Download History")
        win.geometry("900x450")

        search_var = tk.StringVar()
        search_frame = ttk.Frame(win)
        search_frame.pack(fill="x", padx=6, pady=6)
        ttk.Label(search_frame, text="Search:").pack(side="left")
        tk.Entry(search_frame, textvariable=search_var).pack(fill="x", padx=(6, 0), expand=True)

        cols = ("when", "title", "url", "file")
        tree = ttk.Treeview(win, columns=cols, show="headings")
        for c in cols:
            tree.heading(c, text=c.title())
            tree.column(c, width=220 if c == "file" else 180)
        vsb = ttk.Scrollbar(win, orient="vertical", command=tree.yview)
        tree.configure(yscroll=vsb.set)
        tree.pack(fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        def populate(filter_text=""):
            for item in tree.get_children():
                tree.delete(item)
            for e in reversed(hist):
                if filter_text.lower() not in json.dumps(e).lower():
                    continue
                dt = time.strftime("%Y-%m-%d %H:%M", time.localtime(e.get("when", time.time())))
                tree.insert("", "end", values=(dt, e.get("title", "-"), e.get("url", "-"), e.get("file", "-")))

        search_var.trace_add("write", lambda *_: populate(search_var.get().lower()))
        populate()

    def show_about(self):
        messagebox.showinfo("About", f"{APP_NAME} {APP_VERSION}\n\n~ A video downloader that can download any video by inserting URL's and for MORE info go to Viora Documentation ...")

    def show_documentation(self):
        doc_text = """
        Viora Documentation

        Features:
        - Download videos & playlists
        - Audio extraction (MP3, WAV, AAC, FLAC, OPUS)
        - Subtitles download + burn-in
        - Quality selection per task
        - Concurrent downloads (1-5)
        - Pause / Resume / Cancel via double-click
        - Drag & Drop, clipboard autofill
        - Dark / Light theme
        - Persistent history with search
        - Auto-retry failed downloads (3×)
        - Real-time progress notifications
        - Thumbnail preview in quality picker

        Usage:
        1. Paste URL(s) or drag & drop
        2. Choose quality and Formats (optional)
        3. Toggle audio-only if desired
        4. Add to queue
        5. Double-click a row to Pause/Resume
        """
        win = tk.Toplevel(self.root)
        win.title("Documentation")
        win.geometry("500x400")
        text = tk.Text(win, wrap="word", padx=10, pady=10)
        text.insert("1.0", doc_text)
        text.config(state="disabled")
        text.pack(fill="both", expand=True)

    def on_drop(self, event):
        dropped = re.findall(r"{([^}]+)}", event.data) or [event.data.strip()]
        count = 0
        for item in dropped:
            if item.lower().startswith("http") and is_valid_url(item):
                self.enqueue_url(item)
                count += 1
        if count:
            self.status(f"Added {count} URL(s) from drop.")

    def clipboard_watcher(self):
        try:
            data = self.root.clipboard_get()
        except Exception:
            data = ""
        if data != self.clipboard_cache and is_valid_url(data) and not self.url_var.get():
            self.clipboard_cache = data
            self.url_var.set(data)
            self.status("URL detected from clipboard.")
        self.root.after(1200, self.clipboard_watcher)

    def add_url(self):
        url = self.url_var.get().strip()
        if not url:
            messagebox.showerror("Add", "Please enter a URL.")
            return
        if not is_valid_url(url):
            messagebox.showerror("Add", "Invalid URL.")
            return
        self.enqueue_url(url, audio_only=self.audio_only_var.get())
        self.url_var.set("")

    def paste_url(self):
        try:
            data = self.root.clipboard_get()
        except Exception:
            data = ""
        if data:
            self.url_var.set(data)

    def add_multiple_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("Add Multiple URLs with Quality")
        win.geometry("900x900")

        ttk.Label(win, text="Enter one URL per line:").pack(anchor="w", padx=10, pady=6)

        txt = tk.Text(win, width=100, height=12)
        txt.pack(fill="both", expand=True, padx=10, pady=(0, 6))

        frm = ttk.Frame(win)
        frm.pack(fill="both", expand=True, padx=10, pady=6)

        cols = ("URL", "Quality")
        tv = ttk.Treeview(frm, columns=cols, show="headings", height=8)
        vsb = ttk.Scrollbar(frm, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=vsb.set)
        tv.heading("URL", text="URL")
        tv.heading("Quality", text="Quality")
        tv.column("URL", width=550)
        tv.column("Quality", width=120)
        tv.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        def pick_quality():
            item = tv.focus()
            if not item:
                return
            url = tv.set(item, "URL")

            try:
                with YoutubeDL({}) as ydl:
                    info = ydl.extract_info(url, download=False)
            except Exception as e:
                messagebox.showerror("Error", f"Could not fetch formats: {e}")
                return

            formats = info.get("formats") or []
            if not formats:
                messagebox.showinfo("Formats", "No formats found.")
                return

            top = tk.Toplevel(win)
            top.title("Choose Quality")
            top.geometry("600x400")

            cols2 = ("format_id", "ext", "resolution", "fps", "acodec", "note")
            lv = ttk.Treeview(top, columns=cols2, show="headings")
            vsb2 = ttk.Scrollbar(top, orient="vertical", command=lv.yview)
            lv.configure(yscrollcommand=vsb2.set)
            for c in cols2:
                lv.heading(c, text=c)
                lv.column("format_id", width=80)
                lv.column("note", width=200)
            lv.pack(fill="both", expand=True)
            vsb2.pack(side="right", fill="y")

            audio_only = self.audio_only_var.get()
            if audio_only:
                fmt_list = [f for f in formats if f.get('acodec') != 'none' and f.get('vcodec') == 'none']
                fmt_list.sort(key=lambda f: int(f.get("tbr") or 0), reverse=True)
            else:
                fmt_list = sorted(formats, key=lambda f: (int(f.get("height") or 0), int(f.get("tbr") or 0)), reverse=True)

            for f in fmt_list:
                lv.insert("", tk.END, values=(
                    f.get("format_id"),
                    f.get("ext"),
                    f.get("height") and f"{f['height']}p" or "",
                    f.get("fps") or "",
                    f.get("acodec") or "",
                    f.get("format_note") or ""
                ))

            def set_choice():
                sel = lv.focus()
                if sel:
                    fmt = lv.set(sel, "format_id")
                    tv.set(item, "Quality", fmt)
                top.destroy()

            ttk.Button(top, text="Select", command=set_choice).pack(pady=6)

        def fill_list():
            for i in tv.get_children():
                tv.delete(i)
            lines = [ln.strip() for ln in txt.get("1.0", "end").splitlines() if ln.strip()]
            for u in lines:
                if is_valid_url(u):
                    tv.insert("", tk.END, values=(u, "default"))

        def add_all():
            for i in tv.get_children():
                url, fmt = tv.item(i, "values")
                if is_valid_url(url):
                    self.enqueue_url(url, audio_only=self.audio_only_var.get(),
                                     format_id=(None if fmt == "default" else fmt))
            self.status(f"Added {len(tv.get_children())} URL(s).")
            win.destroy()

        btn_frm = ttk.Frame(win)
        btn_frm.pack(fill="x", padx=10, pady=10)

        # NEW: Paste + Clear buttons (operate on the Text widget)
        ttk.Button(btn_frm, text="Paste", command=lambda: txt.insert("end", self.root.clipboard_get())).pack(side="left", padx=5)
        ttk.Button(btn_frm, text="Clear", command=lambda: txt.delete("1.0", "end")).pack(side="left", padx=5)

        # Existing buttons
        ttk.Button(btn_frm, text="Load URLs", command=fill_list).pack(side="left", padx=5)
        ttk.Button(btn_frm, text="Pick Quality", command=pick_quality).pack(side="left", padx=5)
        ttk.Button(btn_frm, text="Add to Queue", command=add_all).pack(side="right", padx=5)

    def enqueue_url(self, url, audio_only=False, format_id=None):
        task = DownloadTask(url, audio_only=audio_only, format_id=format_id)
        task.status = TASK_QUEUED
        self.tasks[task.id] = task
        self._add_row_for_task(task)
        self.task_queue.put(task)

    def start_queue(self):
        self.status("Queue is running…")

    def cancel_current(self):
        """
        Cancel the currently-running task, terminate its process,
        and delete any partially-downloaded file.
        """
        for w in self.workers:
            task = w.current_task
            if task and task.status == TASK_RUNNING:

                task.cancel_flag.set()

                if hasattr(task, "_proc") and task._proc and task._proc.poll() is None:
                    try:
                        task._proc.kill()
                        task._proc.wait(timeout=2)
                    except Exception:
                        pass

                settings = self.get_settings()
                outtmpl = os.path.join(
                    settings["download_folder"],
                    settings["filename_template"]
                )

                try:
                    from yt_dlp import YoutubeDL
                    ydl = YoutubeDL({"outtmpl": outtmpl, "quiet": True})
                    info = ydl.extract_info(task.url, download=False)
                    real_path = ydl.prepare_filename(info)

                    if task.audio_only or settings.get("audio_only"):
                        base, _ = os.path.splitext(real_path)
                        real_path = base + "." + settings.get("audio_format", "mp3")

                    if os.path.isfile(real_path):
                        os.remove(real_path)
                        logger.info("Deleted partial file: %s", real_path)
                except Exception as e:
                    logger.warning("Could not remove partial file: %s", e)

                task.status = TASK_CANCELED
                self._update_task_row(task)
                self.status(f"Cancelled and deleted #{task.id}")
                return

        self.status("No running task to cancel.")

    def pause_all(self):
        count = 0
        for task in self.tasks.values():
            if task.status == TASK_RUNNING:
                task.pause_flag.set()   
                count += 1
        self.status(f"Paused {count} downloads.")

    def resume_all(self):
        count = 0
        for task in self.tasks.values():
            if task.status in (TASK_PAUSED, TASK_FAILED):   
                task.pause_flag.clear()
                task.error = None
                task.status = TASK_QUEUED
                self.task_queue.put(task)
                count += 1
                self._update_task_row(task)
        self.status(f"Resumed {count} downloads.")

    def clear_completed(self):
        to_remove = [tid for tid, t in self.tasks.items() if t.status in (TASK_DONE, TASK_FAILED, TASK_CANCELED)]
        for tid in to_remove:
            self.remove_task(tid)
        self.status(f"Cleared {len(to_remove)} completed items.")

    def remove_task(self, task_id):
        self.tasks.pop(task_id, None)
        if str(task_id) in self.tree.get_children():
            self.tree.delete(str(task_id))

    def gui_callback(self, action, task: DownloadTask):
        if action == "update_task":
            self.root.after_idle(self._update_task_row, task)

    # Quality selector
    def choose_quality_for_entry(self):
        url = self.url_var.get().strip()
        if not url:
            messagebox.showwarning("Choose Quality", "Enter a URL in the entry first.")
            return
        self._open_format_selector(url, task_to_update=None)

    def _open_format_selector(self, url, task_to_update: DownloadTask = None):
        try:
            with YoutubeDL({}) as ydl:
                info = ydl.extract_info(url, download=False)
        except Exception as e:
            messagebox.showerror("Error", f"Could not fetch formats: {e}")
            return
        formats = info.get("formats") or []
        if not formats:
            messagebox.showinfo("Formats", "No formats found for this URL.")
            return

        top = tk.Toplevel(self.root)
        top.title("Choose Quality")
        top.geometry("900x500")

        thumb_lbl = None
        if PIL_AVAILABLE and info.get("thumbnail"):
            try:
                resp = requests.get(info["thumbnail"], timeout=5)
                img = Image.open(BytesIO(resp.content)).resize((160, 90), Image.LANCZOS)
                tk_img = ImageTk.PhotoImage(img)
                thumb_lbl = ttk.Label(top, image=tk_img)
                thumb_lbl.image = tk_img
                thumb_lbl.pack(pady=(6, 0))
            except Exception:
                pass

        cols = ("format_id", "ext", "resolution", "fps", "vcodec", "acodec", "note")
        tv = ttk.Treeview(top, columns=cols, show="headings")
        for c in cols:
            tv.heading(c, text=c)
            tv.column("format_id", width=120)
            tv.column("note", width=240)
        tv.pack(fill="both", expand=True, padx=6, pady=6)

        def _fmt_res(f):
            return f.get("resolution") or (f.get("height") and f"{f['height']}p") or ""

        audio_only = self.audio_only_var.get() or (task_to_update and task_to_update.audio_only)
        if audio_only:
            sorted_formats = [f for f in formats if f.get('acodec') != 'none' and f.get('vcodec') == 'none']
            sorted_formats.sort(key=lambda f: int(f.get("tbr") or 0), reverse=True)
        else:
            sorted_formats = sorted(formats, key=lambda f: (int(f.get("height") or 0), int(f.get("tbr") or 0)), reverse=True)

        for f in sorted_formats:
            tv.insert("", tk.END, values=(
                f.get("format_id"),
                f.get("ext"),
                _fmt_res(f),
                f.get("fps") or "",
                f.get("vcodec") or "",
                f.get("acodec") or "",
                f.get("format_note") or ""
            ))

        def on_select():
            sel = tv.focus()
            if not sel:
                return
            fmt = tv.item(sel, "values")[0]
            if task_to_update is not None:
                task_to_update.format_id = fmt
                self.status(f"Set quality {fmt} for queued item #{task_to_update.id}.")
                self._update_task_row(task_to_update)
            else:
                t = DownloadTask(url, audio_only=self.audio_only_var.get(), format_id=fmt)
                t.status = TASK_QUEUED
                self.tasks[t.id] = t
                self._add_row_for_task(t)
                self.task_queue.put(t)
                self.status(f"Added with format {fmt}.")
                self.url_var.set("")
            top.destroy()

        ttk.Button(top, text="Select", command=on_select).pack(pady=6)

    def on_close(self):
        try:
            for worker in self.workers:
                worker.stop()
        except Exception:
            pass
        time.sleep(0.15)
        try:
            self.root.destroy()
        except Exception:
            pass

def main():
    app = App()
    app.root.protocol("WM_DELETE_WINDOW", app.on_close)

    # Auto-check for updates 2 seconds after startup
    app.root.after(2000, app.detect_update)

    app.root.mainloop()

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        logger.exception("Fatal error: %s", e)
        try:
            messagebox.showerror(APP_NAME, f"Fatal error: {e}")
        except Exception:
            print("Fatal error:", e)

