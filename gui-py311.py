import os
import sys
import time
import platform
import requests
import json
from concurrent.futures import ThreadPoolExecutor
from threading import Thread, Lock
from packaging import version
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import webbrowser
import subprocess
import shutil

def resource_path(relative_path):
    """获取资源的绝对路径,用于PyInstaller打包后定位资源文件"""
    if hasattr(sys, '_MEIPASS'):
        return os.path.join(sys._MEIPASS, relative_path)
    return os.path.join(os.path.abspath("."), relative_path)

# 获取系统架构
def get_system_architecture():
    arch = platform.machine().lower()
    if 'x86' in arch:
        return 'x86'
    elif 'amd64' in arch or 'x86_64' in arch:
        return 'x64'
    elif 'arm64' in arch:
        return 'arm64'
    else:
        raise ValueError(f"Unsupported system architecture: {arch}")

SYSTEM_ARCH = get_system_architecture()

# 释放 7z 文件
def extract_7z_files():
    # 定义要释放的文件
    files_to_extract = [f"7z-{SYSTEM_ARCH}.exe", f"7z-{SYSTEM_ARCH}.dll"]
    # 获取程序当前目录
    current_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
    # 释放文件
    for file in files_to_extract:
        # 获取资源文件路径（从打包的 .exe 文件中提取）
        src_path = resource_path(file)
        # 目标路径（当前目录）
        dst_path = os.path.join(current_dir, file.replace(f"-{SYSTEM_ARCH}", ""))
        # 如果文件已存在，先删除
        if os.path.exists(dst_path):
            os.remove(dst_path)
        # 复制文件到当前目录
        shutil.copy(src_path, dst_path)
        print(f"已释放文件: {file}")

# 删除释放的 7z 文件
def delete_7z_files():
    # 定义要删除的文件
    files_to_delete = [f"7z-{SYSTEM_ARCH}.exe", f"7z-{SYSTEM_ARCH}.dll"]
    # 获取程序当前目录
    current_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
    # 删除文件
    for file in files_to_delete:
        file_path = os.path.join(current_dir, file.replace(f"-{SYSTEM_ARCH}", ""))
        if os.path.exists(file_path):
            try:
                os.remove(file_path)
                print(f"已删除临时文件: {file}")
            except Exception as e:
                print(f"无法删除文件 {file}: {str(e)}")

# 在程序启动时释放 7z 文件
extract_7z_files()

# 配置参数
CURRENT_VERSION = "1.0.5"  # 当前版本号
CURRENT_VER_CODE = "1051"  # 当前版本代码
HEADERS = {"User-Agent": f"RF-Py1-Api/{CURRENT_VERSION}"}  # 设置UA
DEFAULT_DOWNLOAD_DIR = os.path.join(os.getcwd(), "RF-Downloader")  # 默认下载目录为当前目录下的 RF-Downloader 文件夹
ICON_PATH = resource_path("lty1.ico")   # 应用图标
CONFIG_PATH = "config.json"  # 保存窗体位置的文件

class DownloadTracker:
    def __init__(self, total_size):
        self.total_size = total_size
        self.downloaded = 0
        self.lock = Lock()
        self.start_time = time.time()
        self.last_update = self.start_time
        self.last_downloaded = 0
        self.speed = 0
        self.remaining_time = 0

    def update(self, size):
        with self.lock:
            self.downloaded += size

    def get_progress(self):
        with self.lock:
            elapsed = time.time() - self.start_time
            percent = (self.downloaded / self.total_size) * 100 if self.total_size else 0
            self.speed = (self.downloaded - self.last_downloaded) / (time.time() - self.last_update + 1e-9)
            self.last_downloaded = self.downloaded
            self.last_update = time.time()

            self.remaining_time = (self.total_size - self.downloaded) / self.speed if self.speed > 0 else 0

            return {
                'percent': percent,
                'downloaded': self.downloaded,
                'total': self.total_size,
                'speed': self.speed,
                'remaining': self.remaining_time,
            }

    def _human_size(self, size):
        units = ('B', 'KB', 'MB', 'GB')
        index = 0
        while size >= 1024 and index < 3:
            size /= 1024
            index += 1
        return f"{size:.2f} {units[index]}"

    def _format_time(self, seconds):
        if seconds <= 0:
            return "--:--"
        minutes, seconds = divmod(seconds, 60)
        hours, minutes = divmod(minutes, 60)
        days, hours = divmod(hours, 24)
        if days > 0:
            return f"{int(days)}天 {int(hours):02}:{int(minutes):02}:{int(seconds):02}"
        elif hours > 0:
            return f"{int(hours):02}:{int(minutes):02}:{int(seconds):02}"
        return f"{int(minutes):02}:{int(seconds):02}"


class VersionInfo:
    def __init__(self, version, ver_code, changelog, level, url):
        self.version = version
        self.ver_code = ver_code
        self.changelog = changelog.replace('\\n', '\n')
        self.level = level
        self.url = url


class DownloaderApp:
    def __init__(self, root):
        self.root = root
        self.root.title(f"重聚未来离线包下载器   当前版本: v{CURRENT_VERSION} ({CURRENT_VER_CODE})")
        
        # 初始化路径变量为空
        self.path_var = tk.StringVar(value="")
        self.client_dir = tk.StringVar(value="")
        self.download_dir = tk.StringVar(value="")
        self.auto_update_value = False  # 用于保存自动更新的勾选状态

        # 窗口位置配置
        self.window_positions = {}
        self.load_window_positions()

        # 设置主窗口的位置和大小
        self.set_window_position(self.root, "main")
        self.root.minsize(800, 650)

        self.download_dir = tk.StringVar(value=DEFAULT_DOWNLOAD_DIR)
        os.makedirs(self.download_dir.get(), exist_ok=True)

        self.channels = [("beta", "测试版"), ("stable", "稳定版")]
        self.versions = []
        self.selected_channel = None
        self.selected_version = None
        self.is_channel_selected = False
        self.notice = ""

        # 获取程序所在目录的绝对路径
        self.app_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
        self.old_program_path = os.path.abspath(sys.argv[0])
        self.temp_file_path = os.path.join(self.app_dir, "temp_filepath.txt")
        self.update_bat_path = os.path.join(self.app_dir, "update.bat")

        self.create_widgets()
        self.check_for_updates()

        # 绑定关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        # 隐藏功能相关变量
        self.candy_click_count = 0
        self.last_click_time = time.time()

        # 绑定 Ctrl+F6 键
        self.root.bind("<Control-F6>", self.show_secret_window)

    def load_window_positions(self):
        """加载窗体位置配置和用户选择的目录"""
        try:
            if os.path.exists(CONFIG_PATH):
                with open(CONFIG_PATH, 'r') as f:
                    config = json.load(f)
                    self.window_positions = config.get("window_positions", {})
                    # 加载用户选择的目录和自动更新状态
                    user_paths = config.get("user_paths", {})
                    if "download_dir" in user_paths:
                        self.download_dir.set(user_paths["download_dir"])
                        # 只有在路径存在时才创建目录
                        if os.path.exists(self.download_dir.get()):
                            os.makedirs(self.download_dir.get(), exist_ok=True)
                    if "client_dir" in user_paths:
                        self.client_dir.set(user_paths["client_dir"])
                        # 验证客户端目录是否有效
                        if os.path.exists(self.client_dir.get()) and os.path.exists(os.path.join(self.client_dir.get(), "Reunion.exe")):
                            self.path_var.set(self.client_dir.get())
                    if "auto_update" in user_paths:
                        self.auto_update_value = user_paths["auto_update"]
        except Exception as e:
            print(f"加载配置失败: {str(e)}")

    def save_window_position(self, window, window_name):
        """保存指定窗体的位置和用户选择的目录"""
        try:
            x = window.winfo_x()
            y = window.winfo_y()
            width = window.winfo_width()
            height = window.winfo_height()
            if window_name not in self.window_positions:
                self.window_positions[window_name] = {}
            self.window_positions[window_name].update({
                'x': x,
                'y': y,
                'width': width,
                'height': height
            })

            # 保存用户选择的目录和自动更新状态
            user_paths = {
                "download_dir": self.download_dir.get() if os.path.exists(self.download_dir.get()) else "",
                "client_dir": self.client_dir.get() if os.path.exists(self.client_dir.get()) and os.path.exists(os.path.join(self.client_dir.get(), "Reunion.exe")) else "",
                "auto_update": self.auto_update_value
            }

            config = {
                "window_positions": self.window_positions,
                "user_paths": user_paths
            }

            with open(CONFIG_PATH, 'w') as f:
                json.dump(config, f)
        except Exception as e:
            print(f"保存配置失败: {str(e)}")

    def set_window_position(self, window, window_name):
        """设置窗体位置"""
        if window_name in self.window_positions:
            config = self.window_positions[window_name]
            window.geometry(f"{config['width']}x{config['height']}+{config['x']}+{config['y']}")
        else:
            # 如果没有保存的位置信息，使用默认位置并保存
            default_geometry = {
                'main': "800x650",  # 调整主窗口默认高度
                'download': "500x400",
                'update': "400x300",
                'changelog': "400x300",
                'secret': "400x300"
            }
            window.geometry(default_geometry.get(window_name, "800x650"))
            self.save_window_position(window, window_name)

    def set_window_icon(self, window):
        try:
            if os.path.exists(ICON_PATH):
                window.iconbitmap(ICON_PATH)
            else:
                print(f"图标文件不存在: {ICON_PATH}")
        except Exception as e:
            print(f"设置图标失败: {str(e)}")

    def create_widgets(self):
        main_frame = ttk.Frame(self.root, padding="20")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # 公告栏
        notice_frame = ttk.LabelFrame(main_frame, text="公告", padding="10")
        notice_frame.pack(fill=tk.X, pady=(0, 10))  
        notice_frame.pack_propagate(False)
        notice_frame.configure(width=760, height=70)  # 设置宽度和高度
        self.notice_label = ttk.Label(notice_frame, text="", wraplength=740)
        self.notice_label.pack(fill=tk.X, expand=True)

        # 路径选择区域
        path_frame = ttk.Frame(main_frame)
        path_frame.pack(fill=tk.X, pady=10)

        # 路径选择框和自动更新勾选框
        self.auto_update_var = tk.BooleanVar(value=self.auto_update_value)

        dir_frame = ttk.Frame(path_frame)
        dir_frame.pack(fill=tk.X, pady=5)
        path_entry_frame = ttk.Frame(dir_frame)
        path_entry_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        ttk.Label(path_entry_frame, text="路径:").pack(side=tk.LEFT)
        path_entry = ttk.Entry(path_entry_frame, textvariable=self.path_var, state='readonly', width=50)
        path_entry.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)
        
        browse_btn = ttk.Button(path_entry_frame, text="浏览", command=self.choose_path)
        browse_btn.pack(side=tk.LEFT)

        # 自动更新勾选框
        self.auto_update_check = ttk.Checkbutton(
            dir_frame,
            text="自动更新重聚未来客户端",
            variable=self.auto_update_var,
            command=self.on_auto_update_toggle
        )
        self.auto_update_check.pack(side=tk.LEFT, padx=10)

        # 通道选择
        channel_frame = ttk.LabelFrame(main_frame, text="更新通道", padding="10")
        channel_frame.pack(fill=tk.X, pady=10)
        channel_frame.pack_propagate(False)
        channel_frame.configure(width=760, height=70)
        self.channel_var = tk.StringVar()
        for channel_id, description in self.channels:
            ttk.Radiobutton(
                channel_frame,
                text=f"{channel_id.capitalize()} - {description}",
                variable=self.channel_var,
                value=channel_id,
                command=self.on_channel_change
            ).pack(side=tk.LEFT, padx=10)

        # 线程选择
        thread_frame = ttk.LabelFrame(main_frame, text="下载线程数", padding="10")
        thread_frame.pack(fill=tk.X, pady=10)
        thread_frame.pack_propagate(False)
        thread_frame.configure(width=760, height=70)
        self.selected_thread_count = tk.IntVar()
        for opt in [1, 2, 4, 8]:
            ttk.Radiobutton(thread_frame, text=f"{opt} 线程", variable=self.selected_thread_count, value=opt).pack(side=tk.LEFT, padx=10)

        # 版本选择区域
        self.version_frame = ttk.LabelFrame(main_frame, text="可用版本", padding="10")
        self.version_frame.pack(fill=tk.BOTH, pady=10, expand=True)
        self.version_frame.pack_propagate(False)
        self.version_frame.configure(width=760, height=200)

        self.canvas = tk.Canvas(self.version_frame, height=150)  
        self.scrollbar = ttk.Scrollbar(self.version_frame, orient="vertical", command=self.canvas.yview)
        self.scrollable_frame = ttk.Frame(self.canvas)

        self.scrollable_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # 操作按钮和版权信息区域
        bottom_frame = ttk.Frame(main_frame)
        bottom_frame.pack(fill=tk.X, pady=10)
        bottom_frame.pack_propagate(False)
        bottom_frame.configure(width=760, height=80)  # 设置底部区域高度，包含按钮和版权信息

        # 操作按钮
        button_frame = ttk.Frame(bottom_frame)
        button_frame.pack(fill=tk.X)
        ttk.Button(button_frame, text="检查更新", command=self.on_check_for_updates).pack(side=tk.LEFT, padx=10)
        self.download_button = ttk.Button(button_frame, text="开始下载", command=self.start_download, state=tk.DISABLED)
        self.download_button.pack(side=tk.LEFT, padx=10)

        # 版权信息
        copyright_frame = ttk.Frame(bottom_frame)
        copyright_frame.pack(side=tk.BOTTOM, fill=tk.X)
        self.copyright_label = ttk.Label(copyright_frame, text="Copyright © 2025 Candy, All Rights Reserved")
        self.copyright_label.pack(side=tk.RIGHT, padx=10)
        self.copyright_label.bind("<Button-1>", self.on_copyright_click)

    def on_copyright_click(self, event):
        current_time = time.time()
        if current_time - self.last_click_time <= 1:  # 点击间隔不能超过1秒
            if "Candy" in self.copyright_label.cget("text"):
                self.candy_click_count += 1
        else:
            self.candy_click_count = 0
        self.last_click_time = current_time

        if self.candy_click_count == 10:
            self.show_candy_about()

    def show_candy_about(self):
        about_window = tk.Toplevel(self.root)
        about_window.title("关于")
        
        # 设置和保存窗口位置
        self.set_window_position(about_window, "about_candy")
        about_window.geometry("480x360")
        about_window.minsize(400, 300)
        about_window.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(about_window, "about_candy"))

        self.set_window_icon(about_window)

        about_frame = ttk.LabelFrame(about_window, text="关于", padding="10")
        about_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        about_text = tk.Text(about_frame, height=15, wrap=tk.WORD)
        about_text.insert(tk.END, "版权所有 (C) 2025 Candy. 保留所有权利.\n\n未经授权, 禁止任何个人或组织对本软件进行复制、修改或分发.\n\n本软件仅供个人学习和研究使用.")
        about_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        about_text.configure(state=tk.DISABLED)

        ttk.Button(about_window, text="关闭", command=lambda: self.close_window(about_window, "about_candy")).pack(pady=10)

    def on_channel_change(self):
        self.selected_channel = self.channel_var.get()
        self.is_channel_selected = True
        self.fetch_versions()

    def fetch_versions(self):
        try:
            channel = self.channel_var.get()
            filename = f"{channel}.ini"
            url = f"https://api17-2e40-yzlty.ru2023.top/verify1/{filename}"

            response = requests.get(url, headers=HEADERS, timeout=10)
            response.raise_for_status()
            self.versions = []

            current_version = None
            current_ver_code = None
            current_changelog = ""
            current_level = None
            current_url = None
            in_changelog = False

            for line in response.text.splitlines():
                line = line.strip()
                if line.startswith('[') and line.endswith(']'):
                    if current_version:
                        self.versions.append(VersionInfo(current_version, current_ver_code, current_changelog, current_level, current_url))
                        current_changelog = ""
                    current_version = line[1:-1]
                    current_ver_code = None
                    current_level = None
                    current_url = None
                    in_changelog = False
                elif line.startswith('ver='):
                    current_ver_code = line[4:]
                elif line.startswith('changelog='):
                    current_changelog = line[10:].replace('\\n', '\n')
                    in_changelog = True
                elif line.startswith('level='):
                    current_level = int(line[6:])
                elif line.startswith('url='):
                    current_url = line[4:]
                elif in_changelog:
                    current_changelog += '\n' + line

            if current_version and current_url:
                self.versions.append(VersionInfo(current_version, current_ver_code, current_changelog, current_level, current_url))

            for widget in self.scrollable_frame.winfo_children():
                widget.destroy()

            self.version_var = tk.StringVar()

            columns = 2
            for idx, version_info in enumerate(self.versions):
                column = idx % columns
                row = idx // columns

                btn_frame = ttk.Frame(self.scrollable_frame)
                btn_frame.grid(row=row, column=column, padx=5, pady=5, sticky="ew")

                style = ""
                extra_text = ""
                if version_info.level == 2:
                    style = "Warning"
                    extra_text = " ❗ 重大变更版本,谨慎更新"
                elif version_info.level == 3:
                    style = "Caution"
                    extra_text = " ❌️ Bug版本,不建议更新"

                state = tk.NORMAL if version_info.level != 0 else tk.DISABLED
                btn = ttk.Radiobutton(
                    btn_frame,
                    text=f"{version_info.version} ({version_info.ver_code}){extra_text}",
                    variable=self.version_var,
                    value=version_info.ver_code,
                    command=lambda info=version_info: self.on_version_select(info),
                    state=state
                )
                btn.pack(side=tk.LEFT)

                log_btn = ttk.Button(
                    btn_frame,
                    text="查看日志",
                    command=lambda info=version_info: self.show_changelog(info)
                )
                log_btn.pack(side=tk.RIGHT)

            if self.versions:
                available_versions = [v for v in self.versions if v.level != 0]
                if available_versions:
                    self.version_var.set(available_versions[0].ver_code)
                    self.selected_version = available_versions[0]
                    self.download_button.config(state=tk.NORMAL)
                else:
                    self.download_button.config(state=tk.DISABLED)
            else:
                self.download_button.config(state=tk.DISABLED)

        except Exception as e:
            print(f"获取版本列表失败: {str(e)}")

    def on_version_select(self, version_info):
        if version_info.level == 0:
            self.download_button.config(state=tk.DISABLED)
        else:
            self.selected_version = version_info
            self.download_button.config(state=tk.NORMAL)

    def show_changelog(self, version_info):
        log_window = tk.Toplevel(self.root)
        log_window.title(f"更新日志 - {version_info.version} ({version_info.ver_code})")
        
        # 设置和保存窗口位置
        self.set_window_position(log_window, "changelog")
        log_window.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(log_window, "changelog"))

        self.set_window_icon(log_window)

        log_frame = ttk.Frame(log_window)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        changelog_text = tk.Text(log_frame, height=10)
        changelog_text.insert(tk.END, version_info.changelog)
        changelog_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(log_frame, orient="vertical", command=changelog_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        changelog_text.configure(yscrollcommand=scrollbar.set)

        ttk.Button(log_window, text="确定", command=lambda: self.close_window(log_window, "changelog")).pack(pady=10)

    def check_for_updates(self, user_triggered=False):
        try:
            # 根据系统架构选择不同的 version.ini 文件
            if SYSTEM_ARCH == 'x86':
                version_file = "version-32.ini"
            elif SYSTEM_ARCH == 'x64':
                version_file = "version.ini"
            elif SYSTEM_ARCH == 'arm64':
                version_file = "version-64.ini"
            else:
                version_file = "version.ini"  # 默认使用 version.ini

            url = f"https://api17-2e40-yzlty.ru2023.top/{version_file}"
            response = requests.get(url, headers=HEADERS, timeout=10)
            response.raise_for_status()

            latest_ver = None
            latest_ver_code = None
            latest_changelog = ""
            latest_url = None
            notice = ""
            in_changelog = False

            for line in response.text.splitlines():
                line = line.strip()
                if line.startswith('ver='):
                    latest_ver = line[4:]
                elif line.startswith('changelog='):
                    latest_changelog = line[10:].replace('\\n', '\n')
                    in_changelog = True
                elif line.startswith('ver_code='):
                    latest_ver_code = line[9:]
                elif line.startswith('url='):
                    latest_url = line[4:]
                elif line.startswith('notice='):
                    notice = line[7:].replace('\\n', '\n')
                elif in_changelog:
                    latest_changelog += '\n' + line

            if latest_ver and latest_changelog and latest_ver_code and latest_url:
                if version.parse(latest_ver) > version.parse(CURRENT_VERSION):
                    self.show_update_dialog(latest_ver, latest_ver_code, latest_changelog, latest_url)
                    print(f"新版本 v{latest_ver} ({latest_ver_code}) 可用，当前版本 v{CURRENT_VERSION} ({CURRENT_VER_CODE}) 已不是最新")
                else:
                    print(f"当前已是最新版本 ({CURRENT_VERSION} ({CURRENT_VER_CODE}))")
                    if user_triggered:
                        messagebox.showinfo("更新检查", f"当前已是最新版本: v{CURRENT_VERSION} ({CURRENT_VER_CODE})")

            self.notice_label.config(text=notice)

        except Exception as e:
            print(f"检查更新失败: {str(e)}")

    def on_check_for_updates(self):
        self.check_for_updates(user_triggered=True)

    def show_update_dialog(self, latest_ver, latest_ver_code, latest_changelog, latest_url):
        self.update_dialog = tk.Toplevel(self.root)
        self.update_dialog.title("更新可用")
        
        # 设置和保存窗口位置
        self.set_window_position(self.update_dialog, "update")
        self.update_dialog.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(self.update_dialog, "update"))

        self.set_window_icon(self.update_dialog)

        update_info_frame = ttk.Frame(self.update_dialog)
        update_info_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        ttk.Label(update_info_frame, text=f"新版本: {latest_ver} ({latest_ver_code})").pack(pady=10)

        changelog_frame = ttk.Frame(update_info_frame)
        changelog_frame.pack(fill=tk.BOTH, expand=True)

        changelog_text = tk.Text(changelog_frame, height=10)
        changelog_text.insert(tk.END, latest_changelog)
        changelog_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(changelog_frame, orient="vertical", command=changelog_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        changelog_text.configure(yscrollcommand=scrollbar.set)

        button_frame = ttk.Frame(update_info_frame)
        button_frame.pack(fill=tk.X, pady=10)

        ttk.Button(button_frame, text="下载更新", command=lambda: self.download_update(latest_url)).pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="稍后提醒", command=lambda: self.close_window(self.update_dialog, "update")).pack(side=tk.RIGHT, padx=10)

        self.update_dialog.transient(self.root)
        self.update_dialog.grab_set()

    def download_update(self, url):
        try:
            response = requests.get(url, headers=HEADERS, stream=True)
            response.raise_for_status()

            updater_dir = os.getcwd()
            os.makedirs(updater_dir, exist_ok=True)
            save_path = os.path.join(updater_dir, url.split('/')[-1])
            total_size = int(response.headers.get('Content-Length', 0))

            if response.status_code == 304:
                print("资源未修改")
                return

            self.download_window = tk.Toplevel(self.root)
            self.download_window.title("下载进度")
            
            # 设置和保存窗口位置
            self.set_window_position(self.download_window, "download")
            self.download_window.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(self.download_window, "download"))

            self.set_window_icon(self.download_window)

            progress_frame = ttk.LabelFrame(self.download_window, text="下载进度", padding="10")
            progress_frame.pack(fill=tk.X, pady=10)
            self.progress_bar = ttk.Progressbar(progress_frame, orient=tk.HORIZONTAL, mode='determinate')
            self.progress_bar.pack(pady=10, fill=tk.X)
            self.progress_info = ttk.Label(progress_frame, text="")
            self.progress_info.pack(pady=5)

            log_frame = ttk.LabelFrame(self.download_window, text="日志", padding="10")
            log_frame.pack(fill=tk.BOTH, expand=True, pady=10)
            self.log_text = tk.Text(log_frame, height=10, state=tk.DISABLED)
            self.log_text.pack(fill=tk.BOTH, expand=True)

            tracker = DownloadTracker(total_size)
            self.progress_bar['maximum'] = total_size

            def download_task():
                nonlocal tracker
                with open(save_path, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        if chunk:
                            f.write(chunk)
                            tracker.update(len(chunk))
                            self.update_progress(tracker)

                # 下载完成后创建临时文件和更新脚本
                self.create_update_files(save_path)
                self.download_window.destroy()
                if hasattr(self, 'update_dialog'):
                    self.update_dialog.destroy()

                # 运行更新脚本并退出当前程序
                try:
                    subprocess.Popen(self.update_bat_path, shell=True)
                    self.root.destroy()
                except Exception as e:
                    messagebox.showerror("更新失败", f"无法启动更新脚本: {str(e)}", parent=self.root)

            Thread(target=download_task).start()

        except Exception as e:
            print(f"更新下载失败: {str(e)}")

    def start_download(self):
        if not self.is_channel_selected or not self.selected_version or not self.selected_thread_count.get():
            messagebox.showwarning("警告", "请选择更新通道和下载线程数后再开始下载")
            return

        if not self.path_var.get():
            messagebox.showerror("错误", "请选择路径")
            return

        download_url = self.selected_version.url

        if not download_url:
            messagebox.showerror("错误", "无法获取下载链接, 请检查版本信息")
            return

        save_dir = self.path_var.get()
        save_path = os.path.join(save_dir, download_url.split('/')[-1])

        try:
            response = requests.get(download_url, headers=HEADERS, stream=True)
            response.raise_for_status()
            total_size = int(response.headers.get('Content-Length', 0))

            if response.status_code == 3004:
                print("资源未修改")
                return

            self.download_window = tk.Toplevel(self.root)
            self.download_window.title("下载进度")
            
            # 设置和保存窗口位置
            self.set_window_position(self.download_window, "download")
            self.download_window.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(self.download_window, "download"))

            self.set_window_icon(self.download_window)

            progress_frame = ttk.LabelFrame(self.download_window, text="下载进度", padding="10")
            progress_frame.pack(fill=tk.X, pady=10)
            self.progress_bar = ttk.Progressbar(progress_frame, orient=tk.HORIZONTAL, mode='determinate')
            self.progress_bar.pack(pady=10, fill=tk.X)
            self.progress_info = ttk.Label(progress_frame, text="")
            self.progress_info.pack(pady=5)

            log_frame = ttk.LabelFrame(self.download_window, text="日志", padding="10")
            log_frame.pack(fill=tk.BOTH, expand=True, pady=10)
            self.log_text = tk.Text(log_frame, height=10, state=tk.DISABLED)
            self.log_text.pack(fill=tk.BOTH, expand=True)

            tracker = DownloadTracker(total_size)
            self.progress_bar['maximum'] = total_size

            num_threads = self.selected_thread_count.get()
            chunk_size = total_size // num_threads

            def download_range(start, end, part_index):
                headers = HEADERS.copy()
                headers['Range'] = f'bytes={start}-{end}'
                response = requests.get(download_url, headers=headers, stream=True)
                response.raise_for_status()

                part_path = f"{save_path}.part{part_index}"
                with open(part_path, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        if chunk:
                            f.write(chunk)
                            tracker.update(len(chunk))
                            self.update_progress(tracker)

                return part_path

            def download_task():
                nonlocal tracker
                ranges = []
                for i in range(num_threads):
                    start = i * chunk_size
                    end = start + chunk_size - 1
                    if i == num_threads - 1:
                        end = total_size - 1
                    ranges.append((start, end, i))

                with ThreadPoolExecutor(max_workers=num_threads) as executor:
                    futures = [executor.submit(download_range, start, end, i) for start, end, i in ranges]
                    part_files = [future.result() for future in futures]

                with open(save_path, 'wb') as f:
                    for part_file in sorted(part_files, key=lambda x: int(x.split('.')[-1].split('part')[-1])):
                        with open(part_file, 'rb') as part_f:
                            f.write(part_f.read())
                        os.remove(part_file)

                # 如果启用了自动更新，则执行解压操作
                if self.auto_update_var.get():
                    self.extract_and_update(save_path)
                else:
                    messagebox.showinfo("下载完成", f"下载完成, 文件已保存到: {save_path}", parent=self.download_window)

                self.download_window.destroy()
                if hasattr(self, 'update_dialog'):
                    self.update_dialog.destroy()

            Thread(target=download_task).start()

        except Exception as e:
            print(f"下载失败: {str(e)}")
            messagebox.showerror("下载失败", "下载过程中发生错误, 请重试", parent=self.download_window)

    def create_update_files(self, save_path):
        new_program_path = save_path

        # 创建临时文件
        with open(self.temp_file_path, 'w') as temp_file:
            temp_file.write(f"old_program={self.old_program_path}\n")
            temp_file.write(f"new_program={new_program_path}\n")

        # 创建更新脚本
        with open(self.update_bat_path, 'w') as bat_file:
            bat_file.write(f"@echo off\n")
            bat_file.write(f"taskkill /F /IM {os.path.basename(self.old_program_path)}\n")
            bat_file.write(f"del /F /Q {self.old_program_path}\n")
            bat_file.write(f"move /Y {new_program_path} {os.path.dirname(self.old_program_path)}\n")
            bat_file.write(f"{os.path.basename(new_program_path)}\n")

    def update_progress(self, tracker):
        current_time = time.time()
        if not hasattr(self, 'last_update_time') or current_time - self.last_update_time >= 0.4:
            progress = tracker.get_progress()
            self.progress_bar['value'] = progress['downloaded']
            self.progress_info.config(
                text=f"{progress['percent']:.2f}% - {tracker._human_size(progress['downloaded'])}/{tracker._human_size(progress['total'])} - 下载速度: {tracker._human_size(progress['speed'])}/s - 预计剩余时间: {tracker._format_time(progress['remaining'])}"
            )
            self.log_text.configure(state=tk.NORMAL)
            self.log_text.insert(tk.END, f"{progress['percent']:.2f}% - {tracker._human_size(progress['downloaded'])}/{tracker._human_size(progress['total'])} - 速度: {tracker._human_size(progress['speed'])}/s - 预计需要: {tracker._format_time(progress['remaining'])}\n")
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.DISABLED)
            self.last_update_time = current_time

    def choose_path(self):
        if self.auto_update_var.get():
            # 选择客户端目录
            while True:
                client_dir = filedialog.askdirectory(
                    initialdir=self.client_dir.get() if self.client_dir.get() else self.path_var.get(),
                    title="选择重聚未来客户端目录"
                )
                if not client_dir:
                    return  # 用户取消选择
                if os.path.exists(os.path.join(client_dir, "Reunion.exe")):
                    self.client_dir.set(client_dir)
                    self.path_var.set(client_dir)
                    break
                else:
                    messagebox.showwarning(
                        "警告",
                        f"所选目录可能不是重聚未来客户端目录, 请重新选择",
                        parent=self.root
                    )
        else:
            # 选择离线包下载目录
            download_dir = filedialog.askdirectory(
                initialdir=self.download_dir.get() if self.download_dir.get() else DEFAULT_DOWNLOAD_DIR,
                title="选择离线包下载目录"
            )
            if download_dir:
                self.download_dir.set(download_dir)
                self.path_var.set(download_dir)

    def on_auto_update_toggle(self):
        self.auto_update_value = self.auto_update_var.get()
        self.path_var.set("")  # 清空路径显示
        if self.auto_update_var.get():
            # 启用自动更新模式，尝试加载之前保存的客户端目录
            if self.client_dir.get() and os.path.exists(self.client_dir.get()) and os.path.exists(os.path.join(self.client_dir.get(), "Reunion.exe")):
                self.path_var.set(self.client_dir.get())
            messagebox.showinfo("提示", "已启用自动更新模式, 请选择客户端目录", parent=self.root)
        else:
            # 禁用自动更新模式，尝试加载之前保存的下载目录
            if self.download_dir.get() and os.path.exists(self.download_dir.get()):
                self.path_var.set(self.download_dir.get())
            messagebox.showinfo("提示", "已禁用自动更新模式, 请选择离线包下载目录", parent=self.root)

    def extract_and_update(self, archive_path):
        try:
            # 检查7z是否可用
            if not os.path.exists(f"7z-{SYSTEM_ARCH}.exe") or not os.path.exists(f"7z-{SYSTEM_ARCH}.dll"):
                messagebox.showerror("错误", "7z.exe 或 7z.dll 文件缺失, 请确保它们与本程序在同一目录下", parent=self.download_window)
                os.remove(archive_path)
                return

            # 获取客户端目录
            client_dir = self.client_dir.get()

            # 解压命令
            extract_cmd = f'7z-{SYSTEM_ARCH}.exe x "{archive_path}" -o"{client_dir}" -y'

            # 执行解压
            subprocess.run(extract_cmd, shell=True, check=True)

            # 删除下载的压缩包
            os.remove(archive_path)

            messagebox.showinfo("更新完成", f"重聚未来客户端已成功更新, 请手动启动客户端", parent=self.download_window)

        except subprocess.CalledProcessError as e:
            messagebox.showerror("解压失败", f"解压过程中发生错误: {str(e)}", parent=self.download_window)
        except Exception as e:
            messagebox.showerror("更新失败", f"更新过程中发生错误: {str(e)}", parent=self.download_window)

    def on_closing(self):
        """保存主窗体位置并关闭程序"""
        self.save_window_position(self.root, "main")
        if messagebox.askokcancel("退出", "确定要退出程序吗?"):
            # 删除释放的 7z 文件
            delete_7z_files()
            # 关闭程序时删除临时文件
            try:
                if os.path.exists(self.temp_file_path):
                    os.remove(self.temp_file_path)
                if os.path.exists(self.update_bat_path):
                    os.remove(self.update_bat_path)
            except Exception as e:
                print(f"删除临时文件时出错: {str(e)}")
            self.root.destroy()

    def on_child_closing(self, window, window_name):
        """保存子窗体位置并关闭"""
        self.save_window_position(window, window_name)
        window.destroy()

    def close_window(self, window, window_name):
        """关闭窗体并保存位置"""
        self.save_window_position(window, window_name)
        window.destroy()

    def show_secret_window(self, event=None):
        """显示隐藏的指令输入窗口"""
        secret_window = tk.Toplevel(self.root)
        secret_window.title("指令输入")
        secret_window.transient(self.root)
        secret_window.grab_set()

        # 设置和保存窗口位置和大小
        self.set_window_position(secret_window, "secret")
        secret_window.geometry("400x300")
        secret_window.minsize(400, 300)

        self.set_window_icon(secret_window)

        # 模式选择区域
        mode_frame = ttk.LabelFrame(secret_window, text="模式选择", padding="10")
        mode_frame.pack(fill=tk.X, pady=10)

        self.mode_var = tk.StringVar()

        normal_mode_btn = ttk.Radiobutton(
            mode_frame,
            text="普通模式",
            variable=self.mode_var,
            value="normal",
            command=self.on_mode_select
        )
        normal_mode_btn.pack(side=tk.LEFT, padx=10)

        developer_mode_btn = ttk.Radiobutton(
            mode_frame,
            text="开发者模式",
            variable=self.mode_var,
            value="developer",
            command=self.on_mode_select
        )
        developer_mode_btn.pack(side=tk.LEFT, padx=10)

        # 功能区域
        self.function_frame = ttk.Frame(secret_window)
        self.function_frame.pack(fill=tk.BOTH, expand=True, pady=10)

        # 默认不显示任何功能区域
        self.hide_function_area()

        # 绑定窗口关闭事件
        secret_window.protocol("WM_DELETE_WINDOW", lambda: self.on_child_closing(secret_window, "secret"))

    def hide_function_area(self):
        # 隐藏普通模式功能区域
        if hasattr(self, 'normal_instruction_label'):
            self.normal_instruction_label.pack_forget()
        if hasattr(self, 'normal_entry'):
            self.normal_entry.pack_forget()
        if hasattr(self, 'normal_button'):
            self.normal_button.pack_forget()

        # 隐藏开发者模式功能区域
        if hasattr(self, 'developer_instruction_label'):
            self.developer_instruction_label.pack_forget()
        if hasattr(self, 'developer_entry'):
            self.developer_entry.pack_forget()
        if hasattr(self, 'developer_button'):
            self.developer_button.pack_forget()

    def show_copyright_info(self):
        """显示版权信息"""
        window_name = "copyright"
        copyright_window = tk.Toplevel(self.root)
        copyright_window.title("版权信息")
        copyright_window.geometry("500x400")
        copyright_window.minsize(500, 400)
        copyright_window.transient(self.root)
        copyright_window.grab_set()

        self.set_window_icon(copyright_window)

        copyright_frame = ttk.Frame(copyright_window)
        copyright_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        copyright_text = tk.Text(copyright_frame, height=15, wrap=tk.WORD)
        copyright_text.insert(tk.END, (
            "版权所有 (C) 2025 Candy. 保留所有权利.\n\n"
            "未经授权, 禁止任何个人或组织对本软件进行复制、修改或分发.\n\n"
            "本软件仅供个人学习和研究使用.\n\n"
            "网址: https://www.yra2.com\n\n"
            "版权声明: 本软件受版权法保护, 未经许可不得擅自使用或传播, 侵权必究！"
        ))
        copyright_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        copyright_text.configure(state=tk.DISABLED)

        def on_closing():
            self.save_window_position(copyright_window, window_name)
            copyright_window.destroy()

        ttk.Button(copyright_window, text="关闭", command=on_closing).pack(pady=10)
        copyright_window.protocol("WM_DELETE_WINDOW", on_closing)

    def on_mode_select(self):
        self.hide_function_area()  # 隐藏之前的功能区域

        selected_mode = self.mode_var.get()
        if selected_mode == "normal":
            # 显示普通模式功能区域
            self.normal_instruction_label = ttk.Label(self.function_frame, text="普通模式: 输入数字执行快捷指令(对应数字详见目录下的ReadMe.txt)")
            self.normal_instruction_label.pack(pady=5)

            self.normal_entry = ttk.Entry(self.function_frame, width=50)
            self.normal_entry.pack(pady=5)

            self.normal_button = ttk.Button(self.function_frame, text="执行")
            self.normal_button.pack(pady=5)

            def execute_normal_function():
                function = self.normal_entry.get().strip()
                if function == "1":
                    webbrowser.open("https://www.yra2.com")
                elif function == "0320":
                    webbrowser.open("https://ycn4cxc6piui.feishu.cn/wiki/WoUywmd4fibtt8kpwNmcDvY2nKh")
                else:
                    messagebox.showwarning("错误", "未知功能")

            self.normal_button.config(command=execute_normal_function)

        elif selected_mode == "developer":
            # 显示开发者模式功能区域
            self.developer_instruction_label = ttk.Label(self.function_frame, text="开发者模式: 输入指令")
            self.developer_instruction_label.pack(pady=5)

            self.developer_entry = ttk.Entry(self.function_frame, width=50)
            self.developer_entry.pack(pady=5)

            self.developer_button = ttk.Button(self.function_frame, text="提交")
            self.developer_button.pack(pady=5)

            def check_developer_instruction():
                instruction = self.developer_entry.get().strip()
                if instruction == "baka！":
                    self.show_copyright_info()
                else:
                    messagebox.showwarning("错误", "指令错误")

            self.developer_button.config(command=check_developer_instruction)


if __name__ == "__main__":
    root = tk.Tk()
    app = DownloaderApp(root)
    app.set_window_icon(root)
    root.mainloop()
