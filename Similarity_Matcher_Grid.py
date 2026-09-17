import os
import re
import sys
import random
import threading
import subprocess
import ctypes
from ctypes import wintypes
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from rapidfuzz import fuzz

# Try importing modern audio metadata libraries for robust tag extraction
has_tinytag = False
try:
    from tinytag import TinyTag
    has_tinytag = True
except ImportError:
    pass

# Keep scan results around.
# Globals to persist scanned data in RAM for instant post-scan filtering
cached_pair_matches = []

cached_track_metadata = {}
file_paths = {} # Track Treeview item IDs to actual absolute file paths

# Time display helper.
def format_duration(seconds):
    """Converts seconds into a clean MM:SS string format."""
    if not seconds or seconds <= 0:
        return "Unknown"
    mins = int(seconds // 60)
    secs = int(seconds % 60)
    return f"{mins:02d}:{secs:02d}"

# Read tags, then try the filename.
def get_audio_metadata(path):
    """
    Extracts Artist, Year, and Duration metadata.
    First tries TinyTag (covers m4a, mp3, flac, wav),
    then falls back to parsing common 'Artist - Title' filename formats.
    """
    artist = "Unknown"
    year = "Unknown"
    length = "Unknown"
    
    # 1. Primary Method: Use TinyTag library if installed
    if has_tinytag:
        try:
            tag = TinyTag.get(path)
            if tag.artist:
                artist = tag.artist.strip()
            if tag.year:
                # Extract 4-digit year from string/date
                year_match = re.search(r'\b\d{4}\b', str(tag.year))
                if year_match:
                    year = year_match.group(0)
            if tag.duration:
                length = format_duration(tag.duration)
            return artist, year, length
        except Exception:
            pass # Fall back to filename parsing if the tag format is corrupted

    # 2. Fallback Method: Structured Filename Parsing (e.g., "Artist - Song Name")
    filename_clean = os.path.splitext(os.path.basename(path))[0]
    if " - " in filename_clean:
        parts = filename_clean.split(" - ", 1)
        artist_part = parts[0].strip()
        # Clean up common numbers/track indexes at the start of filenames
        artist_part = re.sub(r'^\d+[\s._-]*', '', artist_part)
        if artist_part:
            artist = artist_part

    return artist, year, length

# Make artist comparisons consistent.
def normalize_artist_name(artist_name):
    """Normalizes artist names to lowercase alphanumeric characters for accurate comparisons."""
    if not artist_name or artist_name.lower() == "unknown":
        return "unknown"
    return re.sub(r'\W+', '', artist_name.strip().lower())

def send_to_recycle_bin(path):
    """
    Safely moves a file to the Recycle Bin.
    Uses native Windows Shell APIs via ctypes to prevent permanent file loss.
    """
    if not os.path.exists(path):
        return False
        
    if sys.platform == 'win32':
        class SHFILEOPSTRUCTW(ctypes.Structure):
            _fields_ = [
                ("hwnd", wintypes.HWND),
                ("wFunc", wintypes.UINT),
                ("pFrom", wintypes.LPCWSTR),
                ("pTo", wintypes.LPCWSTR),
                ("fFlags", ctypes.c_ushort),
                ("fAnyOperationsAborted", wintypes.BOOL),
                ("hNameMappings", wintypes.LPVOID),
                ("lpszProgressTitle", wintypes.LPCWSTR)
            ]
        FO_DELETE = 3
        FOF_ALLOWUNDO = 0x40
        FOF_NOCONFIRMATION = 0x10
        FOF_NOERRORUI = 0x0400
        
        p_from = path + "\0\0"
        
        fileop = SHFILEOPSTRUCTW()
        fileop.hwnd = None
        fileop.wFunc = FO_DELETE
        fileop.pFrom = p_from
        fileop.pTo = None
        fileop.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_NOERRORUI
        
        SHFileOperationW = ctypes.windll.shell32.SHFileOperationW
        SHFileOperationW.argtypes = [ctypes.POINTER(SHFILEOPSTRUCTW)]
        SHFileOperationW.restype = ctypes.c_int
        
        result = SHFileOperationW(ctypes.byref(fileop))
        return result == 0
    else:
        try:
            os.remove(path)
            return True
        except Exception:
            return False

# Turn filenames into matching words.
def clean_song_name(filename):
    """Removes extensions, track numbers, tags, and common 'stop words' in memory for clean matching."""
    name_without_ext = os.path.splitext(filename)[0]
    name_lower = name_without_ext.lower()
    
    name_lower = re.sub(r'^\d+[\s._-]*', '', name_lower)
    name_lower = re.sub(r'\b\d{4}\b', ' ', name_lower)
    
    tags_to_remove = [
        r'\(lyrics\)', r'\[lyrics\]', 
        r'\(official video\)', r'\[official video\]',
        r'\(official audio\)', r'\[official audio\]',
        r'\(clean\)', r'\[clean\]',
        r'\(explicit\)', r'\[explicit\]',
        r'\(remix\)', r'\[remix\]',
        r'\(remaster\)', r'\[remaster\]',
        r'\(remastered\)', r'\[remastered\]',
        r'\(live\)', r'\[live\]',
        r'\(acoustic\)', r'\[acoustic\]',
        r'\(version\)', r'\[version\]',
        r'\(radio edit\)', r'\[radio edit\]',
        r'\(original\)', r'\[original\]',
        r'-'
    ]
    
    for tag in tags_to_remove:
        name_lower = re.sub(tag, ' ', name_lower)
        
    name_lower = name_lower.replace("'", "").replace("’", "")
    words = re.findall(r'\b\w+\b', name_lower)
    
    stop_words = {
        'the', 'a', 'an', 'and', 'or', 'of', 'to', 'in', 'is', 'it', 
        'feat', 'ft', 'with', 'by', 'on', 'at', 'for', 'from', 'as', 'but',
        'remaster', 'remastered', 'live', 'acoustic', 'version', 'radio', 
        'edit', 'mix', 'original', 'bonus', 'track', 'album', 'single',
        'mono', 'stereo', 'high', 'quality', 'hq', 'audio', 'video'
    }
    
    clean_words = [w for w in words if w not in stop_words and len(w) > 1]
    return clean_words

# Find supported audio files below a folder.
def find_audio_files(root_folder):
    """Recursively walks subfolders collecting absolute paths individually."""
    valid_extensions = ('.mp3', '.wav', '.flac', '.m4a', '.ogg', '.wma')
    audio_paths = []
    for dirpath, _, filenames in os.walk(root_folder):
        for filename in filenames:
            if filename.lower().endswith(valid_extensions):
                audio_paths.append(os.path.abspath(os.path.join(dirpath, filename)))
    return audio_paths

def generate_soft_color():
    """Generates a soft, highly readable pastel hex color for row grouping."""
    pastels = [
        "#E6F2FF", "#F0E6FF", "#E6FFE6", "#FFE6E6", "#FFE6F9", 
        "#FFFFE6", "#E6FFFF", "#FFF0E6", "#EBF2FA", "#F5FFF0"
    ]
    return random.choice(pastels)

# Rebuild the visible table from cached results.
def refresh_grid():
    """Instantly clears the Treeview grid and re-populates it from RAM cache."""
    global cached_pair_matches, cached_track_metadata, file_paths
    
    tree.delete(*tree.get_children())
    file_paths.clear()
    
    if not cached_pair_matches:
        return

    same_artist_only = same_artist_var.get()
    
    filtered_pairs = []
    for match in cached_pair_matches:
        p1, p2 = match['path1'], match['path2']
        
        if same_artist_only:
            artist1, _, _ = cached_track_metadata.get(p1, ("Unknown", "Unknown", "Unknown"))
            artist2, _, _ = cached_track_metadata.get(p2, ("Unknown", "Unknown", "Unknown"))
            norm_artist1 = normalize_artist_name(artist1)
            norm_artist2 = normalize_artist_name(artist2)
            
            if norm_artist1 == "unknown" or norm_artist2 == "unknown" or norm_artist1 != norm_artist2:
                continue
                
        filtered_pairs.append(match)

    if not filtered_pairs:
        lbl_status.config(text="No matching duplicates found under active filters.")
        return

    adjacency = {}
    pair_details = {}
    
    for match in filtered_pairs:
        p1, p2 = match['path1'], match['path2']
        if p1 not in adjacency:
            adjacency[p1] = set()
        if p2 not in adjacency:
            adjacency[p2] = set()
        adjacency[p1].add(p2)
        adjacency[p2].add(p1)
        
        pair_key = tuple(sorted([p1, p2]))
        pair_details[pair_key] = match

    visited = set()
    groups = []
    
    for node in adjacency:
        if node not in visited:
            group = []
            queue = [node]
            visited.add(node)
            while queue:
                curr = queue.pop(0)
                group.append(curr)
                for neighbor in adjacency[curr]:
                    if neighbor not in visited:
                        visited.add(neighbor)
                        queue.append(neighbor)
            groups.append(group)

    group_scores = []
    for group in groups:
        max_pct = 0.0
        max_raw = 0
        for i in range(len(group)):
            for j in range(i + 1, len(group)):
                key = tuple(sorted([group[i], group[j]]))
                if key in pair_details:
                    details = pair_details[key]
                    if details['pct_score'] > max_pct:
                        max_pct = details['pct_score']
                    if details['raw_match'] > max_raw:
                        max_raw = details['raw_match']
        group_scores.append((max_pct, max_raw, group))

    group_scores.sort(key=lambda x: (x[0], x[1]), reverse=True)

    group_id_counter = 0
    visible_match_count = 0
    
    for max_pct, max_raw, file_list in group_scores:
        file_list.sort(key=lambda p: os.path.basename(p))
        
        color_tag = f"group_{group_id_counter}"
        group_id_counter += 1
        hex_color = generate_soft_color()
        tree.tag_configure(color_tag, background=hex_color)
        
        for path in file_list:
            artist, year, length = cached_track_metadata.get(path, ("Unknown", "Unknown", "Unknown"))
            filename = os.path.basename(path)
            folder = os.path.dirname(path)
            
            best_pct = 0.0
            best_raw = 0
            best_shared_words = []
            
            for other_path in file_list:
                if other_path == path:
                    continue
                key = tuple(sorted([path, other_path]))
                if key in pair_details:
                    details = pair_details[key]
                    if details['pct_score'] > best_pct:
                        best_pct = details['pct_score']
                        best_raw = details['raw_match']
                        best_shared_words = details['matched_words']
            
            shared_str = ", ".join(best_shared_words) if best_shared_words else "Group Core"
            match_display = f"{best_pct:.1f}% Match" if best_pct > 0 else "Group Core"
            raw_display = f"{best_raw} Words" if best_raw > 0 else "Group Core"
            
            item_id = tree.insert("", tk.END, values=(
                filename, artist, year, length, match_display, raw_display, shared_str, folder
            ), tags=(color_tag,))
            file_paths[item_id] = path
            visible_match_count += 1
            
        sep_id = tree.insert("", tk.END, values=("", "", "", "", "", "", "", ""), tags=("separator",))
        file_paths[sep_id] = None
        
    tree.tag_configure("separator", background="#EAEAEA")
    lbl_status.config(text=f"Grid populated. Displaying {len(group_scores)} groups containing {visible_match_count} unique files.")

# Heavy scan work runs away from the main GUI loop.
def processing_worker(target_folder, tree_widget, root_window, pbar_total, lbl_status, btn_browse, chk_widget):
    global cached_pair_matches, cached_track_metadata
    
    def update_ui_status(status_text, total_val=None):
        if status_text:
            lbl_status.config(text=status_text)
        if total_val is not None:
            pbar_total['value'] = total_val
        root_window.update_idletasks()

    cached_pair_matches = []
    cached_track_metadata = {}
    
    root_window.after(0, lambda: tree_widget.delete(*tree_widget.get_children()))

    all_tracks = find_audio_files(target_folder)
    total_files = len(all_tracks)
    
    if not all_tracks:
        update_ui_status("Ready.")
        root_window.after(0, lambda: messagebox.showinfo("Finished", "No audio files found."))
        root_window.after(0, lambda: btn_browse.config(state=tk.NORMAL))
        root_window.after(0, lambda: chk_widget.config(state=tk.NORMAL))
        return

    update_ui_status("Gathering audio track tags and metadata...")

    track_token_map = {}
    local_metadata_cache = {}
    for idx, path in enumerate(all_tracks, 1):
        filename = os.path.basename(path)
        track_token_map[path] = set(clean_song_name(filename))
        local_metadata_cache[path] = get_audio_metadata(path)
        
        if idx % 100 == 0 or idx == total_files:
            progress_pct = (idx / total_files) * 50
            update_ui_status(f"Reading file metadata: {idx}/{total_files}...", total_val=progress_pct)

    total_unique_pairs = (total_files * (total_files - 1)) // 2

    update_ui_status(f"Scanning {total_unique_pairs} unique name pairs...")

    local_pair_matches = []
    pairs_checked = 0

    for i in range(total_files):
        for j in range(i + 1, total_files):
            path1 = all_tracks[i]
            path2 = all_tracks[j]
            
            words1 = track_token_map[path1]
            words2 = track_token_map[path2]
            
            matching_words = words1.intersection(words2)
            match_count = len(matching_words)
            
            if match_count > 0:
                if match_count == 1 and len(list(matching_words)[0]) <= 3:
                    pairs_checked += 1
                    continue
                
                name1 = os.path.splitext(os.path.basename(path1))[0]
                name2 = os.path.splitext(os.path.basename(path2))[0]
                
                pct_score = fuzz.token_sort_ratio(name1, name2)
                
                if pct_score >= 55:
                    local_pair_matches.append({
                        'path1': path1,
                        'path2': path2,
                        'pct_score': pct_score,
                        'raw_match': match_count,
                        'matched_words': list(matching_words)
                    })
                
            pairs_checked += 1
            if pairs_checked % 3000 == 0 or pairs_checked == total_unique_pairs:
                macro_percent = 50 + ((pairs_checked / total_unique_pairs) * 50)
                update_ui_status(f"Scanning name pairs: {pairs_checked}/{total_unique_pairs}...", total_val=macro_percent)

    local_pair_matches.sort(key=lambda x: x['pct_score'], reverse=True)


    cached_pair_matches = local_pair_matches
    cached_track_metadata = local_metadata_cache

    update_ui_status("Rendering grid rows...")
    
    def on_finalize():
        refresh_grid()
        update_ui_status("Analysis complete.", total_val=100)
        messagebox.showinfo("Done", f"Analysis complete! Found {len(cached_pair_matches)} matching pairs.")
        btn_browse.config(state=tk.NORMAL)
        chk_widget.config(state=tk.NORMAL)

    root_window.after(0, on_finalize)

def select_folder_and_start():
    selected_dir = filedialog.askdirectory(title="Select Music Root Folder")
    if selected_dir:
        lbl_status.config(text="Initializing path calculations...")
        btn_browse.config(state=tk.DISABLED)
        chk_same_artist.config(state=tk.DISABLED)
        
        threading.Thread(
            target=processing_worker, 
            args=(selected_dir, tree, root, progress_total, lbl_status, btn_browse, chk_same_artist),
            daemon=True
        ).start()

# Sort the current table column.
def sort_column(tree_widget, col_name, reverse_state):
    for item in tree_widget.get_children(""):
        col_values = tree_widget.item(item)["values"]
        if not col_values or col_values[0] == "":
            tree_widget.delete(item)

    items_list = [(tree_widget.set(item_id, col_name), item_id) for item_id in tree_widget.get_children("")]
    
    def numeric_parser(val_tuple):
        raw_val = val_tuple[0]
        # Convert MM:SS into total seconds for proper numerical sorting
        if ":" in str(raw_val):
            parts = str(raw_val).split(":")
            try:
                return int(parts[0]) * 60 + int(parts[1])
            except ValueError:
                pass
        clean_num = re.sub(r'[^\d\.]', '', str(raw_val))
        try:
            return float(clean_num)
        except ValueError:
            return str(raw_val).lower()

    if col_name in ("match_score", "raw_score", "year", "length"):
        items_list.sort(key=numeric_parser, reverse=reverse_state)
    else:
        items_list.sort(key=lambda x: str(x[0]).lower(), reverse=reverse_state)

    for index, (_, item_id) in enumerate(items_list):
        tree_widget.move(item_id, "", index)

    tree_widget.heading(col_name, command=lambda: sort_column(tree_widget, col_name, not reverse_state))

def handle_double_click(event):
    selected_item = tree.selection()
    if not selected_item:
        return
        
    filepath = file_paths.get(selected_item[0])
    if filepath and os.path.exists(filepath):
        try:
            if sys.platform == 'win32':
                subprocess.run(['explorer', '/select,', os.path.normpath(filepath)])
            elif sys.platform == 'darwin':
                subprocess.run(['open', '-R', filepath])
            else:
                subprocess.run(['xdg-open', os.path.dirname(filepath)])
        except Exception as e:
            messagebox.showerror("Error", f"Could not locate item path: {e}")

# Delete means recycle, not permanent removal.
def delete_selected_file(event=None):
    selected_item = tree.selection()
    if not selected_item:
        return
        
    filepath = file_paths.get(selected_item[0])
    if not filepath or not os.path.exists(filepath):
        return
        
    filename = os.path.basename(filepath)
    success = send_to_recycle_bin(filepath)
    if success:
        file_paths.pop(selected_item[0], None)
        tree.delete(selected_item[0])
        lbl_status.config(text=f"Successfully moved '{filename}' to the Recycle Bin.")
    else:
        lbl_status.config(text=f"Failed to move '{filename}' to the Recycle Bin (File may be in use).")

# --- GUI Windows Construction Layout Engine ---
root = tk.Tk()
root.title("Advanced Filename Similarity Matcher Grid Engine")
root.geometry("1320x670")

style = ttk.Style()
style.theme_use("clam")
style.configure("Treeview", rowheight=24, font=("Arial", 9))
style.configure("Treeview.Heading", font=("Arial", 10, "bold"), background="#E1E1E1")

frame_top = tk.Frame(root)
frame_top.pack(pady=10, fill=tk.X)

lbl_instructions = tk.Label(frame_top, text="Select a directory to compare all audio filenames, extract metadata, and reveal duplicates:", font=("Arial", 10))
lbl_instructions.pack()

frame_buttons = tk.Frame(frame_top)
frame_buttons.pack(pady=8)

btn_browse = tk.Button(frame_buttons, text="Select Folder & Start Scan", command=select_folder_and_start, bg="#008CBA", fg="white", font=("Arial", 11, "bold"), padx=15, pady=5)
btn_browse.grid(row=0, column=0, padx=15)

same_artist_var = tk.BooleanVar(value=False)
chk_same_artist = tk.Checkbutton(
    frame_buttons, 
    text="Only group songs by the same artist", 
    variable=same_artist_var, 
    command=refresh_grid,
    font=("Arial", 10)
)
chk_same_artist.grid(row=0, column=1, padx=15)

lbl_status = tk.Label(root, text="System Ready. Double-click any row to show in File Explorer. Select row and press 'Delete' to recycle.", font=("Arial", 9, "italic"), fg="#555555")
lbl_status.pack(anchor="w", padx=20)

frame_progress = tk.Frame(root)
frame_progress.pack(fill=tk.X, padx=20, pady=5)

progress_total = ttk.Progressbar(frame_progress, orient="horizontal", length=200, mode="determinate")
progress_total.pack(fill=tk.X)

frame_table = tk.Frame(root)
frame_table.pack(pady=10, padx=20, fill=tk.BOTH, expand=True)

# Included "length" in the columns layout
columns = ("filename", "artist", "year", "length", "match_score", "raw_score", "shared_phrases", "folder_path")
tree = ttk.Treeview(frame_table, columns=columns, show="headings", selectmode="browse")

tree.heading("filename", text="File Name", command=lambda: sort_column(tree, "filename", False))
tree.heading("artist", text="Artist", command=lambda: sort_column(tree, "artist", False))
tree.heading("year", text="Year", command=lambda: sort_column(tree, "year", False))
tree.heading("length", text="Length", command=lambda: sort_column(tree, "length", False))
tree.heading("match_score", text="Similarity %", command=lambda: sort_column(tree, "match_score", False))
tree.heading("raw_score", text="Raw Word Match", command=lambda: sort_column(tree, "raw_score", False))
tree.heading("shared_phrases", text="Shared Title Phrases", command=lambda: sort_column(tree, "shared_phrases", False))
tree.heading("folder_path", text="Full Folder Location", command=lambda: sort_column(tree, "folder_path", False))

tree.column("filename", width=220, anchor="w")
tree.column("artist", width=140, anchor="w")
tree.column("year", width=60, anchor="center")
tree.column("length", width=70, anchor="center")
tree.column("match_score", width=110, anchor="center")
tree.column("raw_score", width=110, anchor="center")
tree.column("shared_phrases", width=180, anchor="w")
tree.column("folder_path", width=320, anchor="w")

scrollbar = ttk.Scrollbar(frame_table, orient=tk.VERTICAL, command=tree.yview)
tree.configure(yscrollcommand=scrollbar.set)
scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

tree.bind("<Double-1>", handle_double_click)
tree.bind("<Delete>", delete_selected_file)

root.mainloop()