from array import array
from bisect import bisect_left
import ctypes
from dataclasses import dataclass
from pathlib import Path
from queue import Empty, SimpleQueue
import re
import sys
import threading
import tkinter as tk
import tkinter.font as tkfont
from tkinter import messagebox, ttk
from typing import Callable


MIN_RESULT_FONT_SIZE = 8
MAX_RESULT_FONT_SIZE = 256
FIELD_RADIUS = 14
BACKGROUND = "#080808"
PANEL = "#151515"
INPUT_BACKGROUND = "#222222"
WHITE = "#f4f4f4"
ORANGE = "#ff8c00"
LIGHT_ORANGE = "#ffb347"
DARK_ORANGE = "#9a4b00"
MUTED = "#a0a0a0"
SEARCHING_TEXT = "Ищем совпадение\n..."
SEARCH_ANIMATION_INTERVAL_MS = 100

HEADER_PREFIX = "PiSearch\t"
DATA_FORMAT_HELP = (
    "Первая строка должна быть PiSearch<TAB>digits<TAB>1000000 или "
    "PiSearch<TAB>letters<TAB>1000000<TAB>English<TAB>ABCDEFGHIJKLMNOPQRSTUVWXYZ; "
    "далее идут данные. "
    "Для букв число знаков π указывает исходный ряд, поэтому символов должно быть вдвое меньше."
)


def application_directory() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


@dataclass(frozen=True)
class SearchResult:
    mode: str
    query: str
    sequence: str
    positions: array
    error: str | None = None


@dataclass(frozen=True)
class DataFile:
    path: Path
    kind: str
    decimal_places: int
    language: str | None
    alphabet: str | None
    encoding: str
    has_header: bool

    @property
    def key(self) -> str:
        return "digits" if self.kind == "digits" else f"letters:{self.language}"


@dataclass(frozen=True)
class DataSet:
    decimal_places: int
    digits: DataFile
    letters: dict[str, DataFile]


def _read_header(path: Path) -> DataFile | None:
    with path.open("rb") as data_file:
        header_bytes = data_file.readline(4096)
    if not header_bytes.startswith(HEADER_PREFIX.encode("ascii")):
        return None

    try:
        header = header_bytes.decode("utf-8-sig").rstrip("\r\n")
    except UnicodeError as error:
        raise ValueError(
            f"Некорректный заголовок файла данных: {path.name}. {DATA_FORMAT_HELP}"
        ) from error
    fields = header.split("\t")
    if fields[0] != "PiSearch":
        raise ValueError(
            f"Некорректный заголовок файла данных: {path.name}. {DATA_FORMAT_HELP}"
        )
    kind = fields[1]
    if kind not in ("digits", "letters"):
        raise ValueError(f"Неизвестный тип данных в файле: {path.name}")
    if not re.fullmatch(r"[1-9][0-9]*", fields[2]):
        raise ValueError(f"Некорректное число знаков π в файле: {path.name}")
    decimal_places = int(fields[2])
    language = fields[3].strip() if kind == "letters" and len(fields) == 5 else None
    alphabet = fields[4] if kind == "letters" and len(fields) == 5 else None
    if (
        (kind == "digits" and len(fields) != 3)
        or (
            kind == "letters"
            and (
                len(fields) != 5
                or not language
                or not alphabet
                or len(set(alphabet)) != len(alphabet)
                or any(
                    not character.isalpha() or character.upper() != character
                    for character in alphabet
                )
            )
        )
        or (kind == "letters" and decimal_places % 2)
    ):
        raise ValueError(f"Некорректный заголовок файла данных: {path.name}")
    return DataFile(path, kind, decimal_places, language, alphabet, "utf-8-sig", True)


def _payload(file: DataFile) -> str:
    content = file.path.read_text(encoding=file.encoding)
    if file.has_header:
        _, separator, content = content.partition("\n")
        if not separator:
            content = ""
    return "".join(content.split())


def load_sequence(file: DataFile) -> str:
    content = _payload(file)
    if file.kind == "digits":
        if (
            len(content) != file.decimal_places + 2
            or not content.startswith("3.")
            or not content[2:].isascii()
            or not content[2:].isdigit()
        ):
            raise ValueError(f"Некорректный файл данных: {file.path.name}")
        return content[0] + content[2:]
    expected_length = file.decimal_places // 2
    expected_length = file.decimal_places // 2
    alphabet = set(file.alphabet or "")
    content = content.upper()
    if len(content) != expected_length or any(
        character not in alphabet for character in content
    ):
        raise ValueError(f"Некорректный файл данных: {file.path.name}")
    return content


def _validate_library_presence(file: DataFile) -> None:
    with file.path.open("r", encoding=file.encoding) as data_file:
        if file.has_header:
            data_file.readline()
        while chunk := data_file.read(4096):
            payload = "".join(chunk.split())
            if not payload:
                continue
            if file.kind == "digits":
                if (
                    len(payload) < 3
                    or not payload.startswith("3.")
                    or not payload[2].isascii()
                    or not payload[2].isdigit()
                ):
                    raise ValueError(f"Некорректный файл данных: {file.path.name}")
            elif payload[0] not in set(file.alphabet or ""):
                raise ValueError(
                    f"Файл языка «{file.language}» не содержит символы его алфавита: {file.path.name}"
                )
            return
    if file.kind == "digits":
        raise ValueError(f"Файл не содержит числовые данные: {file.path.name}")
    raise ValueError(f"Файл не содержит буквенные данные: {file.path.name}")


def discover_data_files(directory: Path) -> DataSet:
    files = [
        file
        for path in sorted(directory.iterdir(), key=lambda item: item.name.casefold())
        if path.is_file()
        for file in [_read_header(path)]
        if file is not None
    ]
    if not files:
        raise ValueError(
            "Файлы библиотек PiSearch не найдены. Загрузите необходимые библиотеки "
            "с сайта программы."
        )

    groups = sorted({file.decimal_places for file in files})
    if len(groups) > 1:
        group_list = ", ".join(f"{group:,}".replace(",", " ") for group in groups)
        raise ValueError(
            "Обнаружены библиотеки из разных групп "
            f"({group_list} знаков после запятой). Оставьте в папке программы "
            "файлы только одной группы."
        )

    digits = [file for file in files if file.kind == "digits"]
    if not digits:
        raise ValueError(
            "Файл с цифрами π не найден. Загрузите необходимые библиотеки "
            "с сайта программы."
        )
    if len(digits) > 1:
        raise ValueError("Найдено несколько файлов с цифрами π.")
    letters: dict[str, DataFile] = {}
    for file in files:
        if file.kind != "letters":
            continue
        if file.language is None:
            raise ValueError(f"В файле не указан язык: {file.path.name}")
        if file.language in letters:
            raise ValueError(f"Найдено несколько файлов для языка «{file.language}».")
        _validate_library_presence(file)
        letters[file.language] = file

    _validate_library_presence(digits[0])
    return DataSet(groups[0], digits[0], letters)


def encode_digit_pairs(digits: str, alphabet: str) -> str:
    if len(digits) % 2:
        raise ValueError("Количество цифр должно быть четным.")
    pair_map = tuple(alphabet[value % len(alphabet)] for value in range(100))
    return "".join(
        pair_map[int(digits[index : index + 2])]
        for index in range(0, len(digits), 2)
    )


def find_occurrences(sequence: str, query: str) -> array:
    positions = array("I")
    if not query:
        return positions
    position = sequence.find(query)
    while position != -1:
        positions.append(position)
        position = sequence.find(query, position + 1)
    return positions


def draw_rounded_rectangle(
    canvas: tk.Canvas, tag: str, color: str, radius: int = FIELD_RADIUS
) -> None:
    canvas.delete(tag)
    width = canvas.winfo_width()
    height = canvas.winfo_height()
    if width <= 1 or height <= 1:
        return
    radius = min(radius, width // 2, height // 2)
    points = (
        radius, 0, width - radius, 0, width, 0, width, radius,
        width, height - radius, width, height, width - radius, height,
        radius, height, 0, height, 0, height - radius, 0, radius,
        0, 0,
    )
    canvas.create_polygon(
        points, smooth=True, fill=color, outline="#303030", width=1, tags=tag
    )
    canvas.tag_lower(tag)


class PiSearchApp:
    def __init__(self, root: tk.Tk, data_set: DataSet) -> None:
        self.root = root
        self.root.title("PiSearch")
        self.root.geometry("1000x760")
        self.root.minsize(680, 520)
        self.root.configure(bg=BACKGROUND)
        self._set_window_icon()
        self.root.protocol("WM_DELETE_WINDOW", self.close)

        self.mode = tk.StringVar(value="digits")
        self.alphabet = tk.StringVar(value=next(iter(data_set.letters), ""))
        self.query = tk.StringVar()
        self.status = tk.StringVar(value="Введите последовательность для поиска.")
        self.decimal_places = data_set.decimal_places
        self.languages = tuple(data_set.letters)
        self.data_files = {
            "digits": data_set.digits,
            **{file.key: file for file in data_set.letters.values()},
        }
        self.match_number = tk.StringVar(value="0")
        self.match_total = tk.StringVar(value="из 0 совпадений")
        self.match_limit_note = tk.StringVar(value="Номер от 0 до 0")

        self.sequences: dict[str, str] = {}
        self.active_mode = "digits"
        self.active_sequence = ""
        self.active_positions = array("I")
        self.active_query = ""
        self.current_match = 0
        self.context_character_offsets: list[int] = []
        self._fitting_context_font = False
        self.busy = False
        self.closing = False
        self.search_animation_job: str | None = None
        self.search_animation_frame = 0
        self.results: SimpleQueue[SearchResult] = SimpleQueue()

        self._build_ui()
        self.root.bind("<Return>", lambda _: self.start_search())
        self.root.after(40, self._poll_results)

    def _build_ui(self) -> None:
        style = ttk.Style()
        style.theme_use("clam")
        style.configure(
            "Pi.Vertical.TScrollbar",
            background="#333333",
            troughcolor=PANEL,
            bordercolor=PANEL,
            arrowcolor=ORANGE,
        )
        style.configure(
            "Pi.TCombobox",
            fieldbackground=INPUT_BACKGROUND,
            background=INPUT_BACKGROUND,
            foreground=WHITE,
            arrowcolor=ORANGE,
        )
        style.map(
            "Pi.TCombobox",
            fieldbackground=[
                ("readonly", INPUT_BACKGROUND),
                ("disabled", INPUT_BACKGROUND),
            ],
            foreground=[
                ("readonly", WHITE),
                ("disabled", MUTED),
            ],
        )

        header = tk.Frame(self.root, bg=BACKGROUND)
        header.pack(fill="x", padx=28, pady=(16, 10))
        tk.Label(
            header,
            text="π",
            font=("Arial", 54, "bold"),
            fg=ORANGE,
            bg=BACKGROUND,
        ).pack()
        tk.Label(
            header,
            text=(
                "ПОИСК В ПЕРВЫХ "
                f"{self.decimal_places:,}".replace(",", " ")
                + " ЗНАКАХ ПОСЛЕ ЗАПЯТОЙ"
            ),
            font=("Arial", 11, "bold"),
            fg=WHITE,
            bg=BACKGROUND,
        ).pack(pady=(0, 4))

        controls = tk.Frame(self.root, bg=BACKGROUND)
        controls.pack(fill="x", padx=32, pady=(8, 4))

        modes = tk.Frame(controls, bg=BACKGROUND)
        modes.pack(fill="x", pady=(0, 12))
        self.digits_mode_button = tk.Radiobutton(
            modes,
            text="Цифры",
            value="digits",
            variable=self.mode,
            font=("Arial", 11),
            fg=WHITE,
            bg=BACKGROUND,
            activeforeground=ORANGE,
            activebackground=BACKGROUND,
            selectcolor=INPUT_BACKGROUND,
            highlightthickness=0,
            command=self._on_mode_change,
        )
        self.digits_mode_button.pack(side="left", padx=(0, 18))
        self.letters_mode_button = tk.Radiobutton(
            modes,
            text="Буквы",
            value="letters",
            variable=self.mode,
            font=("Arial", 11),
            fg=WHITE,
            bg=BACKGROUND,
            activeforeground=ORANGE,
            activebackground=BACKGROUND,
            selectcolor=INPUT_BACKGROUND,
            highlightthickness=0,
            command=self._on_mode_change,
            state="normal" if self.languages else "disabled",
            disabledforeground=MUTED,
        )
        self.letters_mode_button.pack(side="left", padx=(0, 18))

        self.alphabet_picker = ttk.Combobox(
            modes,
            textvariable=self.alphabet,
            values=self.languages,
            state="disabled",
            width=12,
            style="Pi.TCombobox",
            postcommand=self._style_alphabet_popup,
        )
        self.alphabet_picker.pack(side="left")
        self.root.option_add("*TCombobox*Listbox.background", INPUT_BACKGROUND)
        self.root.option_add("*TCombobox*Listbox.foreground", WHITE)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ORANGE)
        self.root.option_add("*TCombobox*Listbox.selectForeground", BACKGROUND)
        self.alphabet_picker.bind(
            "<<ComboboxSelected>>", lambda _event: self._on_mode_change()
        )

        search_row = tk.Frame(controls, bg=BACKGROUND)
        search_row.pack(fill="x")
        entry_canvas = tk.Canvas(
            search_row,
            height=48,
            bg=BACKGROUND,
            highlightthickness=0,
            borderwidth=0,
        )
        entry_canvas.pack(side="left", fill="x", expand=True, padx=(0, 10))
        self.search_entry = tk.Entry(
            entry_canvas,
            textvariable=self.query,
            font=("Consolas", 15),
            fg=WHITE,
            bg=INPUT_BACKGROUND,
            insertbackground=ORANGE,
            relief="flat",
            borderwidth=0,
            highlightthickness=0,
            validate="key",
            validatecommand=(self.root.register(self._validate_query), "%P"),
        )
        entry_window = entry_canvas.create_window(
            8, 24, window=self.search_entry, anchor="w", width=200, height=34
        )
        entry_canvas.bind(
            "<Configure>",
            lambda event: self._resize_entry_canvas(event, entry_canvas, entry_window),
        )
        entry_canvas.bind(
            "<Configure>",
            lambda _event: draw_rounded_rectangle(
                entry_canvas, "rounded-entry", INPUT_BACKGROUND
            ),
            add="+",
        )
        self.search_entry.bind("<KeyPress>", self._capitalize_or_reject)
        self.search_entry.bind("<<Paste>>", self._paste_query)
        self.search_entry.bind("<<PasteSelection>>", self._paste_query)
        self.search_button = tk.Canvas(
            search_row,
            width=112,
            height=48,
            bg=BACKGROUND,
            highlightthickness=0,
            borderwidth=0,
            cursor="hand2",
        )
        self.search_button.pack(side="left")
        self.search_button_enabled = True
        self.search_button_hovered = False
        self.search_button.bind("<Configure>", lambda _event: self._draw_search_button())
        self.search_button.bind("<Enter>", self._on_search_button_enter)
        self.search_button.bind("<Leave>", self._on_search_button_leave)
        self.search_button.bind("<Button-1>", lambda _event: self.start_search())
        tk.Label(
            controls,
            text="В режиме букв пары цифр от 00 до 99 кодируются по модулю длины алфавита.",
            anchor="w",
            font=("Arial", 9),
            fg=MUTED,
            bg=BACKGROUND,
        ).pack(fill="x", pady=(6, 0))

        self.status_label = tk.Label(
            self.root,
            textvariable=self.status,
            anchor="w",
            font=("Arial", 10),
            fg=MUTED,
            bg=BACKGROUND,
        )
        self.status_label.pack(fill="x", padx=34, pady=(8, 8))

        navigation = tk.Frame(self.root, bg=BACKGROUND)
        navigation.pack(pady=(12, 4))
        self.previous_button = self._navigation_button(
            navigation, "←", lambda: self._move_match(-1)
        )
        self.previous_button.pack(side="left", padx=12)
        self.match_number_canvas = tk.Canvas(
            navigation,
            width=78,
            height=38,
            bg=BACKGROUND,
            highlightthickness=0,
            borderwidth=0,
        )
        self.match_number_canvas.pack(side="left")
        self.match_number_entry = tk.Entry(
            self.match_number_canvas,
            textvariable=self.match_number,
            width=6,
            font=("Consolas", 11, "bold"),
            fg=WHITE,
            bg=INPUT_BACKGROUND,
            insertbackground=ORANGE,
            justify="center",
            relief="flat",
            validate="key",
            validatecommand=(self.root.register(self._validate_match_number), "%P"),
        )
        self.match_number_window = self.match_number_canvas.create_window(
            6, 4, window=self.match_number_entry, anchor="nw", width=66, height=30
        )
        self.match_number_canvas.bind(
            "<Configure>", self._draw_match_number_background
        )
        self.match_number_entry.bind("<Return>", self._commit_match_number)
        self.match_number_entry.bind("<FocusOut>", self._commit_match_number)
        tk.Label(
            navigation,
            textvariable=self.match_total,
            font=("Consolas", 11, "bold"),
            fg=WHITE,
            bg=BACKGROUND,
        ).pack(side="left", padx=(8, 0))
        self.next_button = self._navigation_button(
            navigation, "→", lambda: self._move_match(1)
        )
        self.next_button.pack(side="left", padx=12)
        tk.Label(
            self.root,
            textvariable=self.match_limit_note,
            font=("Arial", 9),
            fg=MUTED,
            bg=BACKGROUND,
        ).pack(pady=(0, 6))

        context_frame = tk.Frame(self.root, bg=BACKGROUND)
        context_frame.pack(fill="both", expand=True, padx=32, pady=(8, 16))
        tk.Label(
            context_frame,
            text="КОНТЕКСТ: ДО 100 СИМВОЛОВ, ДО И ПОСЛЕ СОВПАДЕНИЯ",
            anchor="w",
            font=("Arial", 9, "bold"),
            fg=MUTED,
            bg=BACKGROUND,
        ).pack(fill="x", pady=(0, 4))
        context_body = tk.Frame(context_frame, bg=BACKGROUND)
        context_body.pack(fill="both", expand=True)
        context_canvas = tk.Canvas(
            context_body,
            bg=BACKGROUND,
            highlightthickness=0,
            borderwidth=0,
        )
        context_canvas.pack(side="left", fill="both", expand=True)
        self.context_font = tkfont.Font(family="Consolas", size=12)
        self.context = tk.Text(
            context_canvas,
            height=6,
            wrap="char",
            font=self.context_font,
            fg=WHITE,
            bg=PANEL,
            insertbackground=ORANGE,
            borderwidth=0,
            padx=10,
            pady=8,
            state="disabled",
        )
        self.context.tag_configure("match", foreground=BACKGROUND, background=ORANGE)
        self.context.tag_configure(
            "match_other",
            foreground=WHITE,
            background=DARK_ORANGE,
        )
        self.context.tag_configure(
            "match_selected",
            foreground=BACKGROUND,
            background=LIGHT_ORANGE,
        )
        self.context.tag_configure("center", justify="center")
        self.context_menu = tk.Menu(
            self.root,
            tearoff=False,
            bg=INPUT_BACKGROUND,
            fg=WHITE,
            activebackground=ORANGE,
            activeforeground=BACKGROUND,
            disabledforeground=MUTED,
        )
        self.context_menu.add_command(
            label="Копировать",
            command=self._copy_context,
        )
        self.context.bind("<Button-3>", self._show_context_menu)
        self.context_scrollbar = ttk.Scrollbar(
            context_body,
            orient="vertical",
            command=self.context.yview,
            style="Pi.Vertical.TScrollbar",
        )
        self.context.configure(yscrollcommand=self.context_scrollbar.set)
        self.context_scrollbar.pack(side="right", fill="y")
        self.context_window = context_canvas.create_window(
            10, 10, window=self.context, anchor="nw", width=300, height=160
        )
        context_canvas.bind(
            "<Configure>",
            lambda event: self._resize_context_canvas(event, context_canvas),
        )
        context_canvas.bind(
            "<Configure>",
            lambda _event: draw_rounded_rectangle(
                context_canvas, "rounded-context", PANEL
            ),
            add="+",
        )
        self.context.bind("<Configure>", self._on_context_resize)
        self.root.after_idle(self._fit_context_font)
        self._update_navigation_state()

    @staticmethod
    def _resize_entry_canvas(
        event: tk.Event, canvas: tk.Canvas, entry_window: int
    ) -> None:
        canvas.itemconfigure(entry_window, width=max(1, event.width - 16))

    def _resize_context_canvas(self, event: tk.Event, canvas: tk.Canvas) -> None:
        canvas.itemconfigure(
            self.context_window,
            width=max(1, event.width - 20),
            height=max(1, event.height - 20),
        )

    def _draw_match_number_background(self, event: tk.Event) -> None:
        self.match_number_canvas.itemconfigure(
            self.match_number_window,
            width=max(1, event.width - 12),
            height=max(1, event.height - 8),
        )
        draw_rounded_rectangle(
            self.match_number_canvas, "rounded-match-number", INPUT_BACKGROUND
        )

    def _on_context_resize(self, _event: tk.Event) -> None:
        if self.active_positions and not self.busy:
            self._show_match()
        else:
            self._fit_context_font()

    def _tag_context_match(
        self, position: int, context_start: int, context_end: int, tag: str
    ) -> None:
        start = max(position, context_start)
        end = min(position + len(self.active_query), context_end)
        if start >= end:
            return
        display_positions = self.context_character_offsets[
            start - context_start : end - context_start
        ]
        segment_start = display_positions[0]
        segment_end = segment_start + 1
        for display_position in display_positions[1:]:
            if display_position == segment_end:
                segment_end += 1
                continue
            self.context.tag_add(
                tag,
                f"1.0+{segment_start}c",
                f"1.0+{segment_end}c",
            )
            segment_start = display_position
            segment_end = display_position + 1
        self.context.tag_add(
            tag,
            f"1.0+{segment_start}c",
            f"1.0+{segment_end}c",
        )

    def _set_window_icon(self) -> None:
        self.icon_image = tk.PhotoImage(width=32, height=32)
        self.icon_image.put(BACKGROUND, to=(0, 0, 32, 32))
        self.icon_image.put(ORANGE, to=(4, 7, 28, 11))
        self.icon_image.put(ORANGE, to=(8, 10, 12, 27))
        self.icon_image.put(ORANGE, to=(20, 10, 24, 27))
        self.root.iconphoto(True, self.icon_image)

    def _style_alphabet_popup(self) -> None:
        popdown = self.root.tk.call(
            "ttk::combobox::PopdownWindow", self.alphabet_picker
        )
        self.root.tk.call(
            f"{popdown}.f.l",
            "configure",
            "-background",
            INPUT_BACKGROUND,
            "-foreground",
            WHITE,
            "-selectbackground",
            ORANGE,
            "-selectforeground",
            BACKGROUND,
            "-highlightbackground",
            "#303030",
            "-highlightcolor",
            ORANGE,
            "-relief",
            "flat",
            "-borderwidth",
            0,
        )

    def _show_context_menu(self, event: tk.Event) -> str:
        try:
            selection_start = self.context.index(tk.SEL_FIRST)
            selection_end = self.context.index(tk.SEL_LAST)
        except tk.TclError:
            return "break"

        clicked_index = self.context.index(f"@{event.x},{event.y}")
        if not (
            self.context.compare(selection_start, "<=", clicked_index)
            and self.context.compare(clicked_index, "<", selection_end)
        ):
            return "break"

        self.context_menu.post(event.x_root, event.y_root)
        return "break"

    def _copy_context(self) -> None:
        try:
            selected_text = self.context.get(tk.SEL_FIRST, tk.SEL_LAST)
        except tk.TclError:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(selected_text)
        self.root.update_idletasks()

    def _draw_search_button(self) -> None:
        if not self.search_button.winfo_exists():
            return
        color = (
            "#444444"
            if not self.search_button_enabled
            else "#ffa733"
            if self.search_button_hovered
            else ORANGE
        )
        text_color = MUTED if not self.search_button_enabled else BACKGROUND
        draw_rounded_rectangle(self.search_button, "search-button", color)
        self.search_button.delete("search-button-text")
        self.search_button.create_text(
            self.search_button.winfo_width() // 2,
            self.search_button.winfo_height() // 2,
            text="НАЙТИ",
            fill=text_color,
            font=("Arial", 10, "bold"),
            tags="search-button-text",
        )

    def _on_search_button_enter(self, _event: tk.Event) -> None:
        self.search_button_hovered = True
        self._draw_search_button()

    def _on_search_button_leave(self, _event: tk.Event) -> None:
        self.search_button_hovered = False
        self._draw_search_button()

    def _set_search_button_enabled(self, enabled: bool) -> None:
        self.search_button_enabled = enabled
        self.search_button.configure(cursor="hand2" if enabled else "arrow")
        self._draw_search_button()

    def _show_search_animation(self) -> None:
        self.search_animation_job = None
        if not self.busy or self.closing:
            return

        self.context.configure(state="normal")
        self.context.delete("1.0", "end")
        self.context.insert(
            "1.0", "Ищем совпадение\n" + "." * (self.search_animation_frame + 1)
        )
        self.context.tag_add("center", "1.0", "end-1c")
        self.context.configure(state="disabled")
        self._fit_context_font(SEARCHING_TEXT)

        self.search_animation_frame = (self.search_animation_frame + 1) % 3
        self.search_animation_job = self.root.after(
            SEARCH_ANIMATION_INTERVAL_MS, self._show_search_animation
        )

    def _stop_search_animation(self) -> None:
        if self.search_animation_job is not None:
            self.root.after_cancel(self.search_animation_job)
            self.search_animation_job = None

    def _fit_context_font(self, text: str | None = None) -> None:
        if self._fitting_context_font:
            return
        self._fitting_context_font = True
        try:
            self.context.update_idletasks()
            width = self.context.winfo_width() - 24
            height = self.context.winfo_height() - 20
            if width <= 0 or height <= 0:
                return
            if text is None and self.busy:
                text = SEARCHING_TEXT
            if text is None:
                content_lines = self.context.get("1.0", "end-1c").splitlines() or [""]
            else:
                content_lines = text.splitlines() or [""]
            lower_size = MIN_RESULT_FONT_SIZE
            upper_size = min(MAX_RESULT_FONT_SIZE, height)
            best_size = MIN_RESULT_FONT_SIZE
            while lower_size <= upper_size:
                size = (lower_size + upper_size) // 2
                self.context_font.configure(size=size)
                character_width = max(1, self.context_font.measure("M"))
                line_height = self.context_font.metrics("linespace")
                characters_per_line = max(1, width // character_width)
                lines = sum(
                    max(
                        1,
                        (len(line) + characters_per_line - 1) // characters_per_line,
                    )
                    for line in content_lines
                )
                if lines * line_height <= height:
                    best_size = size
                    lower_size = size + 1
                else:
                    upper_size = size - 1
            self.context_font.configure(size=best_size)
        finally:
            self._fitting_context_font = False

    def _is_query_character(self, character: str) -> bool:
        if self.mode.get() == "digits":
            return character in "0123456789"
        data_file = self.data_files.get(f"letters:{self.alphabet.get()}")
        return data_file is not None and character in (data_file.alphabet or "")

    def _validate_query(self, proposed: str) -> bool:
        return all(self._is_query_character(character) for character in proposed)

    def _capitalize_or_reject(self, event: tk.Event) -> str | None:
        if event.char and event.char.isalpha():
            uppercase = event.char.upper()
            if uppercase != event.char:
                if all(self._is_query_character(character) for character in uppercase):
                    try:
                        self.search_entry.delete(tk.SEL_FIRST, tk.SEL_LAST)
                    except tk.TclError:
                        pass
                    self.search_entry.insert(tk.INSERT, uppercase)
                return "break"
        return None

    def _paste_query(self, _event: tk.Event) -> str:
        try:
            pasted = self.root.clipboard_get().upper()
        except tk.TclError:
            return "break"
        current = self.query.get()
        try:
            selection_start = self.search_entry.index(tk.SEL_FIRST)
            selection_end = self.search_entry.index(tk.SEL_LAST)
            proposed = current[:selection_start] + pasted + current[selection_end:]
        except tk.TclError:
            insertion = self.search_entry.index(tk.INSERT)
            proposed = current[:insertion] + pasted + current[insertion:]
        if not self._validate_query(proposed):
            return "break"
        try:
            self.search_entry.delete(tk.SEL_FIRST, tk.SEL_LAST)
        except tk.TclError:
            pass
        self.search_entry.insert(tk.INSERT, pasted)
        return "break"

    def _on_mode_change(self) -> None:
        self._update_alphabet_state()
        self.query.set(
            "".join(
                character
                for character in self.query.get().upper()
                if self._is_query_character(character)
            )
        )

    @staticmethod
    def _navigation_button(
        parent: tk.Misc, text: str, command: Callable[[], None]
    ) -> tk.Button:
        return tk.Button(
            parent,
            text=text,
            command=command,
            font=("Arial", 17, "bold"),
            fg=ORANGE,
            bg=BACKGROUND,
            activeforeground=WHITE,
            activebackground=BACKGROUND,
            disabledforeground="#555555",
            relief="flat",
            width=3,
            cursor="hand2",
        )

    def _update_alphabet_state(self) -> None:
        self.alphabet_picker.configure(
            state=(
                "readonly"
                if self.mode.get() == "letters" and self.alphabet_picker["values"]
                else "disabled"
            )
        )

    def _selected_mode(self) -> str:
        if self.mode.get() == "digits":
            return "digits"
        return f"letters:{self.alphabet.get()}"

    @staticmethod
    def _validate_match_number(proposed: str) -> bool:
        return not proposed or proposed.isdigit()

    def _commit_match_number(self, _event: tk.Event | None = None) -> str:
        if not self.active_positions:
            self.match_number.set("0")
            return "break"
        try:
            requested = int(self.match_number.get())
        except ValueError:
            requested = 0
        if 1 <= requested <= len(self.active_positions):
            self.current_match = requested - 1
            self._show_match()
        else:
            self.match_number.set(str(self.current_match + 1))
        return "break"

    def start_search(self) -> None:
        if self.busy:
            return

        mode = self._selected_mode()
        query = self.query.get().strip().upper()
        if mode not in self.data_files:
            self._show_error("Для выбранного режима нет файла данных.")
            return
        if not query:
            self._show_error("Введите цифры или буквы для поиска.")
            return
        if not self._validate_query(query):
            expectation = "цифры от 0 до 9" if mode == "digits" else "буквы выбранного алфавита"
            self._show_error(f"Для этого режима допустимы только {expectation}.")
            return
        if len(query) > self.decimal_places:
            self._show_error("Поисковая последовательность длиннее доступного диапазона.")
            return
        if mode != "digits" and len(query) > self.decimal_places // 2:
            self._show_error("Поисковая последовательность длиннее доступного алфавитного ряда.")
            return

        self.busy = True
        self._clear_results()
        self.search_animation_frame = 0
        self.search_animation_job = self.root.after(
            SEARCH_ANIMATION_INTERVAL_MS, self._show_search_animation
        )
        self._set_search_button_enabled(False)
        self.status.set("Идет поиск...")
        self.status_label.configure(fg=MUTED)
        self._update_navigation_state()
        self.root.update_idletasks()
        cached_sequence = self.sequences.get(mode)
        threading.Thread(
            target=self._search_in_background,
            args=(mode, query, cached_sequence),
            daemon=True,
        ).start()

    def _search_in_background(
        self, mode: str, query: str, cached_sequence: str | None
    ) -> None:
        try:
            sequence = (
                cached_sequence
                if cached_sequence is not None
                else load_sequence(self.data_files[mode])
            )
            positions = find_occurrences(sequence, query)
            result = SearchResult(mode, query, sequence, positions)
        except (OSError, UnicodeError, ValueError) as error:
            result = SearchResult(mode, query, "", array("I"), str(error))
        self.results.put(result)

    def _poll_results(self) -> None:
        if self.closing:
            return
        try:
            result = self.results.get_nowait()
        except Empty:
            pass
        else:
            self._finish_search(result)
        self.root.after(40, self._poll_results)

    def _finish_search(self, result: SearchResult) -> None:
        self.busy = False
        self._stop_search_animation()
        self._set_search_button_enabled(True)
        if result.error is not None:
            self._show_error(f"Ошибка чтения данных: {result.error}")
            return
        self.sequences[result.mode] = result.sequence
        if not result.positions:
            self._show_error(
                f"Последовательность не найдена в первых {self.decimal_places:,} знаках после запятой."
                .replace(",", " ")
            )
            return

        self.active_mode = result.mode
        self.active_sequence = result.sequence
        self.active_positions = result.positions
        self.active_query = result.query
        self.current_match = 0
        self._show_match()

    def _show_match(self) -> None:
        position = self.active_positions[self.current_match]
        end_position = position + len(self.active_query)
        context_start = max(0, position - 100)
        context_end = min(len(self.active_sequence), end_position + 100)
        context = self.active_sequence[context_start:context_end]
        display_characters = [(character, index) for index, character in enumerate(context)]
        if self.active_mode == "digits" and context_start == 0 and context_end > 1:
            display_characters.insert(1, (",", None))
        unwrapped_context = "".join(character for character, _ in display_characters)
        self._fit_context_font(unwrapped_context)
        content_width = (
            self.context.winfo_width() - 2 * int(self.context.cget("padx")) - 4
        )
        characters_per_line = max(
            1, content_width // max(1, self.context_font.measure("M"))
        )
        line_count = max(
            1, (len(display_characters) + characters_per_line - 1) // characters_per_line
        )
        line_length, extra_characters = divmod(len(display_characters), line_count)
        display_lines = []
        self.context_character_offsets = [0] * len(context)
        display_offset = 0
        character_index = 0
        for line_index in range(line_count):
            current_line_length = line_length + (line_index < extra_characters)
            line_characters = display_characters[
                character_index : character_index + current_line_length
            ]
            display_lines.append("".join(character for character, _ in line_characters))
            for character, source_index in line_characters:
                if source_index is not None:
                    self.context_character_offsets[source_index] = display_offset
                display_offset += 1
            character_index += current_line_length
            if line_index < line_count - 1:
                display_offset += 1
        display_context = "\n".join(display_lines)
        self.context.configure(state="normal")
        for tag in ("match", "match_other", "match_selected"):
            self.context.tag_remove(tag, "1.0", "end")
        self.context.delete("1.0", "end")
        self.context.insert("1.0", display_context)
        self.context.tag_add("center", "1.0", "end-1c")
        first_match = bisect_left(self.active_positions, context_start)
        for match_index in range(first_match, len(self.active_positions)):
            match_position = self.active_positions[match_index]
            if match_position >= context_end:
                break
            match_tag = (
                "match_selected"
                if match_index == self.current_match
                else "match_other"
            )
            self._tag_context_match(
                match_position, context_start, context_end, match_tag
            )
        self.context.tag_raise("match_selected")
        self.context.configure(state="disabled")
        self._fit_context_font(display_context)

        total_matches = len(self.active_positions)
        self.match_number.set(str(self.current_match + 1))
        self.match_total.set(f"из {total_matches} совпадений")
        self.match_limit_note.set(f"Введите номер от 1 до {total_matches}")
        if self.active_mode == "digits":
            position_text = (
                "целой части π"
                if position == 0
                else f"{position:,} после запятой"
            )
        else:
            position_text = (
                f"{position + 1:,} в буквенном ряду "
                f"(пара начинается с {position * 2 + 1:,}-й цифры после запятой)"
            )
        self.status.set(f"Совпадение на позиции {position_text}.".replace(",", " "))
        self.status_label.configure(fg=ORANGE)
        self._update_navigation_state()

    def _show_error(self, message: str) -> None:
        self.status.set(message)
        self.status_label.configure(fg=ORANGE)
        self._clear_results()

    def _clear_results(self) -> None:
        self.match_number.set("0")
        self.match_total.set("из 0 совпадений")
        self.match_limit_note.set("Номер от 0 до 0")
        self.active_mode = self.mode.get()
        self.active_positions = array("I")
        self.active_sequence = ""
        self.active_query = ""
        self.current_match = 0
        self.context.configure(state="normal")
        self.context.delete("1.0", "end")
        self.context.configure(state="disabled")
        for tag in ("match", "match_other", "match_selected", "center"):
            self.context.tag_remove(tag, "1.0", "end")
        self._update_navigation_state()

    def _move_match(self, offset: int) -> None:
        if not self.active_positions:
            return
        self.current_match = (self.current_match + offset) % len(self.active_positions)
        self._show_match()

    def _update_navigation_state(self) -> None:
        state = "normal" if self.active_positions and not self.busy else "disabled"
        self.previous_button.configure(state=state)
        self.next_button.configure(state=state)

    def close(self) -> None:
        self.closing = True
        self._stop_search_animation()
        self.root.destroy()


def main() -> None:
    if sys.platform == "win32":
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
            "OpenAI.PiSearch"
        )
    try:
        data_set = discover_data_files(application_directory())
    except (OSError, UnicodeError, ValueError) as error:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror("PiSearch", str(error), parent=root)
        root.destroy()
        return
    root = tk.Tk()
    PiSearchApp(root, data_set)
    root.mainloop()


if __name__ == "__main__":
    main()
