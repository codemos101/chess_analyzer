#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Chess Analyzer - offline desktop chess analysis workstation (single file).

Install:  pip install python-chess matplotlib requests
Run:      python chess_analyzer.py

MOVE CLASSIFICATION PRIORITY (explicit, every move gets exactly one grade):
  1. Book        - move continues a recognised opening line (or the Portable Game Notation
                   comment says "book") and loses less than the "Good" threshold.
  2. Brilliant   - sound material sacrifice (static exchange search), engine-confirmed
                   (move is inside the engine's multi-line results, loss <= "Excellent",
                   position still >= 45% expected points, not already crushing, not a recapture).
  3. Great Move  - engine-best move whose best alternative is at least `great_gap`
                   Expected Points worse (an only-move style decision), position not lost.
  4. Miss        - a Mistake-level loss thrown away from a clearly better position
                   (>= 70% expected points before, still >= 40% after) when an opportunity
                   existed (opponent's previous move was an error, or the best move was unique).
  5. Best / Excellent / Good / Inaccuracy / Mistake / Blunder - Expected Points loss ladder.

EXPECTED POINTS (EP) = 1 / (1 + 10^(-cp/400)),  loss_i = max(0, EP_best - EP_played)
ACCURACY = 100 * exp(-k * average_loss).  Calibration of k = 10: an average loss of
0.005 (master-level) gives about 95%, 0.015 about 86%, 0.04 about 67%, 0.08 about 45%.
"""
from __future__ import annotations

import copy
import hashlib
import io
import json
import math
import os
import platform
import queue
import random
import re
import shutil
import stat
import statistics
import sys
import tarfile
import threading
import time
import traceback
import urllib.request
import zipfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional

# =============================================================================
# 1. IMPORTS AND DEPENDENCY CHECKS
# =============================================================================
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox, colorchooser
except ImportError:
    sys.stderr.write("Tkinter is required but was not found. Install the Python Tk package for your system.\n")
    sys.exit(1)

INSTALL_COMMAND = "pip install python-chess pillow matplotlib requests"
try:
    import chess
    import chess.engine
    import chess.pgn
except ImportError:
    _msg = ("The required library 'python-chess' is not installed.\n\nInstall it with:\n    "
            + INSTALL_COMMAND + "\n\nThen start the application again.")
    sys.stderr.write(_msg + "\n")
    try:
        _root = tk.Tk()
        _root.withdraw()
        messagebox.showerror("Missing dependency", _msg)
        _root.destroy()
    except tk.TclError as _exc:
        sys.stderr.write(f"(Could not show a dialog: {_exc})\n")
    sys.exit(1)

try:
    import requests  # optional: nicer downloads
except ImportError:
    requests = None

HAS_MPL = False
try:  # optional: evaluation graph through Matplotlib
    import matplotlib
    matplotlib.use("TkAgg")
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    HAS_MPL = True
except Exception as _mpl_exc:  # optional dependency boundary: any failure means "use the canvas graph"
    sys.stderr.write(f"Matplotlib unavailable ({_mpl_exc}); using the built-in canvas graph.\n")

# =============================================================================
# 2. APPLICATION CONFIGURATION
# =============================================================================
APP_NAME = "Chess Analyzer"
APP_DIR = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd()
CONFIG_PATH = APP_DIR / "chess_analyzer_settings.json"
ENGINE_DIR = APP_DIR / "engines"
RELEASE_API = "https://api.github.com/repos/official-stockfish/Stockfish/releases/latest"
SETTINGS_SCHEMA = 1
IS_WINDOWS = platform.system() == "Windows"
IS_MAC = platform.system() == "Darwin"
UI_FONT = "Segoe UI" if IS_WINDOWS else ("Helvetica Neue" if IS_MAC else "DejaVu Sans")
PIECE_FONT = "Segoe UI Symbol" if IS_WINDOWS else ("Apple Symbols" if IS_MAC else "DejaVu Sans")

BG, PANEL, PANEL2, FG, MUTED, ACCENT = "#1b1b1b", "#262522", "#302e2c", "#e6e6e6", "#9a9a9a", "#81b64c"

GRADES = ["Book", "Brilliant", "Great Move", "Best", "Excellent", "Good", "Inaccuracy", "Mistake", "Blunder", "Miss"]
GRADE_COLORS = {"Book": "#a88865", "Brilliant": "#1baca6", "Great Move": "#5c8bb0", "Best": "#81b64c",
                "Excellent": "#96bc4b", "Good": "#97af8b", "Inaccuracy": "#f7c631", "Mistake": "#e6912c",
                "Blunder": "#ca3431", "Miss": "#d17ba0"}
GRADE_TEXT = {
    "Book": "A move from recognised opening theory.",
    "Brilliant": "A sound sacrifice confirmed by the engine.",
    "Great Move": "A critical decision: the alternatives were clearly worse.",
    "Best": "The engine's top choice (or equal in value).",
    "Excellent": "Almost as good as the best move.",
    "Good": "A solid move with a small loss.",
    "Inaccuracy": "A slightly inferior move.",
    "Mistake": "A clear error that gave away a lot of value.",
    "Blunder": "A serious error.",
    "Miss": "A winning opportunity was not taken.",
}
DEFAULT_THRESHOLDS = {"best": 0.005, "excellent": 0.015, "good": 0.035, "inaccuracy": 0.08, "mistake": 0.18}
DEFAULT_SETTINGS = {
    "schema": SETTINGS_SCHEMA, "engine_path": "", "auto_detect": True, "offer_download": True,
    "depth": 14, "time_limit": 2.0, "multipv": 3,
    "light_color": "#eeeed2", "dark_color": "#769656", "flip_board": False, "sound": True,
    "ai_elo": 1400, "accuracy_k": 10.0, "thresholds": dict(DEFAULT_THRESHOLDS),
    "great_gap": 0.12, "miss_min_loss": 0.08,
}
SETTING_RANGES = {"depth": (1, 40), "time_limit": (0.0, 120.0), "multipv": (1, 5), "ai_elo": (800, 2500),
                  "accuracy_k": (0.1, 100.0), "great_gap": (0.01, 0.9), "miss_min_loss": (0.01, 0.9)}

MATE_CP = 3000          # bounded value used for forced mates (distinct from ordinary cp)
MATE_THRESHOLD = 2500   # anything at or above this magnitude is a forced mate
ORDINARY_CP_CAP = 2000  # ordinary centipawn scores are clamped here
PIECE_VALUES = {chess.PAWN: 1, chess.KNIGHT: 3, chess.BISHOP: 3, chess.ROOK: 5, chess.QUEEN: 9, chess.KING: 0}
GLYPHS = {chess.PAWN: "\u265f", chess.KNIGHT: "\u265e", chess.BISHOP: "\u265d",
          chess.ROOK: "\u265c", chess.QUEEN: "\u265b", chess.KING: "\u265a"}
START_COUNTS = {chess.QUEEN: 1, chess.ROOK: 2, chess.BISHOP: 2, chess.KNIGHT: 2, chess.PAWN: 8}


class AnalysisError(Exception):
    """Raised when a game cannot be analysed."""


class AnalysisCancelled(Exception):
    """Raised when the user cancels an analysis."""


class EngineUnavailable(Exception):
    """Raised when the chess engine cannot be used."""


class InstallError(Exception):
    """Raised when engine download or installation fails."""


class InstallCancelled(InstallError):
    """Raised when the user cancels the installation."""


class Settings:
    """Persistent settings stored in a local JSON file with validation and safe defaults."""

    def __init__(self) -> None:
        self.data = copy.deepcopy(DEFAULT_SETTINGS)

    @staticmethod
    def _valid(key: str, value, default):
        if key == "thresholds":
            if not isinstance(value, dict):
                raise ValueError("thresholds must be an object")
            keys = ["best", "excellent", "good", "inaccuracy", "mistake"]
            vals = [value.get(k) for k in keys]
            if any(isinstance(v, bool) or not isinstance(v, (int, float)) for v in vals):
                raise ValueError("thresholds must be numbers")
            if not all(0 < a < b for a, b in zip(vals, vals[1:])) or vals[0] <= 0 or vals[-1] >= 1:
                raise ValueError("thresholds must be positive and increasing")
            return {k: float(v) for k, v in zip(keys, vals)}
        if isinstance(default, bool):
            if not isinstance(value, bool):
                raise ValueError(f"{key} must be true/false")
            return value
        if isinstance(default, int):
            if isinstance(value, bool) or not isinstance(value, int):
                raise ValueError(f"{key} must be an integer")
        elif isinstance(default, float):
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                raise ValueError(f"{key} must be a number")
            value = float(value)
        elif isinstance(default, str):
            if not isinstance(value, str):
                raise ValueError(f"{key} must be text")
            if key.endswith("_color") and not re.fullmatch(r"#[0-9a-fA-F]{6}", value):
                raise ValueError(f"{key} must look like #rrggbb")
        if key in SETTING_RANGES:
            lo, hi = SETTING_RANGES[key]
            if not lo <= value <= hi:
                raise ValueError(f"{key} must be between {lo} and {hi}")
        return value

    def load(self) -> Optional[str]:
        """Load settings; returns a warning text if the file had to be reset."""
        if not CONFIG_PATH.exists():
            return None
        try:
            raw = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
            if not isinstance(raw, dict) or raw.get("schema") != SETTINGS_SCHEMA:
                raise ValueError("incompatible settings version")
            merged = copy.deepcopy(DEFAULT_SETTINGS)
            for key, default in DEFAULT_SETTINGS.items():
                if key in raw:
                    merged[key] = self._valid(key, raw[key], default)
            self.data = merged
            return None
        except (OSError, ValueError, TypeError) as exc:
            self.data = copy.deepcopy(DEFAULT_SETTINGS)
            return f"The settings file could not be used ({exc}). Safe defaults were restored."

    def save(self) -> Optional[str]:
        try:
            CONFIG_PATH.write_text(json.dumps(self.data, indent=2), encoding="utf-8")
            return None
        except OSError as exc:
            return f"Settings could not be saved: {exc}"


# =============================================================================
# 3. EVALUATION MATHEMATICS (shared helpers)
# =============================================================================
def expected_points(cp: float) -> float:
    """EP = 1 / (1 + 10^(-cp/400)), evaluated in a numerically stable way."""
    cp = max(-MATE_CP, min(MATE_CP, float(cp)))
    if cp >= 0:
        return 1.0 / (1.0 + 10.0 ** (-cp / 400.0))
    t = 10.0 ** (cp / 400.0)
    return t / (1.0 + t)


def score_to_cp(score) -> int:
    """Convert a Score seen from the mover's side into a bounded integer.
    Forced mates map to +/-(3000 - 10*distance) so they stay separable from ordinary cp."""
    if score.is_mate():
        mate = score.mate()
        if mate is None or mate <= 0:
            return -MATE_CP
        return MATE_CP - 10 * min(mate, 50)
    value = score.score()
    return max(-ORDINARY_CP_CAP, min(ORDINARY_CP_CAP, int(value)))


def clamp_cp(cp: int, limit: int = 1000) -> int:
    return max(-limit, min(limit, cp))


def fmt_cp(cp: int) -> str:
    if abs(cp) >= MATE_THRESHOLD:
        return "Mate for the mover" if cp > 0 else "Mated"
    return f"{cp / 100:+.2f}"


def fmt_cp_white(cp: int) -> str:
    if abs(cp) >= MATE_THRESHOLD:
        return "+Mate" if cp > 0 else "-Mate"
    return f"{cp / 100:+.2f}"


def material(board: chess.Board, color: bool) -> int:
    return sum(PIECE_VALUES[p.piece_type] for p in board.piece_map().values() if p.color == color)


def qsearch(board: chess.Board, alpha: int, beta: int, depth: int = 6) -> int:
    """Capture-only material search from the side to move's perspective (static exchange)."""
    stand = material(board, board.turn) - material(board, not board.turn)
    if depth == 0:
        return stand
    if stand >= beta:
        return beta
    alpha = max(alpha, stand)
    captures = [m for m in board.legal_moves if board.is_capture(m)]
    captures.sort(key=lambda m: -PIECE_VALUES.get(board.piece_type_at(m.to_square) or chess.PAWN, 1))
    for move in captures:
        board.push(move)
        score = -qsearch(board, -beta, -alpha, depth - 1)
        board.pop()
        if score >= beta:
            return beta
        alpha = max(alpha, score)
    return alpha


def game_phase(board: chess.Board, move_index: int) -> str:
    if move_index < 20:
        return "Opening"
    non_pawn = sum(PIECE_VALUES[p.piece_type] for p in board.piece_map().values()
                   if p.piece_type not in (chess.PAWN, chess.KING))
    return "Endgame" if non_pawn <= 24 else "Middlegame"


def accuracy_from_losses(losses: list[float], k: float) -> Optional[float]:
    """Accuracy = 100 * exp(-k * Average_Loss), where Average_Loss = Total_Loss / moves."""
    if not losses:
        return None
    total_loss = sum(losses)
    average_loss = total_loss / len(losses)
    return max(0.0, min(100.0, 100.0 * math.exp(-k * average_loss)))


def estimate_performance(losses: list[float], cp_losses: list[int], counts: dict, phase_acc: dict,
                         accuracy: float, depth_reached: float, k: float) -> dict:
    """Heuristic performance rating (NOT an official rating). Documented assumptions:
    - baseline from average centipawn loss (exponential decay) blended with accuracy;
    - penalties per rate of blunders/mistakes/inaccuracies; reward for best+excellent share;
    - small capped bonus for brilliant moves; consistency adjustment from the weakest phase;
    - shrink toward 1200 for short games; bounds 400..3000."""
    n = len(losses)
    acpl = statistics.fmean(min(c, 500) for c in cp_losses)
    elo_from_acpl = 400 + 2600 * math.exp(-acpl / 55.0)
    elo_from_acc = 300 + 2500 * (max(0.0, accuracy - 20.0) / 80.0) ** 2.2
    base = 0.6 * elo_from_acpl + 0.4 * elo_from_acc
    bad = counts["Blunder"]
    mid = counts["Mistake"] + counts["Miss"]
    small = counts["Inaccuracy"]
    penalty = min(400.0, 900.0 * bad / n + 350.0 * mid / n + 150.0 * small / n)
    strong_share = (counts["Best"] + counts["Excellent"] + counts["Brilliant"] + counts["Great Move"]) / n
    reward = max(-100.0, min(120.0, 300.0 * (strong_share - 0.40)))
    brilliant_bonus = min(60.0, 20.0 * counts["Brilliant"])
    known = [v for v in phase_acc.values() if v is not None]
    phase_adj = max(-60.0, 0.5 * (min(known) - accuracy)) if known else 0.0
    elo = base - penalty + reward + brilliant_bonus + phase_adj
    shrink = 0.5 * max(0.0, 1.0 - n / 30.0)
    elo = elo + (1200.0 - elo) * shrink
    elo = int(round(max(400.0, min(3000.0, elo)) / 10.0) * 10)
    conf = 0.6 * min(1.0, n / 40.0) + 0.4 * min(1.0, depth_reached / 18.0)
    label = "Low" if conf < 0.4 else ("Medium" if conf < 0.7 else "High")
    margin = int(round(80 + 420 * (1 - conf), -1))
    if elo < 800:
        category = "Beginner"
    elif elo < 1200:
        category = "Novice"
    elif elo < 1600:
        category = "Intermediate"
    elif elo < 2000:
        category = "Advanced"
    elif elo < 2400:
        category = "Expert"
    else:
        category = "Master-level performance"
    return {"elo": elo, "category": category, "confidence": conf, "confidence_label": label, "margin": margin}


# =============================================================================
# 4. OPENING BOOK (lightweight built-in recognition)
# =============================================================================
OPENING_LINES = [
    ("King's Pawn Opening", "e4"), ("Queen's Pawn Opening", "d4"), ("English Opening", "c4"),
    ("Reti Opening", "Nf3"), ("King's Pawn Game", "e4 e5"), ("Sicilian Defence", "e4 c5"),
    ("French Defence", "e4 e6"), ("Caro-Kann Defence", "e4 c6"), ("Scandinavian Defence", "e4 d5"),
    ("Indian Defence", "d4 Nf6"), ("Queen's Pawn Game", "d4 d5"),
    ("Italian Game", "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d3 d6 O-O O-O"),
    ("Evans Gambit", "e4 e5 Nf3 Nc6 Bc4 Bc5 b4 Bxb4 c3 Ba5 d4 exd4 O-O d6"),
    ("Two Knights Defence", "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Na5 Bb5+ c6 dxc6 bxc6 Be2 h6"),
    ("Ruy Lopez", "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O h3"),
    ("Ruy Lopez, Berlin Defence", "e4 e5 Nf3 Nc6 Bb5 Nf6 O-O Nxe4 d4 Nd6 Bxc6 dxc6 dxe5 Nf5 Qxd8+ Kxd8"),
    ("Scotch Game", "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 Nf6 Nxc6 bxc6 e5 Qe7 Qe2 Nd5 c4 Ba6"),
    ("Four Knights Game", "e4 e5 Nf3 Nc6 Nc3 Nf6 Bb5 Bb4 O-O O-O d3 d6 Bg5 Bxc3 bxc3 Qe7"),
    ("Petrov Defence", "e4 e5 Nf3 Nf6 Nxe5 d6 Nf3 Nxe4 d4 d5 Bd3 Nc6 O-O Be7 c4 Nb4"),
    ("Philidor Defence", "e4 e5 Nf3 d6 d4 Nf6 Nc3 Nbd7 Bc4 Be7 O-O O-O"),
    ("Vienna Game", "e4 e5 Nc3 Nf6 f4 d5 fxe5 Nxe4 Nf3 Be7 d4 O-O Bd3 f5"),
    ("King's Gambit", "e4 e5 f4 exf4 Nf3 g5 h4 g4 Ne5 Nf6"),
    ("Sicilian Defence, Najdorf", "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Be3 e5 Nb3 Be6 f3 Be7"),
    ("Sicilian Defence, Dragon", "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 g6 Be3 Bg7 f3 O-O Qd2 Nc6"),
    ("Sicilian Defence, Classical", "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nf6 Nc3 d6 Bg5 e6 Qd2 a6 O-O-O"),
    ("Sicilian Defence, Alapin", "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 Nf3 Nc6 cxd4 d6 Bc4 Nb6 Bb5 dxe5 Nxe5 Bd7"),
    ("Sicilian Defence, Closed", "e4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Be3 e6"),
    ("French Defence, Winawer", "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 Qg4 Qc7"),
    ("French Defence, Classical", "e4 e6 d4 d5 Nc3 Nf6 Bg5 Be7 e5 Nfd7 Bxe7 Qxe7 f4 O-O Nf3 c5"),
    ("Caro-Kann Defence, Classical", "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 h5 Bh7 Bd3 Bxd3 Qxd3 e6"),
    ("Scandinavian Defence, Main Line", "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 c6 Nf3 Nf6 Bc4 Bf5"),
    ("Pirc Defence", "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 O-O Bd3 Na6"),
    ("Alekhine Defence", "e4 Nf6 e5 Nd5 d4 d6 Nf3 Bg4 Be2 e6 O-O Be7"),
    ("Queen's Gambit Declined", "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 h6 Bh4 b6"),
    ("Queen's Gambit Accepted", "d4 d5 c4 dxc4 Nf3 Nf6 e3 e6 Bxc4 c5 O-O a6"),
    ("Slav Defence", "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 a4 Bf5 e3 e6 Bxc4 Bb4 O-O O-O"),
    ("London System", "d4 d5 Bf4 Nf6 e3 c5 c3 Nc6 Nd2 e6 Ngf3 Bd6"),
    ("Nimzo-Indian Defence", "d4 Nf6 c4 e6 Nc3 Bb4 e3 O-O Bd3 d5 Nf3 c5 O-O Nc6"),
    ("Queen's Indian Defence", "d4 Nf6 c4 e6 Nf3 b6 g3 Bb7 Bg2 Be7 O-O O-O Nc3 Ne4"),
    ("King's Indian Defence", "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7"),
    ("Gruenfeld Defence", "d4 Nf6 c4 g6 Nc3 d5 cxd5 Nxd5 e4 Nxc3 bxc3 Bg7 Nf3 c5 Rb1 O-O"),
    ("Benoni Defence", "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 e4 g6 Nf3 Bg7"),
    ("Catalan Opening", "d4 Nf6 c4 e6 g3 d5 Bg2 Be7 Nf3 O-O O-O dxc4"),
    ("Dutch Defence", "d4 f5 g3 Nf6 Bg2 e6 Nf3 Be7 O-O O-O c4 d6"),
    ("English Opening, Symmetrical", "c4 e5 Nc3 Nf6 Nf3 Nc6 g3 d5 cxd5 Nxd5 Bg2 Nb6 O-O Be7"),
    ("Reti Opening, King's Indian Attack", "Nf3 d5 g3 Nf6 Bg2 e6 O-O Be7 d3 O-O Nbd2 c5"),
    ("Bird Opening", "f4 d5 Nf3 Nf6 e3 g6"),
]


class OpeningBook:
    """Maps move sequences (as Universal Chess Interface strings) to opening names."""

    def __init__(self) -> None:
        self.names: dict[tuple[str, ...], str] = {}
        for name, line in OPENING_LINES:
            board = chess.Board()
            sequence: list[str] = []
            try:
                for san in line.split():
                    move = board.parse_san(san)
                    sequence.append(move.uci())
                    board.push(move)
                    self.names.setdefault(tuple(sequence), name)
            except ValueError as exc:
                sys.stderr.write(f"Opening line '{name}' skipped: {exc}\n")

    def contains(self, ucis: list[str]) -> bool:
        return tuple(ucis) in self.names

    def name_for(self, ucis: list[str]) -> str:
        for j in range(min(len(ucis), 40), 0, -1):
            name = self.names.get(tuple(ucis[:j]))
            if name:
                return name
        return ""


# =============================================================================
# 5. STOCKFISH MANAGER (detection, download, process management)
# =============================================================================
def find_stockfish_candidates() -> list[Path]:
    name = "stockfish.exe" if IS_WINDOWS else "stockfish"
    found: list[Path] = []

    def add(p) -> None:
        p = Path(p)
        if p.is_file() and p not in found:
            found.append(p)

    for base in (APP_DIR, ENGINE_DIR):
        add(base / name)
    if ENGINE_DIR.is_dir():
        for p in sorted(ENGINE_DIR.rglob("stockfish*")):
            if p.is_file() and p.suffix.lower() in ("", ".exe") and p.stat().st_size > 500_000:
                add(p)
    which = shutil.which("stockfish")
    if which:
        add(which)
    home = Path.home()
    if IS_WINDOWS:
        common = [r"C:\Program Files\Stockfish\stockfish.exe", r"C:\Stockfish\stockfish.exe",
                  r"C:\stockfish\stockfish.exe", home / "stockfish" / "stockfish.exe"]
    elif IS_MAC:
        common = ["/opt/homebrew/bin/stockfish", "/usr/local/bin/stockfish",
                  "/Applications/Stockfish.app/Contents/MacOS/stockfish", home / "stockfish" / "stockfish"]
    else:
        common = ["/usr/games/stockfish", "/usr/bin/stockfish", "/usr/local/bin/stockfish",
                  "/usr/local/games/stockfish", "/snap/bin/stockfish", "/opt/stockfish/stockfish",
                  home / "stockfish" / "stockfish"]
    for c in common:
        add(c)
    return found


def validate_engine(path: Path) -> tuple[bool, str]:
    """Initialise an executable through python-chess (Universal Chess Interface handshake)."""
    try:
        engine = chess.engine.SimpleEngine.popen_uci(str(path), timeout=20)
    except Exception as exc:  # external process boundary: any failure means "invalid engine"
        return False, f"{type(exc).__name__}: {exc}"
    try:
        return True, str(engine.id.get("name", "Unknown engine"))
    finally:
        try:
            engine.quit()
        except Exception as exc:
            sys.stderr.write(f"Engine did not quit cleanly ({exc}); closing.\n")
            engine.close()


def http_get_json(url: str) -> dict:
    headers = {"User-Agent": "ChessAnalyzer/1.0", "Accept": "application/vnd.github+json"}
    try:
        if requests is not None:
            resp = requests.get(url, headers=headers, timeout=30)
            resp.raise_for_status()
            return resp.json()
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as exc:  # network boundary
        raise InstallError(f"Could not contact the release server: {exc}") from exc


def download_file(url: str, dest: Path, progress: Callable, cancel: threading.Event) -> str:
    """Download with progress; returns the SHA-256 digest of the file."""
    digest = hashlib.sha256()
    headers = {"User-Agent": "ChessAnalyzer/1.0"}
    try:
        if requests is not None:
            resp = requests.get(url, headers=headers, stream=True, timeout=30)
            resp.raise_for_status()
            total = int(resp.headers.get("content-length", 0))
            chunks = resp.iter_content(65536)
        else:
            resp = urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=30)
            total = int(resp.headers.get("Content-Length", 0))
            chunks = iter(lambda: resp.read(65536), b"")
        done = 0
        with open(dest, "wb") as handle:
            for chunk in chunks:
                if cancel.is_set():
                    raise InstallCancelled("Download cancelled.")
                handle.write(chunk)
                digest.update(chunk)
                done += len(chunk)
                progress(done / total if total else None, f"Downloading... {done / 1048576:.1f} MB")
    except InstallError:
        raise
    except Exception as exc:  # network / disk boundary
        raise InstallError(f"Download failed: {exc}") from exc
    return digest.hexdigest()


def safe_extract(archive: Path, target: Path) -> None:
    target.mkdir(parents=True, exist_ok=True)
    root = target.resolve()
    try:
        if archive.name.lower().endswith(".zip"):
            with zipfile.ZipFile(archive) as zf:
                for name in zf.namelist():
                    if not (root / name).resolve().is_relative_to(root):
                        raise InstallError("Archive contains an unsafe path.")
                zf.extractall(target)
        else:
            with tarfile.open(archive) as tf:
                for member in tf.getmembers():
                    if not (root / member.name).resolve().is_relative_to(root) or member.issym() \
                            or member.islnk() or member.isdev():
                        raise InstallError("Archive contains an unsafe entry.")
                try:
                    tf.extractall(target, filter="data")
                except TypeError:
                    tf.extractall(target)
    except (zipfile.BadZipFile, tarfile.TarError, OSError) as exc:
        raise InstallError(f"Invalid or corrupted archive: {exc}") from exc


def platform_asset_tags() -> tuple[str, list[str]]:
    system, machine = platform.system(), platform.machine().lower()
    x86 = machine in ("amd64", "x86_64", "x64")
    arm = machine in ("arm64", "aarch64")
    if system == "Windows" and x86:
        return "windows", ["x86-64-avx2", "x86-64-sse41-popcnt", "x86-64"]
    if system == "Linux" and x86:
        return "ubuntu", ["x86-64-avx2", "x86-64-sse41-popcnt", "x86-64"]
    if system == "Darwin" and arm:
        return "macos", ["m1-apple-silicon"]
    if system == "Darwin" and x86:
        return "macos", ["x86-64-avx2", "x86-64-sse41-popcnt", "x86-64"]
    raise InstallError(f"No official prebuilt Stockfish was found for {system}/{machine}. "
                       "Please install Stockfish manually and choose the executable.")


def install_stockfish(progress: Callable, cancel: threading.Event) -> Path:
    os_tag, tags = platform_asset_tags()
    progress(None, "Contacting the official Stockfish release feed...")
    release = http_get_json(RELEASE_API)
    assets = release.get("assets", [])
    chosen = []
    for tag in tags:
        for asset in assets:
            name = str(asset.get("name", "")).lower()
            if name.startswith(f"stockfish-{os_tag}-{tag}.") and name.endswith((".zip", ".tar", ".tar.gz", ".tgz")):
                chosen.append(asset)
    if not chosen:
        raise InstallError("The release contains no build matching this system. Download Stockfish "
                           "from stockfishchess.org and choose the executable manually.")
    ENGINE_DIR.mkdir(parents=True, exist_ok=True)
    errors = []
    for asset in chosen:
        try:
            return _install_asset(asset, progress, cancel)
        except InstallCancelled:
            raise
        except InstallError as exc:
            errors.append(f"{asset.get('name')}: {exc}")
    raise InstallError("All compatible builds failed:\n" + "\n".join(errors))


def _install_asset(asset: dict, progress: Callable, cancel: threading.Event) -> Path:
    name = asset["name"]
    archive = ENGINE_DIR / name
    folder = ENGINE_DIR / re.sub(r"\.(zip|tar\.gz|tgz|tar)$", "", name)
    digest = download_file(asset["browser_download_url"], archive, progress, cancel)
    published = str(asset.get("digest") or "")
    if published.startswith("sha256:"):
        if published.split(":", 1)[1].lower() != digest.lower():
            archive.unlink(missing_ok=True)
            raise InstallError("Checksum mismatch: the download was rejected and deleted.")
        progress(None, "Checksum verified (SHA-256).")
    else:
        progress(None, "No published checksum; the executable will be tested before use.")
    progress(None, "Extracting...")
    if folder.exists():
        shutil.rmtree(folder, ignore_errors=True)
    safe_extract(archive, folder)
    archive.unlink(missing_ok=True)
    candidates = [p for p in folder.rglob("*") if p.is_file() and p.name.lower().startswith("stockfish")
                  and p.suffix.lower() in ("", ".exe") and p.stat().st_size > 500_000]
    if not candidates:
        shutil.rmtree(folder, ignore_errors=True)
        raise InstallError("No engine executable was found inside the archive.")
    exe = sorted(candidates, key=lambda p: (len(p.name), str(p)))[0]
    if not IS_WINDOWS:
        exe.chmod(exe.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    progress(None, "Testing the engine...")
    ok, info = validate_engine(exe)
    if not ok:
        shutil.rmtree(folder, ignore_errors=True)
        raise InstallError(f"The engine failed validation: {info}")
    progress(1.0, f"Installed {info}")
    return exe


@dataclass
class AIProfile:
    options: dict
    limit: "chess.engine.Limit"
    multipv: int
    window: float      # maximum Expected Points loss allowed when choosing a weaker candidate
    weak_prob: float   # probability of choosing a (bounded) weaker candidate
    note: str


def ai_profile(target: int, options) -> AIProfile:
    """Translate a target Elo into engine settings (approximate, documented calibration)."""
    has_elo = "UCI_Elo" in options and "UCI_LimitStrength" in options
    if has_elo:
        lo, hi = options["UCI_Elo"].min, options["UCI_Elo"].max
        if lo <= target <= hi:
            return AIProfile({"UCI_LimitStrength": True, "UCI_Elo": int(target)},
                             chess.engine.Limit(time=0.4), 1, 0.0, 0.0, f"UCI_Elo {target}")
        if target > hi:
            return AIProfile({"UCI_LimitStrength": False, "Skill Level": 20}, chess.engine.Limit(time=1.0),
                             1, 0.0, 0.0, "full strength")
    skill = int(max(0, min(20, round((target - 800) / 85.0))))
    depth_cap = int(max(1, round(1 + (target - 800) / 130.0)))
    time_cap = 0.05 + (target - 800) / 1700.0
    window = max(0.0, (1700 - target) / 900.0 * 0.15)
    prob = max(0.0, (1800 - target) / 1000.0 * 0.5)
    mpv = 4 if prob > 0 else 1
    return AIProfile({"UCI_LimitStrength": False, "Skill Level": skill},
                     chess.engine.Limit(depth=depth_cap, time=time_cap), mpv, window, prob,
                     f"Skill Level {skill}, depth {depth_cap}")


class EngineManager:
    """Centralised, thread-safe owner of the single engine process."""

    def __init__(self, post: Callable) -> None:
        self._post = post
        self._lock = threading.RLock()
        self._engine: Optional[chess.engine.SimpleEngine] = None
        self._profile_key = None
        self._closing = False
        self._cache: dict = {}
        self.path = ""
        self.name = ""
        self.author = ""
        self.option_names: list[str] = []

    def log(self, text: str) -> None:
        self._post(("engine_log", f"[{time.strftime('%H:%M:%S')}] {text}"))

    @property
    def alive(self) -> bool:
        return self._engine is not None

    def clear_cache(self) -> None:
        self._cache.clear()

    def _close_locked(self) -> None:
        engine, self._engine = self._engine, None
        self._profile_key = None
        if engine is None:
            return
        try:
            engine.quit()
        except Exception as exc:
            self.log(f"Engine did not quit cleanly ({exc}); closing the process.")
            engine.close()

    def start(self, path: str) -> None:
        with self._lock:
            if self._closing:
                raise EngineUnavailable("The application is closing.")
            self._close_locked()
            try:
                engine = chess.engine.SimpleEngine.popen_uci(path)
            except Exception as exc:  # external process boundary
                self.log(f"Could not start '{path}': {exc}")
                raise EngineUnavailable(f"Could not start the engine: {exc}") from exc
            self._engine = engine
            self.path = path
            self.name = str(engine.id.get("name", "Unknown engine"))
            self.author = str(engine.id.get("author", ""))
            self.option_names = sorted(engine.options.keys())
            self._cache.clear()
            self.log(f"Engine started: {self.name} ({path})")

    def stop(self) -> None:
        got = self._lock.acquire(timeout=1.0)
        try:
            if got:
                self._close_locked()
            elif self._engine is not None:
                self.log("Engine busy; terminating the process.")
                self._engine.close()
        finally:
            if got:
                self._lock.release()

    def shutdown(self) -> None:
        self._closing = True
        self.stop()

    def _call(self, fn: Callable):
        with self._lock:
            last: Optional[BaseException] = None
            for _ in range(2):
                if self._closing:
                    raise EngineUnavailable("The application is closing.")
                if self._engine is None:
                    if not self.path:
                        raise EngineUnavailable("No engine is configured.")
                    self.start(self.path)
                try:
                    return fn(self._engine)
                except (chess.engine.EngineTerminatedError, BrokenPipeError, ConnectionError, OSError) as exc:
                    last = exc
                    self.log(f"Engine process ended unexpectedly ({exc}); restarting.")
                    self._engine_dead()
            raise EngineUnavailable(f"The engine keeps terminating: {last}")

    def _engine_dead(self) -> None:
        engine, self._engine = self._engine, None
        self._profile_key = None
        if engine is not None:
            engine.close()

    def _apply(self, engine, options: dict) -> None:
        key = tuple(sorted(options.items()))
        if key == self._profile_key:
            return
        clean = {}
        for name, value in options.items():
            opt = engine.options.get(name)
            if opt is None:
                self.log(f"Option '{name}' is not supported by this engine; skipped.")
                continue
            if opt.type == "spin" and opt.min is not None and opt.max is not None:
                value = max(opt.min, min(opt.max, int(value)))
            clean[name] = value
        if clean:
            engine.configure(clean)
        self._profile_key = key

    @staticmethod
    def analysis_options() -> dict:
        return {"Threads": min(4, os.cpu_count() or 1), "Hash": 128,
                "UCI_LimitStrength": False, "Skill Level": 20}

    def analyse_lines(self, board: chess.Board, depth: int, time_limit: float, multipv: int):
        """Returns ([(move, cp_from_side_to_move), ...] best first, depth_reached)."""
        key = (board.epd(), depth, time_limit, multipv)
        if key in self._cache:
            return self._cache[key]
        limit = chess.engine.Limit(depth=depth, time=time_limit if time_limit > 0 else None)

        def run(engine):
            self._apply(engine, self.analysis_options())
            return engine.analyse(board, limit, multipv=multipv)

        infos = self._call(run)
        lines, depths = [], []
        for info in infos:
            pv = info.get("pv")
            if not pv or "score" not in info:
                continue
            lines.append((pv[0], score_to_cp(info["score"].pov(board.turn))))
            depths.append(info.get("depth", 0))
        if not lines:
            raise AnalysisError("The engine returned no analysis for a position.")
        result = (lines, float(min(depths)) if depths else 0.0)
        if len(self._cache) > 20000:
            self._cache.clear()
        self._cache[key] = result
        return result

    def best_move_for_elo(self, board: chess.Board, target: int) -> chess.Move:
        def run(engine):
            prof = ai_profile(target, engine.options)
            self._apply(engine, prof.options)
            if prof.multipv > 1:
                infos = engine.analyse(board, prof.limit, multipv=prof.multipv)
                cands = [(i["pv"][0], score_to_cp(i["score"].pov(board.turn)))
                         for i in infos if i.get("pv") and "score" in i]
                if cands:
                    return pick_candidate(cands, prof)
            result = engine.play(board, prof.limit)
            if result.move is None:
                raise EngineUnavailable("The engine did not return a move.")
            return result.move

        return self._call(run)


def pick_candidate(cands: list, prof: AIProfile) -> chess.Move:
    best_move, best_cp = cands[0]
    if random.random() > prof.weak_prob:
        return best_move
    best_ep = expected_points(best_cp)
    pool = [(m, best_ep - expected_points(c)) for m, c in cands if best_ep - expected_points(c) <= prof.window]
    weights = [math.exp(-loss / 0.05) for _, loss in pool]
    return random.choices([m for m, _ in pool], weights=weights, k=1)[0]


# =============================================================================
# 6. PGN PARSER
# =============================================================================
def parse_pgn_text(text: str) -> tuple[list, list[str]]:
    """Returns (games, messages). Never raises on malformed input."""
    text = text.strip()
    if not text:
        return [], ["The Portable Game Notation (PGN) text is empty."]
    stream = io.StringIO(text)
    games, messages, index = [], [], 0
    while True:
        try:
            game = chess.pgn.read_game(stream)
        except Exception as exc:  # parser boundary: report instead of crashing
            messages.append(f"Game {index + 1}: unreadable ({exc}).")
            break
        if game is None:
            break
        index += 1
        for err in game.errors:
            messages.append(f"Game {index}: {err}")
        if not list(game.mainline_moves()):
            messages.append(f"Game {index}: contains no playable moves and was skipped.")
            continue
        games.append(game)
    if not games and not messages:
        messages.append("No games were found in the text.")
    return games, messages


def game_label(game, number: int) -> str:
    h = game.headers
    return (f"{number}. {h.get('White', '?')} vs {h.get('Black', '?')} - {h.get('Result', '*')} "
            f"({h.get('Event', '?')}, {h.get('Date', '????.??.??')})")


# =============================================================================
# 7-9. EVALUATION ENGINE, MOVE CLASSIFICATION, ACCURACY AND ELO ESTIMATION
# =============================================================================
@dataclass
class MoveResult:
    ply: int
    color: bool
    san: str
    uci: str
    best_uci: str
    best_san: str
    cp_best: int
    cp_played: int
    ep_best: float
    ep_played: float
    ep_loss: float
    cp_loss: int
    grade: str
    reason: str
    eval_white: int
    phase: str
    opening: str = ""
    in_top_lines: bool = True


@dataclass
class GameAnalysis:
    results: list
    graph_values: list
    summary: dict
    headers: dict
    depth_reached: float
    start_eval: int = 0


class MoveClassifier:
    def __init__(self, settings: Settings, book: OpeningBook) -> None:
        d = settings.data
        self.t = d["thresholds"]
        self.great_gap = d["great_gap"]
        self.miss_min = d["miss_min_loss"]
        self.book = book

    def base_grade(self, loss: float) -> str:
        t = self.t
        if loss <= t["best"]:
            return "Best"
        if loss <= t["excellent"]:
            return "Excellent"
        if loss <= t["good"]:
            return "Good"
        if loss <= t["inaccuracy"]:
            return "Inaccuracy"
        if loss <= t["mistake"]:
            return "Mistake"
        return "Blunder"

    @staticmethod
    def _is_recapture(board: chess.Board, move: chess.Move) -> bool:
        if not board.move_stack or not board.is_capture(move):
            return False
        return move.to_square == board.peek().to_square

    @staticmethod
    def _is_sacrifice(board: chess.Board, move: chess.Move) -> bool:
        before = qsearch(board.copy(stack=False), -999, 999, 6)
        after_board = board.copy(stack=False)
        after_board.push(move)
        after = -qsearch(after_board, -999, 999, 6)
        return after - before <= -2

    def classify(self, board, move, top, in_top, ep_best, ep_played, loss, prev_loss, ucis, comment):
        t = self.t
        legal = board.legal_moves.count()
        gap = 0.0
        if len(top) >= 2:
            gap = expected_points(top[0][1]) - expected_points(top[1][1])
        if loss < t["good"] and len(ucis) <= 30 and (self.book.contains(ucis) or "book" in comment.lower()):
            return "Book", "Recognised opening theory."
        if (in_top and legal > 1 and loss <= t["excellent"] and ep_played >= 0.45 and ep_best < 0.97
                and not self._is_recapture(board, move) and self._is_sacrifice(board, move)):
            return "Brilliant", "A sound material sacrifice that keeps the position healthy."
        if in_top and legal > 1 and len(top) >= 2 and loss <= t["best"] and gap >= self.great_gap and ep_best >= 0.35:
            return "Great Move", f"The next best alternative was {gap * 100:.0f}% Expected Points worse."
        grade = self.base_grade(loss)
        if grade in ("Inaccuracy", "Mistake", "Blunder") and loss >= self.miss_min and ep_best >= 0.70 \
                and ep_played >= 0.40:
            opportunity = (prev_loss is not None and prev_loss >= self.miss_min) or gap >= self.great_gap
            if opportunity:
                return "Miss", "A clearly better position was available, but the opportunity was not taken."
        return grade, f"Expected Points loss {loss:.3f}."


def side_stats(rs: list, k: float, depth: float) -> dict:
    counts = {g: 0 for g in GRADES}
    for r in rs:
        counts[r.grade] += 1
    n = len(rs)
    if n == 0:
        return {"n": 0, "counts": counts, "accuracy": None, "avg_ep_loss": None, "acpl": None,
                "phases": {}, "est": None}
    losses = [r.ep_loss for r in rs]
    acc = accuracy_from_losses(losses, k)
    acpl = statistics.fmean(min(r.cp_loss, 500) for r in rs)
    phases = {}
    for ph in ("Opening", "Middlegame", "Endgame"):
        sub = [r.ep_loss for r in rs if r.phase == ph]
        phases[ph] = accuracy_from_losses(sub, k) if sub else None
    est = estimate_performance(losses, [r.cp_loss for r in rs], counts, phases, acc, depth, k)
    return {"n": n, "counts": counts, "accuracy": acc, "avg_ep_loss": sum(losses) / n, "acpl": acpl,
            "phases": phases, "est": est}


def build_summary(results: list, k: float, depth: float) -> dict:
    return {"white": side_stats([r for r in results if r.color == chess.WHITE], k, depth),
            "black": side_stats([r for r in results if r.color == chess.BLACK], k, depth),
            "game": side_stats(results, k, depth)}


class GameAnalyzer:
    """Sequentially evaluates every position of a game with one engine search per position."""

    def __init__(self, engine: EngineManager, settings: Settings, book: OpeningBook,
                 cancel: threading.Event, progress: Callable) -> None:
        self.engine, self.settings, self.cancel, self.progress = engine, settings, cancel, progress
        self.classifier = MoveClassifier(settings, book)
        self.book = book

    def run(self, game, depth: int, time_limit: float, multipv: int) -> GameAnalysis:
        if game.headers.get("Variant", "Standard").lower() not in ("standard", "chess", ""):
            raise AnalysisError("Only standard chess games are supported.")
        nodes = list(game.mainline())
        moves = [n.move for n in nodes]
        comments = [n.comment or "" for n in nodes]
        if not moves:
            raise AnalysisError("The game contains no moves.")
        board = game.board()
        boards = []
        for mv in moves:
            boards.append(board.copy())
            board.push(mv)
        boards.append(board.copy())
        lines, depths = [], []
        for idx, b in enumerate(boards):
            if self.cancel.is_set():
                raise AnalysisCancelled()
            if b.is_game_over():
                lines.append([(None, -MATE_CP if b.is_checkmate() else 0)])
            else:
                ln, d = self.engine.analyse_lines(b, depth, time_limit, multipv)
                lines.append(ln)
                depths.append(d)
            self.progress(idx + 1, len(boards))
        results, ucis, prev_loss = [], [], None
        for i, mv in enumerate(moves):
            b = boards[i]
            mover = b.turn
            top = lines[i]
            best_move, best_cp = top[0]
            found = [cp for m, cp in top if m == mv]
            if found:
                played_cp, in_top = found[0], True
            else:
                played_cp, in_top = min(best_cp, -lines[i + 1][0][1]), False
            ep_best, ep_played = expected_points(best_cp), expected_points(played_cp)
            loss = max(0.0, ep_best - ep_played)
            if loss < 1e-9:
                loss = 0.0
            cp_loss = max(0, clamp_cp(best_cp) - clamp_cp(played_cp))
            ucis.append(mv.uci())
            grade, reason = self.classifier.classify(b, mv, top, in_top, ep_best, ep_played, loss,
                                                     prev_loss, ucis, comments[i])
            eval_white = played_cp if mover == chess.WHITE else -played_cp
            results.append(MoveResult(
                ply=i + 1, color=mover, san=b.san(mv), uci=mv.uci(), best_uci=best_move.uci() if best_move else "",
                best_san=b.san(best_move) if best_move else "", cp_best=best_cp, cp_played=played_cp,
                ep_best=ep_best, ep_played=ep_played, ep_loss=loss, cp_loss=cp_loss, grade=grade, reason=reason,
                eval_white=eval_white, phase=game_phase(b, i),
                opening=self.book.name_for(ucis) if grade == "Book" else "", in_top_lines=in_top))
            prev_loss = loss
        start_cp = lines[0][0][1]
        start_eval = start_cp if boards[0].turn == chess.WHITE else -start_cp
        depth_reached = statistics.fmean(depths) if depths else float(depth)
        k = self.settings.data["accuracy_k"]
        return GameAnalysis(results, [start_eval] + [r.eval_white for r in results],
                            build_summary(results, k, depth_reached), dict(game.headers), depth_reached, start_eval)


def build_report(analysis: GameAnalysis, k: float) -> str:
    h = analysis.headers
    s = analysis.summary
    out = [f"{h.get('White', '?')} vs {h.get('Black', '?')}  |  {h.get('Event', '?')}  |  "
           f"{h.get('Date', '?')}  |  Result {h.get('Result', '*')}",
           f"Average engine depth reached: {analysis.depth_reached:.1f}", "",
           "ESTIMATED GAME PERFORMANCE - NOT AN OFFICIAL RATING", ""]
    for key, title in (("white", "White"), ("black", "Black"), ("game", "Whole game")):
        st = s[key]
        if not st["n"]:
            continue
        e = st["est"]
        out.append(f"{title}: accuracy {st['accuracy']:.1f}%  |  average centipawn loss {st['acpl']:.1f}  |  "
                   f"average Expected Points loss {st['avg_ep_loss']:.4f}")
        out.append(f"    estimated performance {e['elo']} ({e['category']}), confidence {e['confidence_label']} "
                   f"(about +/-{e['margin']})")
        ph = ", ".join(f"{p} {v:.1f}%" for p, v in st["phases"].items() if v is not None)
        out.append(f"    accuracy by phase: {ph}")
    out += ["", "MOVE GRADE DISTRIBUTION (White / Black)"]
    for g in GRADES:
        out.append(f"  {g:<11} {s['white']['counts'][g]:>3} / {s['black']['counts'][g]:>3}")
    worst = sorted(analysis.results, key=lambda r: r.ep_loss, reverse=True)[:5]
    out += ["", "LARGEST LOSSES"]
    for r in worst:
        num = (r.ply + 1) // 2
        out.append(f"  {num}{'.' if r.color == chess.WHITE else '...'} {r.san:<8} {r.grade:<10} "
                   f"loss {r.ep_loss:.3f}, best was {r.best_san}")
    out += ["", f"Method: Expected Points EP = 1/(1+10^(-cp/400)); accuracy = 100*exp(-k*average loss) with k = {k}.",
            "Accuracy is an application-defined estimate, not the official Chess.com or Lichess formula.",
            "A single game cannot establish a true Elo rating."]
    return "\n".join(out)


# =============================================================================
# 10. GUI HELPERS
# =============================================================================
def blend(c1: str, c2: str, t: float) -> str:
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(x * (1 - t) + y * t) for x, y in zip(a, b))


def setup_style(root: tk.Tk) -> None:
    st = ttk.Style(root)
    st.theme_use("clam")
    st.configure(".", background=PANEL, foreground=FG, fieldbackground=PANEL2, bordercolor="#444",
                 lightcolor=PANEL, darkcolor=PANEL, troughcolor=PANEL2, focuscolor=PANEL, font=(UI_FONT, 10))
    st.configure("TFrame", background=PANEL)
    st.configure("Dark.TFrame", background=BG)
    st.configure("TLabel", background=PANEL, foreground=FG)
    st.configure("Muted.TLabel", foreground=MUTED)
    st.configure("Title.TLabel", font=(UI_FONT, 14, "bold"))
    st.configure("Big.TLabel", font=(UI_FONT, 12, "bold"))
    st.configure("TButton", background="#3a3836", foreground=FG, padding=5, borderwidth=0)
    st.map("TButton", background=[("active", "#4a4846"), ("disabled", "#2a2928")], foreground=[("disabled", "#777")])
    st.configure("Accent.TButton", background=ACCENT, foreground="#101010")
    st.map("Accent.TButton", background=[("active", "#95c95a"), ("disabled", "#3d4a30")])
    st.configure("Side.TButton", background=BG, foreground=FG, padding=(14, 10), anchor="w", borderwidth=0)
    st.map("Side.TButton", background=[("active", "#2e2d2b")])
    st.configure("SideActive.TButton", background="#3a3836", foreground=ACCENT, padding=(14, 10), anchor="w")
    st.configure("Treeview", background=PANEL2, fieldbackground=PANEL2, foreground=FG, rowheight=21, borderwidth=0)
    st.configure("Treeview.Heading", background="#3a3836", foreground=FG)
    st.map("Treeview", background=[("selected", "#4b6fa5")], foreground=[("selected", "#ffffff")])
    st.map("TCombobox", fieldbackground=[("readonly", PANEL2)], foreground=[("readonly", FG)],
           selectbackground=[("readonly", PANEL2)], selectforeground=[("readonly", FG)])
    st.configure("TCheckbutton", background=PANEL, foreground=FG)
    st.map("TCheckbutton", background=[("active", PANEL)])
    st.configure("Horizontal.TProgressbar", troughcolor=PANEL2, background=ACCENT)
    root.option_add("*TCombobox*Listbox.background", PANEL2)
    root.option_add("*TCombobox*Listbox.foreground", FG)
    root.configure(bg=BG)


def make_text(parent, height: int = 6, **kw) -> tk.Text:
    return tk.Text(parent, height=height, bg=PANEL2, fg=FG, insertbackground=FG, relief="flat", wrap="word",
                   font=(UI_FONT, 9), padx=6, pady=4, highlightthickness=0, **kw)


def ask_promotion(parent, color: bool) -> int:
    top = tk.Toplevel(parent)
    top.title("Promote pawn")
    top.configure(bg=PANEL)
    top.transient(parent)
    choice = {"piece": chess.QUEEN}

    def pick(piece_type: int) -> None:
        choice["piece"] = piece_type
        top.destroy()

    for pt, name in ((chess.QUEEN, "Queen"), (chess.ROOK, "Rook"), (chess.BISHOP, "Bishop"), (chess.KNIGHT, "Knight")):
        ttk.Button(top, text=f"{GLYPHS[pt]} {name}", command=lambda p=pt: pick(p)).pack(side="left", padx=5, pady=10)
    top.grab_set()
    top.wait_window()
    return choice["piece"]


class BoardView(tk.Canvas):
    """Interactive board: click or drag moves, highlights, legal-move dots, coordinates, arrow."""
    COORD = 18

    def __init__(self, master, settings: Settings, on_move: Optional[Callable] = None,
                 interactive: Optional[Callable] = None, size: int = 520) -> None:
        super().__init__(master, width=size, height=size, bg=PANEL, highlightthickness=0)
        self.settings = settings
        self.on_move = on_move
        self.interactive = interactive or (lambda: False)
        self.board = chess.Board()
        self.flipped = False
        self.last_move: Optional[chess.Move] = None
        self.arrow: Optional[chess.Move] = None
        self.selected: Optional[int] = None
        self.drag: Optional[list] = None
        self.drag_hide: Optional[int] = None
        self.sq = 60
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)

    def set_position(self, board: chess.Board, last_move=None, arrow=None) -> None:
        self.board, self.last_move, self.arrow, self.selected = board.copy(), last_move, arrow, None
        self.redraw()

    def set_flipped(self, flipped: bool) -> None:
        self.flipped = flipped
        self.redraw()

    def _square_xy(self, square: int) -> tuple[int, int]:
        f, r = chess.square_file(square), chess.square_rank(square)
        col = 7 - f if self.flipped else f
        row = r if self.flipped else 7 - r
        return self.COORD + col * self.sq, row * self.sq

    def _xy_square(self, x: float, y: float) -> Optional[int]:
        col, row = int((x - self.COORD) // self.sq), int(y // self.sq)
        if x < self.COORD or not (0 <= col < 8 and 0 <= row < 8):
            return None
        f = 7 - col if self.flipped else col
        r = row if self.flipped else 7 - row
        return chess.square(f, r)

    def _draw_piece(self, cx: float, cy: float, piece: chess.Piece, tag: str) -> None:
        font = (PIECE_FONT, max(10, int(self.sq * 0.72)))
        glyph = GLYPHS[piece.piece_type]
        fill, edge = ("#fdfdfd", "#151515") if piece.color else ("#151515", "#f0f0f0")
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            self.create_text(cx + dx, cy + dy, text=glyph, font=font, fill=edge, tags=tag)
        self.create_text(cx, cy, text=glyph, font=font, fill=fill, tags=tag)

    def redraw(self) -> None:
        self.delete("all")
        w, h = max(self.winfo_width(), 160), max(self.winfo_height(), 160)
        self.sq = max(12, (min(w - self.COORD, h - self.COORD)) // 8)
        sq, d = self.sq, self.settings.data
        targets = {m.to_square for m in self.board.legal_moves if m.from_square == self.selected} \
            if self.selected is not None else set()
        check_sq = self.board.king(self.board.turn) if self.board.is_check() else None
        for square in chess.SQUARES:
            x, y = self._square_xy(square)
            base = d["light_color"] if (chess.square_file(square) + chess.square_rank(square)) % 2 else d["dark_color"]
            color = base
            if self.last_move and square in (self.last_move.from_square, self.last_move.to_square):
                color = blend(base, "#f7ec5a", 0.55)
            if square == self.selected:
                color = blend(base, "#4aa3ff", 0.55)
            if square == check_sq:
                color = blend(base, "#ff3b3b", 0.75)
            self.create_rectangle(x, y, x + sq, y + sq, fill=color, outline=color)
            if square in targets:
                cx, cy = x + sq / 2, y + sq / 2
                if self.board.piece_at(square) or self.board.is_en_passant(chess.Move(self.selected, square)):
                    self.create_oval(x + 3, y + 3, x + sq - 3, y + sq - 3, outline="#3a3a3a", width=3)
                else:
                    r = sq * 0.14
                    self.create_oval(cx - r, cy - r, cx + r, cy + r, fill="#3a3a3a", outline="")
        for i in range(8):
            rank = 7 - i if not self.flipped else i
            file_ = i if not self.flipped else 7 - i
            self.create_text(self.COORD / 2, i * sq + sq / 2, text=str(rank + 1), fill=MUTED, font=(UI_FONT, 8))
            self.create_text(self.COORD + i * sq + sq / 2, 8 * sq + self.COORD / 2,
                             text="abcdefgh"[file_], fill=MUTED, font=(UI_FONT, 8))
        for square, piece in self.board.piece_map().items():
            if square == self.drag_hide:
                continue
            x, y = self._square_xy(square)
            self._draw_piece(x + sq / 2, y + sq / 2, piece, "piece")
        if self.arrow:
            x1, y1 = self._square_xy(self.arrow.from_square)
            x2, y2 = self._square_xy(self.arrow.to_square)
            self.create_line(x1 + sq / 2, y1 + sq / 2, x2 + sq / 2, y2 + sq / 2, fill="#3d9be9",
                             width=max(4, sq // 8), arrow=tk.LAST, arrowshape=(16, 20, 8), capstyle="round")

    def _is_target(self, square: int) -> bool:
        return any(m.from_square == self.selected and m.to_square == square for m in self.board.legal_moves)

    def _press(self, e) -> None:
        square = self._xy_square(e.x, e.y)
        if square is None:
            return
        if self.selected is not None and square != self.selected and self._is_target(square):
            self._attempt(self.selected, square)
            return
        piece = self.board.piece_at(square)
        if piece and piece.color == self.board.turn and self.interactive():
            self.selected, self.drag = square, [square, False]
        else:
            self.selected, self.drag = None, None
        self.redraw()

    def _motion(self, e) -> None:
        if not self.drag:
            return
        if not self.drag[1]:
            self.drag[1] = True
            self.drag_hide = self.drag[0]
            self.redraw()
        self.delete("drag")
        piece = self.board.piece_at(self.drag[0])
        if piece:
            self._draw_piece(e.x, e.y, piece, "drag")

    def _release(self, e) -> None:
        drag, self.drag = self.drag, None
        self.drag_hide = None
        if drag and drag[1]:
            dest = self._xy_square(e.x, e.y)
            if dest is not None and dest != drag[0] and self._is_target(dest):
                self._attempt(drag[0], dest)
                return
        self.redraw()

    def _attempt(self, frm: int, to: int) -> None:
        piece = self.board.piece_at(frm)
        promo = None
        if piece and piece.piece_type == chess.PAWN and chess.square_rank(to) in (0, 7):
            promo = ask_promotion(self.winfo_toplevel(), piece.color)
        move = chess.Move(frm, to, promotion=promo)
        self.selected = None
        if move in self.board.legal_moves and self.on_move:
            self.on_move(move)
        else:
            self.redraw()


class EvalGraph(ttk.Frame):
    """Evaluation graph (Matplotlib when available, otherwise a Tkinter canvas)."""

    def __init__(self, master, on_select: Callable) -> None:
        super().__init__(master)
        self.on_select = on_select
        self.values: list[int] = []
        self.current = 0
        self.use_mpl = False
        self._geo = (34, 1.0)
        if HAS_MPL:
            try:
                self.fig = Figure(figsize=(5, 1.9), dpi=100, facecolor=PANEL)
                self.ax = self.fig.add_subplot(111)
                self.fig.subplots_adjust(left=0.07, right=0.99, top=0.96, bottom=0.22)
                self.mpl = FigureCanvasTkAgg(self.fig, master=self)
                self.mpl.get_tk_widget().pack(fill="both", expand=True)
                self.mpl.mpl_connect("button_press_event", self._mpl_click)
                self.use_mpl = True
            except Exception as exc:  # backend problems: fall back to canvas
                sys.stderr.write(f"Matplotlib graph disabled: {exc}\n")
        if not self.use_mpl:
            self.cv = tk.Canvas(self, height=150, bg=PANEL2, highlightthickness=0)
            self.cv.pack(fill="both", expand=True)
            self.cv.bind("<Configure>", lambda e: self.draw())
            self.cv.bind("<Button-1>", self._canvas_click)
        self.draw()

    def set_values(self, values: list) -> None:
        self.values, self.current = list(values), 0
        self.draw()

    def set_current(self, idx: int) -> None:
        self.current = idx
        self.draw()

    def _mpl_click(self, ev) -> None:
        if ev.inaxes is self.ax and ev.xdata is not None and self.values:
            self.on_select(max(0, min(len(self.values) - 1, int(round(ev.xdata * 2)))))

    def _canvas_click(self, e) -> None:
        left, step = self._geo
        if self.values:
            self.on_select(max(0, min(len(self.values) - 1, int(round((e.x - left) / step)))))

    def draw(self) -> None:
        vals = [max(-1000, min(1000, v)) for v in self.values]
        if self.use_mpl:
            ax = self.ax
            ax.clear()
            ax.set_facecolor(PANEL2)
            xs = [i / 2 for i in range(len(vals))]
            if vals:
                ax.fill_between(xs, vals, 0, where=[v >= 0 for v in vals], interpolate=True, color="#e6e6e6")
                ax.fill_between(xs, vals, 0, where=[v <= 0 for v in vals], interpolate=True, color="#6a6a6a")
                ax.plot(xs, vals, color="#ffffff", linewidth=0.8)
                ax.axvline(self.current / 2, color=ACCENT, linewidth=2)
                ax.set_xlim(0, max(1, (len(vals) - 1) / 2))
            ax.axhline(0, color="#888888", linewidth=0.8)
            ax.set_ylim(-1000, 1000)
            ax.set_yticks([-1000, -500, 0, 500, 1000])
            ax.set_yticklabels(["-10", "-5", "0", "+5", "+10"])
            ax.tick_params(colors=MUTED, labelsize=7)
            ax.set_xlabel("Move number (advantage in pawns, White above zero)", color=MUTED, fontsize=7)
            for spine in ax.spines.values():
                spine.set_color("#444444")
            self.mpl.draw_idle()
            return
        cv = self.cv
        cv.delete("all")
        w, h = max(cv.winfo_width(), 200), max(cv.winfo_height(), 100)
        left, right, top, bottom = 34, 8, 8, 18
        pw, ph = w - left - right, h - top - bottom
        mid = top + ph / 2
        for pawns in (-10, -5, 5, 10):
            y = mid - pawns * 100 / 1000 * (ph / 2)
            cv.create_line(left, y, left + pw, y, fill="#3a3a3a")
            cv.create_text(left - 4, y, text=f"{pawns:+d}", fill=MUTED, font=(UI_FONT, 7), anchor="e")
        cv.create_line(left, mid, left + pw, mid, fill="#888888")
        cv.create_text(left - 4, mid, text="0", fill=MUTED, font=(UI_FONT, 7), anchor="e")
        n = len(vals)
        if n:
            step = pw / max(1, n - 1)
            self._geo = (left, step)
            pts = []
            for i, v in enumerate(vals):
                x = left + i * step
                y = mid - v / 1000 * (ph / 2)
                cv.create_line(x, mid, x, y, fill="#d8d8d8" if v >= 0 else "#6a6a6a", width=max(1, int(step)))
                pts += [x, y]
            if n >= 2:
                cv.create_line(*pts, fill="#ffffff")
            cx = left + self.current * step
            cv.create_line(cx, top, cx, top + ph, fill=ACCENT, width=2)
            tick = max(2, 2 * math.ceil(40 / max(step, 0.1) / 2))
            for i in range(0, n, tick):
                cv.create_text(left + i * step, h - 8, text=str(i // 2), fill=MUTED, font=(UI_FONT, 7))


# =============================================================================
# 13. PGN ANALYSIS INTERFACE (board + analysis dashboard)
# =============================================================================
class AnalysisPage(ttk.Frame):
    def __init__(self, master, app: "ChessApp") -> None:
        super().__init__(master)
        self.app = app
        self.games: list = []
        self.game = None
        self.positions: list[chess.Board] = []
        self.moves: list[chess.Move] = []
        self.analysis: Optional[GameAnalysis] = None
        self.cur = 0
        self.token = 0
        self.busy = False
        self.cancel = threading.Event()
        self._syncing = False
        self.columnconfigure(0, weight=5)
        self.columnconfigure(1, weight=4)
        self.rowconfigure(0, weight=1)
        self._build_left()
        self._build_right()
        for kind, fn in (("analysis_progress", self.on_progress), ("analysis_done", self.on_done),
                         ("analysis_cancelled", self.on_cancelled), ("analysis_error", self.on_error)):
            app.register(kind, fn)
        app.root.bind("<Left>", lambda e: self._key(self.prev))
        app.root.bind("<Right>", lambda e: self._key(self.next))

    def _key(self, fn: Callable) -> None:
        focus = self.focus_get()
        if self.app.current_page == "analysis" and not isinstance(focus, (tk.Entry, tk.Text, ttk.Entry,
                                                                           ttk.Combobox, ttk.Spinbox)):
            fn()

    def _build_left(self) -> None:
        left = ttk.Frame(self)
        left.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)
        self.view = BoardView(left, self.app.settings)
        self.view.grid(row=0, column=0, sticky="nsew")
        self.pos_label = ttk.Label(left, text="Load a game to begin.", style="Big.TLabel")
        self.pos_label.grid(row=1, column=0, sticky="w", pady=(6, 2))
        nav = ttk.Frame(left)
        nav.grid(row=2, column=0, sticky="w")
        for text, cmd in (("|<", self.first), ("<", self.prev), (">", self.next), (">|", self.last),
                          ("Flip board", self.flip)):
            ttk.Button(nav, text=text, command=cmd, width=10 if len(text) > 2 else 4).pack(side="left", padx=2)
        self.show_best = tk.BooleanVar(value=True)
        ttk.Checkbutton(nav, text="Show engine's best move", variable=self.show_best,
                        command=self.refresh_board).pack(side="left", padx=10)

    def _build_right(self) -> None:
        right = ttk.Frame(self)
        right.grid(row=0, column=1, sticky="nsew", padx=(0, 8), pady=8)
        right.columnconfigure(0, weight=1)
        right.rowconfigure(5, weight=1)
        row1 = ttk.Frame(right)
        row1.grid(row=0, column=0, sticky="ew")
        ttk.Button(row1, text="Open PGN file...", command=self.open_file).pack(side="left")
        ttk.Button(row1, text="Paste PGN text...", command=self.paste_text).pack(side="left", padx=4)
        self.game_var = tk.StringVar()
        self.game_box = ttk.Combobox(row1, textvariable=self.game_var, state="readonly", width=38)
        self.game_box.pack(side="left", fill="x", expand=True)
        self.game_box.bind("<<ComboboxSelected>>", lambda e: self.select_game(self.game_box.current()))
        row2 = ttk.Frame(right)
        row2.grid(row=1, column=0, sticky="ew", pady=4)
        ttk.Label(row2, text="Search depth:").pack(side="left")
        self.depth_var = tk.IntVar(value=self.app.settings.data["depth"])
        ttk.Spinbox(row2, from_=4, to=30, width=4, textvariable=self.depth_var).pack(side="left", padx=4)
        ttk.Label(row2, text="(10 fast, 14 balanced, 18 deep)", style="Muted.TLabel").pack(side="left")
        self.btn_analyze = ttk.Button(row2, text="Analyze game", style="Accent.TButton", command=self.start_analysis)
        self.btn_analyze.pack(side="left", padx=8)
        self.btn_cancel = ttk.Button(row2, text="Cancel", command=self.cancel_analysis, state="disabled")
        self.btn_cancel.pack(side="left")
        self.progress = ttk.Progressbar(right, mode="determinate", maximum=100)
        self.progress.grid(row=2, column=0, sticky="ew")
        self.status = ttk.Label(right, text="No game loaded.", style="Muted.TLabel")
        self.status.grid(row=3, column=0, sticky="w")
        mid = ttk.Frame(right)
        mid.grid(row=4, column=0, sticky="ew", pady=4)
        mid.columnconfigure(0, weight=1)
        self.summary = ttk.Frame(mid)
        self.summary.grid(row=0, column=0, sticky="nw")
        self.sum_labels: dict = {}
        for c, head in enumerate(("", "White", "Black", "Game")):
            ttk.Label(self.summary, text=head, style="Muted.TLabel").grid(row=0, column=c, padx=6, sticky="w")
        for r, name in enumerate(("Accuracy", "Average centipawn loss", "Estimated Elo", "Category", "Confidence"), 1):
            ttk.Label(self.summary, text=name).grid(row=r, column=0, sticky="w", padx=6)
            for c, side in enumerate(("white", "black", "game"), 1):
                lab = ttk.Label(self.summary, text="-", style="Big.TLabel" if r in (1, 3) else "TLabel")
                lab.grid(row=r, column=c, sticky="w", padx=6)
                self.sum_labels[(name, side)] = lab
        ttk.Label(self.summary, text="Estimated Game Performance - Not an Official Rating", foreground="#e0b050"
                  ).grid(row=6, column=0, columnspan=4, sticky="w", padx=6)
        ttk.Label(self.summary, text="Accuracy is an application-defined estimate, not the official "
                  "Chess.com or Lichess formula.", style="Muted.TLabel", wraplength=420
                  ).grid(row=7, column=0, columnspan=4, sticky="w", padx=6)
        dist = ttk.Frame(mid)
        dist.grid(row=0, column=1, sticky="ne", padx=(10, 0))
        for c, head in enumerate(("Grade", "W", "B")):
            ttk.Label(dist, text=head, style="Muted.TLabel").grid(row=0, column=c, padx=4)
        self.dist_labels: dict = {}
        for r, g in enumerate(GRADES, 1):
            tk.Label(dist, text=g, fg=GRADE_COLORS[g], bg=PANEL, font=(UI_FONT, 9), anchor="w", width=11
                     ).grid(row=r, column=0, sticky="w")
            for c, side in enumerate(("white", "black"), 1):
                lab = ttk.Label(dist, text="0", width=3)
                lab.grid(row=r, column=c)
                self.dist_labels[(g, side)] = lab
        lower = ttk.Frame(right)
        lower.grid(row=5, column=0, sticky="nsew")
        lower.columnconfigure(0, weight=1)
        lower.rowconfigure(2, weight=1)
        self.graph = EvalGraph(lower, self.goto)
        self.graph.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        self.graph.configure(height=150)
        flt = ttk.Frame(lower)
        flt.grid(row=1, column=0, sticky="ew")
        ttk.Label(flt, text="Filter:").pack(side="left")
        self.filter_var = tk.StringVar(value="All moves")
        box = ttk.Combobox(flt, textvariable=self.filter_var, state="readonly", width=12, values=["All moves"] + GRADES)
        box.pack(side="left", padx=4)
        box.bind("<<ComboboxSelected>>", lambda e: self._rebuild_list())
        ttk.Label(flt, text="Search:").pack(side="left", padx=(8, 0))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self._rebuild_list())
        ttk.Entry(flt, textvariable=self.search_var, width=16).pack(side="left", padx=4)
        cols = ("no", "side", "move", "grade", "cpl", "epl")
        self.tree = ttk.Treeview(lower, columns=cols, show="headings", height=8, selectmode="browse")
        for col, head, wd in (("no", "No.", 50), ("side", "Side", 55), ("move", "Move", 80), ("grade", "Grade", 90),
                              ("cpl", "Centipawn Loss", 100), ("epl", "Expected Points Loss", 130)):
            self.tree.heading(col, text=head)
            self.tree.column(col, width=wd, anchor="w")
        for g, color in GRADE_COLORS.items():
            self.tree.tag_configure(g, foreground=color)
        self.tree.grid(row=2, column=0, sticky="nsew")
        sb = ttk.Scrollbar(lower, orient="vertical", command=self.tree.yview)
        sb.grid(row=2, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)
        self.details = make_text(lower, height=5)
        self.details.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(4, 0))
        self.details.configure(state="disabled")

    # ---- loading ----
    def open_file(self) -> None:
        path = filedialog.askopenfilename(title="Open PGN file", filetypes=[("PGN files", "*.pgn"), ("All files", "*.*")])
        if not path:
            return
        text = None
        for enc in ("utf-8-sig", "latin-1"):
            try:
                text = Path(path).read_text(encoding=enc)
                break
            except UnicodeDecodeError:
                continue
            except OSError as exc:
                messagebox.showerror("Cannot read file", str(exc))
                return
        self.load_text(text or "")

    def paste_text(self) -> None:
        top = tk.Toplevel(self.app.root)
        top.title("Paste Portable Game Notation (PGN)")
        top.configure(bg=PANEL)
        txt = make_text(top, height=20, width=80)
        txt.pack(fill="both", expand=True, padx=8, pady=8)

        def go() -> None:
            content = txt.get("1.0", "end")
            top.destroy()
            self.load_text(content)

        ttk.Button(top, text="Load", style="Accent.TButton", command=go).pack(pady=(0, 8))

    def load_text(self, text: str) -> None:
        if self.busy:
            messagebox.showinfo(APP_NAME, "Please cancel the running analysis first.")
            return
        games, messages = parse_pgn_text(text)
        if messages:
            shown = "\n".join(messages[:12]) + (f"\n... and {len(messages) - 12} more" if len(messages) > 12 else "")
            (messagebox.showwarning if games else messagebox.showerror)("PGN problems", shown)
        if not games:
            return
        self.games = games
        self.game_box["values"] = [game_label(g, i + 1) for i, g in enumerate(games)]
        self.game_box.current(0)
        self.select_game(0)

    def select_game(self, idx: int) -> None:
        if self.busy or idx < 0 or idx >= len(self.games):
            return
        game = self.games[idx]
        try:
            board = game.board()
            positions, moves = [board.copy()], []
            for mv in game.mainline_moves():
                board.push(mv)
                moves.append(mv)
                positions.append(board.copy())
        except (ValueError, AssertionError) as exc:
            messagebox.showerror("Invalid game", f"The game could not be set up: {exc}")
            return
        self.game, self.positions, self.moves, self.analysis = game, positions, moves, None
        h = game.headers
        self.status.configure(text=f"{h.get('White', '?')} vs {h.get('Black', '?')} | {h.get('Event', '?')} | "
                              f"{h.get('Date', '?')} | {h.get('Result', '*')} | {len(moves)} moves | "
                              f"Opening: {h.get('Opening', 'n/a')}")
        self.graph.set_values([])
        self._clear_summary()
        self._rebuild_list()
        self.goto(0)

    def _clear_summary(self) -> None:
        for lab in self.sum_labels.values():
            lab.configure(text="-")
        for lab in self.dist_labels.values():
            lab.configure(text="0")

    # ---- navigation ----
    def first(self) -> None:
        self.goto(0)

    def prev(self) -> None:
        self.goto(self.cur - 1)

    def next(self) -> None:
        self.goto(self.cur + 1)

    def last(self) -> None:
        self.goto(len(self.moves))

    def flip(self) -> None:
        self.view.set_flipped(not self.view.flipped)

    def goto(self, idx: int) -> None:
        if not self.positions:
            return
        self.cur = max(0, min(len(self.moves), idx))
        self.refresh_board()
        self.graph.set_current(self.cur)
        self._syncing = True
        try:
            if self.cur > 0 and self.tree.exists(str(self.cur)):
                self.tree.selection_set(str(self.cur))
                self.tree.see(str(self.cur))
            elif self.tree.selection():
                self.tree.selection_remove(self.tree.selection())
        finally:
            self._syncing = False
        self._update_details()

    def _move_label(self, ply: int) -> str:
        before = self.positions[ply - 1]
        return f"{before.fullmove_number}{'.' if before.turn == chess.WHITE else '...'}"

    def refresh_board(self) -> None:
        if not self.positions:
            return
        last = self.moves[self.cur - 1] if self.cur > 0 else None
        arrow = None
        if self.show_best.get() and self.analysis and self.cur < len(self.moves):
            uci = self.analysis.results[self.cur].best_uci
            arrow = chess.Move.from_uci(uci) if uci else None
        self.view.set_position(self.positions[self.cur], last, arrow)
        if self.cur == 0:
            self.pos_label.configure(text="Starting position")
        else:
            san = self.positions[self.cur - 1].san(self.moves[self.cur - 1])
            self.pos_label.configure(text=f"Move {self._move_label(self.cur)} {san}   (position {self.cur}/{len(self.moves)})")

    def _on_tree_select(self, _e) -> None:
        if self._syncing:
            return
        sel = self.tree.selection()
        if sel:
            self.goto(int(sel[0]))

    def _rebuild_list(self) -> None:
        self.tree.delete(*self.tree.get_children())
        if not self.positions:
            return
        wanted, needle = self.filter_var.get(), self.search_var.get().strip().lower()
        for ply in range(1, len(self.moves) + 1):
            san = self.positions[ply - 1].san(self.moves[ply - 1])
            side = "White" if self.positions[ply - 1].turn == chess.WHITE else "Black"
            grade, cpl, epl = "-", "", ""
            if self.analysis:
                r = self.analysis.results[ply - 1]
                grade, cpl, epl = r.grade, str(r.cp_loss), f"{r.ep_loss:.3f}"
            if wanted != "All moves" and grade != wanted:
                continue
            label = self._move_label(ply)
            if needle and needle not in san.lower() and needle not in grade.lower() and needle not in label:
                continue
            self.tree.insert("", "end", iid=str(ply), values=(label, side, san, grade, cpl, epl),
                             tags=(grade,) if grade in GRADE_COLORS else ())
        if self.cur > 0 and self.tree.exists(str(self.cur)):
            self._syncing = True
            self.tree.selection_set(str(self.cur))
            self._syncing = False

    def _update_details(self) -> None:
        if self.cur == 0 or not self.moves:
            text = "Starting position. Select a move to see its details."
        elif not self.analysis:
            text = (f"Move {self._move_label(self.cur)} {self.positions[self.cur - 1].san(self.moves[self.cur - 1])}"
                    "\nRun the analysis to grade this move.")
        else:
            r = self.analysis.results[self.cur - 1]
            text = (f"{self._move_label(self.cur)} {r.san}  -  {r.grade}\n{GRADE_TEXT[r.grade]} {r.reason}\n"
                    f"Engine's best move here: {r.best_san}.   Evaluation (mover's view): best {fmt_cp(r.cp_best)}, "
                    f"played {fmt_cp(r.cp_played)}.\nCentipawn loss {r.cp_loss}; Expected Points loss {r.ep_loss:.3f} "
                    f"(before {r.ep_best:.3f}, after {r.ep_played:.3f}).  Phase: {r.phase}."
                    + (f"  Opening: {r.opening}." if r.opening else "")
                    + f"  Evaluation after the move (White's view): {fmt_cp_white(r.eval_white)}.")
        self.details.configure(state="normal")
        self.details.delete("1.0", "end")
        self.details.insert("1.0", text)
        self.details.configure(state="disabled")

    # ---- analysis ----
    def start_analysis(self) -> None:
        if self.busy:
            return
        if self.game is None:
            messagebox.showinfo(APP_NAME, "Load a Portable Game Notation (PGN) game first.")
            return
        try:
            depth = int(self.depth_var.get())
        except (tk.TclError, ValueError):
            messagebox.showerror(APP_NAME, "The search depth must be a whole number.")
            return
        if not self.app.ensure_engine():
            return
        d = self.app.settings.data
        self.busy = True
        self.token += 1
        self.cancel = threading.Event()
        self.analysis = None
        self._clear_summary()
        self._rebuild_list()
        self.progress["value"] = 0
        self.btn_analyze.state(["disabled"])
        self.btn_cancel.state(["!disabled"])
        threading.Thread(target=self._worker, daemon=True,
                         args=(self.token, self.game, depth, float(d["time_limit"]), int(d["multipv"]), self.cancel)).start()

    def _worker(self, token, game, depth, time_limit, multipv, cancel) -> None:
        q = self.app.ui_queue
        try:
            analyzer = GameAnalyzer(self.app.engine, self.app.settings, self.app.book, cancel,
                                    lambda done, total: q.put(("analysis_progress", token, done, total)))
            q.put(("analysis_done", token, analyzer.run(game, depth, time_limit, multipv)))
        except AnalysisCancelled:
            q.put(("analysis_cancelled", token))
        except Exception as exc:  # worker boundary: report, never crash the application
            q.put(("analysis_error", token, f"{type(exc).__name__}: {exc}", traceback.format_exc()))

    def cancel_analysis(self) -> None:
        if self.busy:
            self.cancel.set()
            self.status.configure(text="Cancelling...")

    def _finish_ui(self) -> None:
        self.busy = False
        self.btn_analyze.state(["!disabled"])
        self.btn_cancel.state(["disabled"])

    def on_progress(self, msg) -> None:
        if msg[1] == self.token:
            self.progress["value"] = 100.0 * msg[2] / max(1, msg[3])
            self.status.configure(text=f"Analyzing position {msg[2]} of {msg[3]}...")

    def on_cancelled(self, msg) -> None:
        if msg[1] == self.token:
            self._finish_ui()
            self.status.configure(text="Analysis cancelled.")

    def on_error(self, msg) -> None:
        if msg[1] == self.token:
            self._finish_ui()
            self.status.configure(text="Analysis failed.")
            sys.stderr.write(msg[3])
            messagebox.showerror("Analysis failed", msg[2])

    def on_done(self, msg) -> None:
        if msg[1] != self.token:
            return
        self._finish_ui()
        self.analysis = msg[2]
        self.progress["value"] = 100
        self.status.configure(text="Analysis complete.")
        self.graph.set_values(self.analysis.graph_values)
        self.render_summary()
        self._rebuild_list()
        self.goto(self.cur)
        self.app.pages["report"].refresh()

    def render_summary(self) -> None:
        s = self.analysis.summary
        for side in ("white", "black", "game"):
            st = s[side]
            if not st["n"]:
                continue
            e = st["est"]
            vals = {"Accuracy": f"{st['accuracy']:.1f}%", "Average centipawn loss": f"{st['acpl']:.1f}",
                    "Estimated Elo": str(e["elo"]), "Category": e["category"],
                    "Confidence": f"{e['confidence_label']} (+/-{e['margin']})"}
            for name, text in vals.items():
                self.sum_labels[(name, side)].configure(text=text)
        for g in GRADES:
            for side in ("white", "black"):
                self.dist_labels[(g, side)].configure(text=str(s[side]["counts"][g]))


# =============================================================================
# 14. PLAY AGAINST THE OFFLINE ARTIFICIAL INTELLIGENCE OPPONENT
# =============================================================================
class PlayPage(ttk.Frame):
    def __init__(self, master, app: "ChessApp") -> None:
        super().__init__(master)
        self.app = app
        self.board = chess.Board()
        self.start_fen = chess.STARTING_FEN
        self.human = chess.WHITE
        self.over = False
        self.thinking = False
        self.token = 0
        self.redo_stack: list[chess.Move] = []
        self.columnconfigure(0, weight=5)
        self.columnconfigure(1, weight=3)
        self.rowconfigure(0, weight=1)
        left = ttk.Frame(self)
        left.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)
        self.view = BoardView(left, app.settings, on_move=self.on_user_move, interactive=self.can_human_move)
        self.view.grid(row=0, column=0, sticky="nsew")
        cap = ttk.Frame(left)
        cap.grid(row=1, column=0, sticky="ew", pady=4)
        self.cap_you = tk.Label(cap, text="", bg=PANEL, fg="#bbbbbb", font=(PIECE_FONT, 14))
        self.cap_you.pack(side="left")
        self.cap_ai = tk.Label(cap, text="", bg=PANEL, fg="#bbbbbb", font=(PIECE_FONT, 14))
        self.cap_ai.pack(side="right")
        right = ttk.Frame(self)
        right.grid(row=0, column=1, sticky="nsew", pady=8, padx=(0, 8))
        right.columnconfigure(0, weight=1)
        right.rowconfigure(9, weight=1)
        ttk.Label(right, text="Play against Stockfish (offline)", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        row = ttk.Frame(right)
        row.grid(row=1, column=0, sticky="ew", pady=4)
        ttk.Label(row, text="You play:").pack(side="left")
        self.color_var = tk.StringVar(value="White")
        ttk.Combobox(row, textvariable=self.color_var, values=["White", "Black", "Random"], state="readonly",
                     width=8).pack(side="left", padx=6)
        ttk.Label(right, text="Opponent strength (approximate Elo):").grid(row=2, column=0, sticky="w")
        presets = ttk.Frame(right)
        presets.grid(row=3, column=0, sticky="ew")
        self.elo = tk.IntVar(value=app.settings.data["ai_elo"])
        for i, e in enumerate((800, 1000, 1200, 1400, 1600, 1800, 2000, 2200, 2500)):
            ttk.Button(presets, text=str(e), width=5, command=lambda v=e: self.elo.set(v)).grid(row=i // 5, column=i % 5, padx=2, pady=2)
        scale = tk.Scale(right, from_=800, to=2500, orient="horizontal", variable=self.elo, resolution=10,
                         bg=PANEL, fg=FG, troughcolor=PANEL2, highlightthickness=0, length=300)
        scale.grid(row=4, column=0, sticky="ew")
        ttk.Label(right, text="Strength uses the engine's UCI_Elo when supported, otherwise Skill Level, search limits "
                  "and bounded candidate choice. Values are approximate.", style="Muted.TLabel", wraplength=330
                  ).grid(row=5, column=0, sticky="w")
        fen_row = ttk.Frame(right)
        fen_row.grid(row=6, column=0, sticky="ew", pady=4)
        ttk.Label(fen_row, text="Optional start position (Forsyth-Edwards Notation):").pack(anchor="w")
        self.fen_var = tk.StringVar()
        ttk.Entry(fen_row, textvariable=self.fen_var).pack(fill="x")
        btns = ttk.Frame(right)
        btns.grid(row=7, column=0, sticky="ew", pady=4)
        for text, cmd, style in (("New game", self.new_game, "Accent.TButton"), ("Undo", self.undo, "TButton"),
                                 ("Redo", self.redo, "TButton"), ("Resign", self.resign, "TButton"),
                                 ("Flip", lambda: self.view.set_flipped(not self.view.flipped), "TButton")):
            ttk.Button(btns, text=text, command=cmd, style=style, width=8).pack(side="left", padx=2)
        self.status = ttk.Label(right, text="Press New game to start.", style="Big.TLabel", wraplength=330)
        self.status.grid(row=8, column=0, sticky="w")
        self.history = make_text(right, height=10)
        self.history.grid(row=9, column=0, sticky="nsew", pady=4)
        self.history.configure(state="disabled")
        self.think_bar = ttk.Progressbar(right, mode="indeterminate")
        self.think_bar.grid(row=10, column=0, sticky="ew")
        app.register("ai_move", self.on_ai_move)
        app.register("ai_error", self.on_ai_error)
        self.refresh()

    def can_human_move(self) -> bool:
        return not self.over and not self.thinking and self.board.turn == self.human

    def new_game(self) -> None:
        fen = self.fen_var.get().strip()
        try:
            board = chess.Board(fen) if fen else chess.Board()
        except ValueError as exc:
            messagebox.showerror("Invalid Forsyth-Edwards Notation (FEN)", str(exc))
            return
        if not board.is_valid() or board.is_game_over():
            messagebox.showerror("Invalid position", "That position is illegal or the game is already over.")
            return
        if not self.app.ensure_engine():
            return
        self.token += 1
        self.board, self.start_fen = board, board.fen()
        choice = self.color_var.get()
        self.human = random.choice([chess.WHITE, chess.BLACK]) if choice == "Random" else (choice == "White")
        self.view.flipped = not self.human
        self.over, self.thinking = False, False
        self.redo_stack.clear()
        self.app.settings.data["ai_elo"] = int(self.elo.get())
        self.refresh()
        if self.board.turn != self.human:
            self._request_ai()

    def on_user_move(self, move: chess.Move) -> None:
        if not self.can_human_move() or move not in self.board.legal_moves:
            return
        self.app.play_sound("capture" if self.board.is_capture(move) else "move")
        self.board.push(move)
        self.redo_stack.clear()
        self.refresh()
        if not self._check_end():
            self._request_ai()

    def _request_ai(self) -> None:
        if self.over:
            return
        if not self.app.ensure_engine():
            self.status.configure(text="The engine is unavailable. Start it from Engine Status.")
            return
        self.token += 1
        token = self.token
        self.thinking = True
        self.think_bar.start(12)
        self.status.configure(text="Engine is thinking...")
        threading.Thread(target=self._ai_worker, args=(token, self.board.copy(), int(self.elo.get())), daemon=True).start()

    def _ai_worker(self, token: int, board: chess.Board, elo: int) -> None:
        q = self.app.ui_queue
        try:
            q.put(("ai_move", token, self.app.engine.best_move_for_elo(board, elo).uci()))
        except Exception as exc:  # worker boundary
            q.put(("ai_error", token, f"{type(exc).__name__}: {exc}"))

    def on_ai_move(self, msg) -> None:
        if msg[1] != self.token or self.over:
            return
        self.thinking = False
        self.think_bar.stop()
        try:
            move = chess.Move.from_uci(msg[2])
        except ValueError:
            self.status.configure(text="The engine returned an unreadable move.")
            return
        if move not in self.board.legal_moves:
            self.status.configure(text="The engine returned an illegal move; it was ignored.")
            return
        self.app.play_sound("capture" if self.board.is_capture(move) else "move")
        self.board.push(move)
        self.refresh()
        self._check_end()

    def on_ai_error(self, msg) -> None:
        if msg[1] != self.token:
            return
        self.thinking = False
        self.think_bar.stop()
        self.status.configure(text=f"Engine error: {msg[2]}")
        self.refresh()

    def _check_end(self) -> bool:
        outcome = self.board.outcome(claim_draw=True)
        if outcome is None:
            return False
        self.over = True
        reason = outcome.termination.name.replace("_", " ").title()
        if outcome.winner is None:
            text = f"Draw ({reason})."
        else:
            text = f"{'You win' if outcome.winner == self.human else 'The engine wins'} - {reason}."
        self.status.configure(text=text)
        self.app.play_sound("end")
        return True

    def undo(self) -> None:
        if not self.board.move_stack:
            return
        self.token += 1
        self.thinking = False
        self.think_bar.stop()
        count = 2 if self.board.turn == self.human else 1
        for _ in range(min(count, len(self.board.move_stack))):
            self.redo_stack.append(self.board.pop())
        self.over = False
        self.refresh()
        if self.board.turn != self.human:
            self._request_ai()

    def redo(self) -> None:
        if not self.redo_stack or self.thinking:
            return
        for _ in range(min(2, len(self.redo_stack))):
            move = self.redo_stack.pop()
            if move in self.board.legal_moves:
                self.board.push(move)
            if self.board.turn == self.human:
                break
        self.refresh()
        if not self._check_end() and self.board.turn != self.human:
            self._request_ai()

    def resign(self) -> None:
        if self.over or not self.board.move_stack and self.board.turn == self.human:
            return
        if messagebox.askyesno("Resign", "Do you really want to resign this game?"):
            self.token += 1
            self.thinking, self.over = False, True
            self.think_bar.stop()
            self.status.configure(text="You resigned. The engine wins.")
            self.refresh()

    def refresh(self) -> None:
        last = self.board.peek() if self.board.move_stack else None
        self.view.set_position(self.board, last)
        if not self.over and not self.thinking:
            self.status.configure(text="Your move." if self.board.turn == self.human else "Engine to move.")
        try:
            history = chess.Board(self.start_fen).variation_san(self.board.move_stack)
        except ValueError as exc:
            history = f"(history unavailable: {exc})"
        self.history.configure(state="normal")
        self.history.delete("1.0", "end")
        self.history.insert("1.0", history)
        self.history.configure(state="disabled")
        self.cap_you.configure(text="You captured: " + self._captured(self.human))
        self.cap_ai.configure(text="Engine captured: " + self._captured(not self.human))

    def _captured(self, by_color: bool) -> str:
        opponent, text = not by_color, ""
        for pt in (chess.QUEEN, chess.ROOK, chess.BISHOP, chess.KNIGHT, chess.PAWN):
            missing = max(0, START_COUNTS[pt] - len(self.board.pieces(pt, opponent)))
            text += GLYPHS[pt] * missing
        diff = material(self.board, by_color) - material(self.board, opponent)
        return text + (f" +{diff}" if diff > 0 else "")


# =============================================================================
# 12. ANALYSIS DASHBOARD (full report), SETTINGS AND ENGINE STATUS PAGES
# =============================================================================
class ReportPage(ttk.Frame):
    def __init__(self, master, app: "ChessApp") -> None:
        super().__init__(master)
        self.app = app
        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)
        top = ttk.Frame(self)
        top.grid(row=0, column=0, sticky="ew", padx=12, pady=8)
        ttk.Label(top, text="Analysis Dashboard - full game report", style="Title.TLabel").pack(side="left")
        ttk.Button(top, text="Export report...", command=self.export).pack(side="right")
        ttk.Button(top, text="Refresh", command=self.refresh).pack(side="right", padx=6)
        self.text = make_text(self, height=30)
        self.text.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 12))
        self.refresh()

    def _content(self) -> str:
        analysis = self.app.pages["analysis"].analysis if "analysis" in self.app.pages else None
        if analysis is None:
            return "No analysis yet. Open the PGN Analysis page, load a game and press Analyze game."
        return build_report(analysis, self.app.settings.data["accuracy_k"])

    def refresh(self) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        self.text.insert("1.0", self._content())
        self.text.configure(state="disabled")

    def export(self) -> None:
        path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text", "*.txt")])
        if path:
            try:
                Path(path).write_text(self._content(), encoding="utf-8")
            except OSError as exc:
                messagebox.showerror("Export failed", str(exc))


class SettingsPage(ttk.Frame):
    def __init__(self, master, app: "ChessApp") -> None:
        super().__init__(master)
        self.app = app
        self.vars: dict = {}
        self.colors: dict = {}
        ttk.Label(self, text="Settings", style="Title.TLabel").grid(row=0, column=0, columnspan=3, sticky="w", padx=12, pady=8)
        self.body = ttk.Frame(self)
        self.body.grid(row=1, column=0, sticky="nw", padx=12)
        self._build()

    def _row(self, r: int, label: str, widget_maker: Callable) -> None:
        ttk.Label(self.body, text=label).grid(row=r, column=0, sticky="w", pady=3, padx=(0, 12))
        widget_maker(self.body).grid(row=r, column=1, sticky="w", pady=3)

    def _build(self) -> None:
        d = self.app.settings.data
        t = d["thresholds"]
        spec = [("engine_path", "Stockfish executable path", d["engine_path"], 52), ("depth", "Analysis depth", d["depth"], 8),
                ("time_limit", "Analysis time limit per position (seconds, 0 = none)", d["time_limit"], 8),
                ("multipv", "Candidate lines per position (1-5)", d["multipv"], 8),
                ("ai_elo", "Default AI strength (Elo 800-2500)", d["ai_elo"], 8),
                ("accuracy_k", "Accuracy calibration coefficient k", d["accuracy_k"], 8),
                ("t_best", "Threshold: Best up to (Expected Points loss)", t["best"], 8),
                ("t_excellent", "Threshold: Excellent up to", t["excellent"], 8),
                ("t_good", "Threshold: Good up to", t["good"], 8),
                ("t_inaccuracy", "Threshold: Inaccuracy up to", t["inaccuracy"], 8),
                ("t_mistake", "Threshold: Mistake up to (above = Blunder)", t["mistake"], 8),
                ("great_gap", "Great Move: minimum gap to second-best move", d["great_gap"], 8),
                ("miss_min_loss", "Miss: minimum Expected Points loss", d["miss_min_loss"], 8)]
        r = 0
        for key, label, value, width in spec:
            self.vars[key] = tk.StringVar(value=str(value))
            if key == "engine_path":
                def maker(p, key=key, width=width):
                    f = ttk.Frame(p)
                    ttk.Entry(f, textvariable=self.vars[key], width=width).pack(side="left")
                    ttk.Button(f, text="Browse...", command=self.browse).pack(side="left", padx=4)
                    ttk.Button(f, text="Auto-detect", command=self.detect).pack(side="left")
                    ttk.Button(f, text="Download...", command=self.app.open_installer).pack(side="left", padx=4)
                    return f
            else:
                def maker(p, key=key, width=width):
                    return ttk.Entry(p, textvariable=self.vars[key], width=width)
            self._row(r, label, maker)
            r += 1
        for key, label in (("light_color", "Light square colour"), ("dark_color", "Dark square colour")):
            self.colors[key] = d[key]

            def cmaker(p, key=key):
                f = ttk.Frame(p)
                swatch = tk.Label(f, width=4, bg=self.colors[key])
                swatch.pack(side="left")
                ttk.Button(f, text="Choose...", command=lambda: self.pick(key, swatch)).pack(side="left", padx=6)
                return f

            self._row(r, label, cmaker)
            r += 1
        for key, label in (("flip_board", "Flip boards by default (play Black perspective)"), ("sound", "Sound effects"),
                           ("auto_detect", "Detect the engine automatically"),
                           ("offer_download", "Offer to download the engine when none is found")):
            self.vars[key] = tk.BooleanVar(value=d[key])
            self._row(r, label, lambda p, key=key: ttk.Checkbutton(p, variable=self.vars[key]))
            r += 1
        btns = ttk.Frame(self)
        btns.grid(row=2, column=0, sticky="w", padx=12, pady=10)
        ttk.Button(btns, text="Save settings", style="Accent.TButton", command=self.save).pack(side="left")
        ttk.Button(btns, text="Restore defaults", command=self.restore).pack(side="left", padx=8)
        self.msg = ttk.Label(self, text="", style="Muted.TLabel")
        self.msg.grid(row=3, column=0, sticky="w", padx=12)

    def pick(self, key: str, swatch: tk.Label) -> None:
        chosen = colorchooser.askcolor(color=self.colors[key], title="Choose colour")[1]
        if chosen:
            self.colors[key] = chosen
            swatch.configure(bg=chosen)

    def browse(self) -> None:
        self.app.browse_engine()
        self.vars["engine_path"].set(self.app.settings.data["engine_path"])

    def detect(self) -> None:
        self.app.init_engine()
        self.vars["engine_path"].set(self.app.settings.data["engine_path"])
        self.msg.configure(text="Engine detected and started." if self.app.engine.alive else "No working engine was found.")

    def save(self) -> None:
        try:
            new = copy.deepcopy(self.app.settings.data)
            new["engine_path"] = self.vars["engine_path"].get().strip()
            new["depth"] = int(self.vars["depth"].get())
            new["time_limit"] = float(self.vars["time_limit"].get())
            new["multipv"] = int(self.vars["multipv"].get())
            new["ai_elo"] = int(self.vars["ai_elo"].get())
            new["accuracy_k"] = float(self.vars["accuracy_k"].get())
            new["great_gap"] = float(self.vars["great_gap"].get())
            new["miss_min_loss"] = float(self.vars["miss_min_loss"].get())
            new["thresholds"] = {k: float(self.vars[f"t_{k}"].get()) for k in DEFAULT_THRESHOLDS}
            for key in ("flip_board", "sound", "auto_detect", "offer_download"):
                new[key] = bool(self.vars[key].get())
            new["light_color"], new["dark_color"] = self.colors["light_color"], self.colors["dark_color"]
            checked = {}
            for key, default in DEFAULT_SETTINGS.items():
                checked[key] = Settings._valid(key, new[key], default)
        except (ValueError, tk.TclError) as exc:
            messagebox.showerror("Invalid settings", str(exc))
            return
        self.app.settings.data = checked
        err = self.app.settings.save()
        self.app.apply_settings()
        self.msg.configure(text=err or "Settings saved.")

    def restore(self) -> None:
        self.app.settings.data = copy.deepcopy(DEFAULT_SETTINGS)
        self.app.settings.save()
        for child in self.body.winfo_children():
            child.destroy()
        self.vars.clear()
        self._build_again()
        self.app.apply_settings()
        self.msg.configure(text="Defaults restored.")

    def _build_again(self) -> None:
        for widget in self.winfo_children():
            if widget is not self.body and int(widget.grid_info().get("row", 0)) > 1:
                widget.destroy()
        self._build()


class EnginePage(ttk.Frame):
    def __init__(self, master, app: "ChessApp") -> None:
        super().__init__(master)
        self.app = app
        self.columnconfigure(0, weight=1)
        self.rowconfigure(3, weight=1)
        ttk.Label(self, text="Engine Status", style="Title.TLabel").grid(row=0, column=0, sticky="w", padx=12, pady=8)
        self.info = ttk.Label(self, text="", justify="left")
        self.info.grid(row=1, column=0, sticky="w", padx=12)
        btns = ttk.Frame(self)
        btns.grid(row=2, column=0, sticky="w", padx=12, pady=8)
        for text, cmd in (("Detect and start", app.init_engine), ("Restart engine", app.restart_engine),
                          ("Stop engine", app.stop_engine), ("Choose executable...", app.browse_engine),
                          ("Download Stockfish...", app.open_installer)):
            ttk.Button(btns, text=text, command=cmd).pack(side="left", padx=3)
        self.log = make_text(self, height=18)
        self.log.grid(row=3, column=0, sticky="nsew", padx=12, pady=(0, 12))
        self.log.configure(state="disabled")
        app.register("engine_log", lambda m: self.append(m[1]))
        self.refresh()

    def append(self, text: str) -> None:
        self.log.configure(state="normal")
        self.log.insert("end", text + "\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    def refresh(self) -> None:
        e = self.app.engine
        if e.alive:
            self.info.configure(text=f"Status: running\nEngine: {e.name}\nAuthor: {e.author}\nPath: {e.path}\n"
                                f"Supported options: {len(e.option_names)}")
        else:
            self.info.configure(text="Status: not running\nBoards and PGN loading still work; analysis and "
                                "Play vs AI need the engine.\nUse Detect, Choose executable, or Download.")


class EngineInstallDialog(tk.Toplevel):
    """Informs the user, then downloads and installs the official Stockfish release."""

    def __init__(self, app: "ChessApp") -> None:
        super().__init__(app.root)
        self.app = app
        self.title("Install Stockfish")
        self.configure(bg=PANEL)
        self.transient(app.root)
        self.q: queue.Queue = queue.Queue()
        self.cancel = threading.Event()
        self.running = False
        ttk.Label(self, wraplength=440, justify="left", text=(
            "Stockfish was not found. This application can download the official Stockfish release "
            "from github.com/official-stockfish/Stockfish (about 40-80 MB) into its 'engines' folder.\n\n"
            "The download is checked against the published SHA-256 checksum when one is available, "
            "extracted safely, and tested through the Universal Chess Interface before it is used. "
            "Nothing is downloaded until you press the button.")).pack(padx=14, pady=12)
        self.bar = ttk.Progressbar(self, mode="determinate", length=420, maximum=100)
        self.bar.pack(padx=14)
        self.label = ttk.Label(self, text="Waiting.", style="Muted.TLabel", wraplength=440)
        self.label.pack(padx=14, pady=6)
        row = ttk.Frame(self)
        row.pack(pady=10)
        self.go = ttk.Button(row, text="Download and install", style="Accent.TButton", command=self.start)
        self.go.pack(side="left", padx=4)
        ttk.Button(row, text="Choose existing executable...", command=self.manual).pack(side="left", padx=4)
        ttk.Button(row, text="Close", command=self.close).pack(side="left", padx=4)
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.grab_set()
        self.after(100, self.poll)

    def start(self) -> None:
        if self.running:
            return
        self.running = True
        self.go.state(["disabled"])
        threading.Thread(target=self._work, daemon=True).start()

    def _work(self) -> None:
        try:
            path = install_stockfish(lambda frac, text: self.q.put(("p", frac, text)), self.cancel)
            self.q.put(("done", str(path)))
        except InstallError as exc:
            self.q.put(("err", str(exc)))
        except Exception as exc:  # worker boundary
            self.q.put(("err", f"Unexpected error: {exc}"))

    def poll(self) -> None:
        try:
            while True:
                msg = self.q.get_nowait()
                if msg[0] == "p":
                    if msg[1] is None:
                        self.bar.configure(mode="indeterminate")
                        self.bar.start(15)
                    else:
                        self.bar.stop()
                        self.bar.configure(mode="determinate", value=msg[1] * 100)
                    self.label.configure(text=msg[2])
                elif msg[0] == "done":
                    self.bar.stop()
                    self.running = False
                    self.app.settings.data["engine_path"] = msg[1]
                    self.app.settings.save()
                    self.label.configure(text="Installed successfully.")
                    self.destroy()
                    return
                else:
                    self.bar.stop()
                    self.running = False
                    self.go.state(["!disabled"])
                    self.label.configure(text=msg[1])
        except queue.Empty:
            self.after(100, self.poll)

    def manual(self) -> None:
        self.app.browse_engine()
        if self.app.engine.alive:
            self.destroy()

    def close(self) -> None:
        self.cancel.set()
        self.destroy()


# =============================================================================
# 15. APPLICATION CONTROLLER
# =============================================================================
class ChessApp:
    def __init__(self) -> None:
        self.root = tk.Tk()
        self.root.title(f"{APP_NAME} - offline analysis and play")
        self.root.geometry("1380x880")
        self.root.minsize(1100, 720)
        setup_style(self.root)
        self.settings = Settings()
        self.settings_warning = self.settings.load()
        self.ui_queue: queue.Queue = queue.Queue()
        self.engine = EngineManager(self.ui_queue.put)
        self.book = OpeningBook()
        self.handlers: dict = {}
        self.pages: dict = {}
        self.current_page = "analysis"
        self.closing = False
        self.prompted_download = False
        side = ttk.Frame(self.root, style="Dark.TFrame")
        side.grid(row=0, column=0, sticky="ns")
        ttk.Label(side, text=APP_NAME, style="Title.TLabel", background=BG, foreground=ACCENT
                  ).pack(padx=14, pady=(14, 18))
        self.nav: dict = {}
        for key, text in (("analysis", "PGN Analysis"), ("play", "Play vs AI"), ("report", "Analysis Dashboard"),
                          ("settings", "Settings"), ("engine", "Engine Status")):
            btn = ttk.Button(side, text=text, style="Side.TButton", command=lambda k=key: self.show_page(k))
            btn.pack(fill="x")
            self.nav[key] = btn
        self.content = ttk.Frame(self.root)
        self.content.grid(row=0, column=1, sticky="nsew")
        self.content.columnconfigure(0, weight=1)
        self.content.rowconfigure(0, weight=1)
        self.status_bar = ttk.Label(self.root, text="", style="Muted.TLabel", background=BG)
        self.status_bar.grid(row=1, column=0, columnspan=2, sticky="ew")
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(0, weight=1)
        self.pages["analysis"] = AnalysisPage(self.content, self)
        self.pages["play"] = PlayPage(self.content, self)
        self.pages["report"] = ReportPage(self.content, self)
        self.pages["settings"] = SettingsPage(self.content, self)
        self.pages["engine"] = EnginePage(self.content, self)
        for page in self.pages.values():
            page.grid(row=0, column=0, sticky="nsew")
        self.show_page("analysis")
        self.apply_settings()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(40, self.poll_queue)
        self.root.after(250, self.startup)

    def register(self, kind: str, fn: Callable) -> None:
        self.handlers[kind] = fn

    def show_page(self, key: str) -> None:
        self.current_page = key
        self.pages[key].tkraise()
        for k, btn in self.nav.items():
            btn.configure(style="SideActive.TButton" if k == key else "Side.TButton")
        if key == "report":
            self.pages["report"].refresh()
        if key == "engine":
            self.pages["engine"].refresh()

    def poll_queue(self) -> None:
        """Only the GUI thread touches widgets; workers communicate exclusively through this queue."""
        try:
            for _ in range(300):
                msg = self.ui_queue.get_nowait()
                handler = self.handlers.get(msg[0])
                if handler:
                    try:
                        handler(msg)
                    except Exception:  # keep the event loop alive; show the traceback on the console
                        traceback.print_exc()
        except queue.Empty:
            pass
        if not self.closing:
            self.root.after(40, self.poll_queue)

    def apply_settings(self) -> None:
        d = self.settings.data
        for key in ("analysis", "play"):
            self.pages[key].view.redraw()
        if "analysis" in self.pages:
            self.pages["analysis"].view.flipped = d["flip_board"]
            self.pages["analysis"].view.redraw()
            self.pages["analysis"].depth_var.set(d["depth"])
        self.engine.clear_cache()
        path = d["engine_path"]
        if path and path != self.engine.path and Path(path).is_file():
            self.try_start(path)

    def play_sound(self, kind: str) -> None:
        if not self.settings.data["sound"]:
            return
        if IS_WINDOWS:
            try:
                import winsound
                winsound.Beep({"move": 600, "capture": 450, "end": 800}.get(kind, 600), 60)
                return
            except (ImportError, RuntimeError) as exc:
                sys.stderr.write(f"Sound unavailable: {exc}\n")
        self.root.bell()

    def update_engine_status(self) -> None:
        e = self.engine
        self.status_bar.configure(text=f" Engine: {e.name} - ready" if e.alive else
                                  " Engine: not running (boards and PGN viewing still work)")
        self.pages["engine"].refresh()

    def try_start(self, path: str) -> bool:
        try:
            self.engine.start(path)
        except EngineUnavailable as exc:
            self.engine.log(str(exc))
            self.update_engine_status()
            return False
        self.settings.data["engine_path"] = path
        self.settings.save()
        self.update_engine_status()
        return True

    def init_engine(self) -> bool:
        paths: list[str] = []
        saved = self.settings.data["engine_path"]
        if saved and Path(saved).is_file():
            paths.append(saved)
        if self.settings.data["auto_detect"] or not paths:
            paths += [str(p) for p in find_stockfish_candidates() if str(p) not in paths]
        for p in paths:
            if self.try_start(p):
                return True
        self.update_engine_status()
        return False

    def restart_engine(self) -> None:
        path = self.engine.path or self.settings.data["engine_path"]
        if not path or not self.try_start(path):
            self.init_engine()

    def stop_engine(self) -> None:
        self.engine.stop()
        self.update_engine_status()

    def browse_engine(self) -> None:
        path = filedialog.askopenfilename(title="Choose the Stockfish executable")
        if not path:
            return
        if not self.try_start(path):
            messagebox.showerror("Invalid engine", "That file could not be started as a Universal Chess Interface engine.")

    def open_installer(self) -> None:
        dialog = EngineInstallDialog(self)
        self.root.wait_window(dialog)
        if not self.engine.alive:
            self.init_engine()
        else:
            self.update_engine_status()

    def ensure_engine(self) -> bool:
        if self.engine.alive:
            return True
        if self.init_engine():
            return True
        if messagebox.askyesno("Stockfish not found", "No working Stockfish engine was found.\n\n"
                               "Do you want to download or choose one now?"):
            self.open_installer()
        return self.engine.alive

    def startup(self) -> None:
        if self.settings_warning:
            messagebox.showwarning("Settings", self.settings_warning)
        if not self.init_engine() and self.settings.data["offer_download"]:
            self.prompted_download = True
            if messagebox.askyesno("Stockfish not found", "No Stockfish engine was found on this computer.\n\n"
                                   "Download the official release now? (You can also choose an existing "
                                   "executable in Settings.)"):
                self.open_installer()

    def on_close(self) -> None:
        self.closing = True
        self.pages["analysis"].cancel.set()
        self.pages["play"].token += 1
        self.engine.shutdown()
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


# =============================================================================
# 16. MAIN EXECUTION ENTRY POINT
# =============================================================================
def main() -> None:
    try:
        app = ChessApp()
    except tk.TclError as exc:
        sys.stderr.write(f"The graphical interface could not be started: {exc}\n")
        sys.exit(1)
    app.run()


if __name__ == "__main__":
    main()