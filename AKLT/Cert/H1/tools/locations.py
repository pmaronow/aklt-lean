"""Shared H1 input and report locations, independent of the export root."""
import os
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[4]
INPUT_DIR = Path(os.environ.get('H1_INPUT_DIR', REPOSITORY / 'data/h1'))
REPORT_DIR = Path(os.environ.get('H1_REGEN_REPORT', REPOSITORY / 'verification/runs/H1'))
