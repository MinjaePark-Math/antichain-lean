"""Bind a built paper PDF to the exact local source and figure snapshot."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


INPUT_SUFFIXES = frozenset({
    ".tex", ".bib", ".sty", ".cls", ".pdf", ".png", ".jpg", ".jpeg",
    ".eps", ".ps", ".svg", ".webp", ".gif", ".tif", ".tiff", ".bmp",
    ".mps", ".jbig2", ".jb2",
})
EXCLUDED_DIRECTORIES = frozenset({
    ".git", ".lake", "__pycache__", "output", "outputs", "intermediates",
    "build", "_build",
})


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def paper_input_hashes(folder: Path | str) -> dict[str, str]:
    """Hash local TeX/bibliography/style inputs and image/PDF figures.

    The root main.pdf is the output. Build/output/intermediate directories and
    ordinary auxiliary files are excluded. A PDF under figures/ is an input.
    Relative paths and the complete file set are part of the snapshot.
    """
    folder = Path(folder)
    if not folder.is_dir():
        raise RuntimeError(f"Paper folder does not exist: {folder}")
    inputs: dict[str, str] = {}
    for path in sorted(folder.rglob("*")):
        relative = path.relative_to(folder)
        if any(part.lower() in EXCLUDED_DIRECTORIES for part in relative.parts[:-1]):
            continue
        if relative.as_posix().lower() == "main.pdf":
            continue
        if path.is_file() and path.suffix.lower() in INPUT_SUFFIXES:
            inputs[relative.as_posix()] = sha256(path)
    return inputs


def check_paper_receipt(folder: Path | str) -> dict[str, Any]:
    """Require a successful build receipt matching all inputs and PDF bytes.

    This verifies a recorded build snapshot, not the mathematics in the paper.
    """
    folder = Path(folder)
    receipt_path = folder / "build-receipt.json"
    if not receipt_path.is_file():
        raise RuntimeError(f"Missing paper build receipt: {receipt_path}")
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise RuntimeError(f"Invalid paper build receipt: {receipt_path}") from exc
    if not isinstance(receipt, dict) or receipt.get("schema_version") != 1 or receipt.get("status") != "built":
        raise RuntimeError(f"Unrecognized paper build receipt: {receipt_path}")
    if receipt.get("pdf") != "main.pdf":
        raise RuntimeError("Paper receipt does not identify main.pdf")
    expected = receipt.get("source_sha256")
    current = paper_input_hashes(folder)
    if not isinstance(expected, dict) or set(expected) != set(current):
        raise RuntimeError("Paper input file set differs from the successful build; rebuild the PDF")
    changed = [name for name, value in current.items() if expected[name] != value]
    if changed:
        raise RuntimeError("Paper input changed since the successful build: " + ", ".join(changed))
    pdf = folder / "main.pdf"
    if not pdf.is_file() or not pdf.stat().st_size:
        raise RuntimeError(f"Missing or empty paper PDF: {pdf}")
    if receipt.get("pdf_sha256") != sha256(pdf):
        raise RuntimeError("Paper PDF differs from the successful build receipt")
    return receipt
