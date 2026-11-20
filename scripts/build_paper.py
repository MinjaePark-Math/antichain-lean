"""Force a real LaTeX build and record the exact paper/PDF snapshot.

The authoring workspace defaults to ai-drafts/lean-status; a public repository
defaults to paper/. This command does not generate Lean verification status.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys

from paper_snapshot import check_paper_receipt, paper_input_hashes, sha256


ROOT = Path(__file__).resolve().parents[1]


def default_paper_folder() -> Path:
    workspace = ROOT / "ai-drafts/lean-status"
    return workspace if workspace.is_dir() else ROOT / "paper"


def build_paper(folder: Path, latexmk: str) -> dict:
    folder = folder.resolve()
    if not (folder / "main.tex").is_file():
        raise RuntimeError(f"Missing paper source: {folder / 'main.tex'}")
    receipt_path = folder / "build-receipt.json"
    # A failed rebuild must not leave an old successful receipt in force.
    receipt_path.unlink(missing_ok=True)
    before = paper_input_hashes(folder)
    command = [latexmk, "-g", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]
    log_path = folder / "build-output.log"
    print(f"Building paper in {folder}; compiler output: {log_path}", flush=True)
    with log_path.open("w", encoding="utf-8", newline="\n") as output:
        result = subprocess.run(command, cwd=folder, text=True, encoding="utf-8",
                                errors="replace", stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Paper build failed with exit code {result.returncode}; see {log_path}")
    after = paper_input_hashes(folder)
    if before != after:
        raise RuntimeError("Paper inputs changed during the build; rerun on the finished snapshot")
    pdf = folder / "main.pdf"
    if not pdf.is_file() or not pdf.stat().st_size:
        raise RuntimeError("LaTeX reported success without a nonempty main.pdf")
    receipt = {
        "schema_version": 1,
        "status": "built",
        "completed_at": datetime.now(timezone.utc).isoformat(),
        "command": command,
        "working_directory": ".",
        "exit_code": result.returncode,
        "build_log": "build-output.log",
        "source_sha256": after,
        "pdf": "main.pdf",
        "pdf_sha256": sha256(pdf),
    }
    temporary = folder / ".build-receipt.json.tmp"
    temporary.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
                         encoding="utf-8", newline="\n")
    temporary.replace(receipt_path)
    check_paper_receipt(folder)
    print(f"Built and checked main.pdf against {len(after)} paper inputs.", flush=True)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper-dir", type=Path, default=None)
    parser.add_argument("--latexmk", default=shutil.which("latexmk") or "latexmk")
    args = parser.parse_args()
    build_paper(args.paper_dir or default_paper_folder(), args.latexmk)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError) as exc:
        sys.exit(str(exc))
