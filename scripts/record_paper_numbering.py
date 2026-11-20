"""Record current auxiliary labels and actual PDF headings (requires pypdf).

This is a numbering check, not a substitute for visual PDF review.
"""
from __future__ import annotations
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import re

from pypdf import PdfReader
from paper_snapshot import check_paper_receipt

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE_PAPER = ROOT / "ai-drafts/lean-status"
PAPER = WORKSPACE_PAPER if WORKSPACE_PAPER.is_dir() else ROOT / "paper"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    receipt = check_paper_receipt(PAPER)
    path = ROOT / "formalization/statement-inventory.json"
    inventory_bytes = path.read_bytes()
    inventory = json.loads(inventory_bytes.decode("utf-8"))
    source = ROOT / "main.tex" if (ROOT / "main.tex").exists() else ROOT / "source/main.tex"
    if sha(source) != inventory["source_sha256"]:
        raise RuntimeError("Current manuscript has not received a correspondence review")
    pdf = PAPER / "main.pdf"
    pdf_bytes = pdf.read_bytes()
    fingerprint = hashlib.sha256(pdf_bytes).hexdigest()
    if fingerprint != receipt["pdf_sha256"]:
        raise RuntimeError("PDF changed before numbering extraction")
    auxiliary_bytes = (PAPER / "main.aux").read_bytes()
    auxiliary = auxiliary_bytes.decode("utf-8")
    annotated_sha = receipt["source_sha256"]["main.tex"]
    watched = {path: hashlib.sha256(inventory_bytes).hexdigest(), pdf: fingerprint,
               PAPER / "main.aux": hashlib.sha256(auxiliary_bytes).hexdigest(),
               PAPER / "main.tex": annotated_sha, source: inventory["source_sha256"]}
    pages = [page.extract_text() or "" for page in PdfReader(io.BytesIO(pdf_bytes)).pages]
    labels = {}
    for line in auxiliary.splitlines():
        match = re.match(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}", line)
        if match:
            if match[1] in labels:
                raise RuntimeError(f"Duplicate auxiliary label: {match[1]}")
            labels[match[1]] = (match[2], match[3], line)
    stamp = datetime.now(timezone.utc).isoformat()
    checks = []
    for row in inventory["statements"]:
        number = row["number"]
        pattern = re.compile(r"^\s*" + row["kind"].capitalize() + r"\s*" +
                             re.escape(number) + r"(?:\s*\([^\n]*\))?\.", re.MULTILINE)
        hits = [(i + 1, match.group().strip()) for i, text in enumerate(pages)
                for match in pattern.finditer(text)]
        if not hits:
            raise RuntimeError(f"Actual numbered PDF heading missing: {row['id']}")
        source_labels = re.findall(r"\\label\{([^}]+)\}", row["statement_tex"])
        previous = row.get("compiled_number_check", {}).get("label")
        theorem_labels = [label for label in source_labels if re.match(
            r"^(thm|theorem|lem|lemma|prop|proposition|cor|rem|remark|ques|question|conj|conjecture):", label)]
        label = previous if previous in source_labels else next(iter(theorem_labels), None)
        check = dict(number=number, page=str(hits[0][0]), matches_reconstructed_number=True,
                     fresh_source_check=True, compiled_pdf_sha256=fingerprint,
                     compiled_page_count=len(pages), compiled_at=stamp,
                     source_sha256=inventory["source_sha256"], annotated_main_sha256=annotated_sha,
                     evidence_file="formalization/compiled-numbering-review.json",
                     pdf_heading=hits[0][1], pdf_heading_pages=sorted({page for page, _ in hits}))
        if label:
            if label not in labels or labels[label][0] != number:
                raise RuntimeError(f"Auxiliary/source counter mismatch: {row['id']}: {label}")
            if int(labels[label][1]) not in check["pdf_heading_pages"]:
                raise RuntimeError(f"Auxiliary/PDF page mismatch: {row['id']}")
            check.update(label=label, page=labels[label][1], auxiliary_line=labels[label][2],
                         evidence_kind="fresh_auxiliary_label_and_pdf_heading")
        else:
            check["evidence_kind"] = "fresh_pdf_heading_and_source_counter"
        row["compiled_number_check"] = check
        checks.append(dict(id=row["id"], **check))
    if check_paper_receipt(PAPER) != receipt or any(sha(file) != digest for file, digest in watched.items()):
        raise RuntimeError("Paper, auxiliary labels, manuscript or inventory changed during numbering review")
    evidence = dict(status="passed", pdf_snapshot_stable=True, checked_at=stamp, source_sha256=inventory["source_sha256"],
                    pdf_sha256=fingerprint, annotated_main_sha256=annotated_sha,
                    auxiliary_sha256=hashlib.sha256(auxiliary_bytes).hexdigest(),
                    page_count=len(pages), numbered_items=len(checks),
                    auxiliary_label_checks=sum("label" in check for check in checks),
                    checks=checks, scope="Actual PDF headings and current auxiliary labels; visual layout is reviewed separately.")
    output = ROOT / "formalization/compiled-numbering-review.json"
    output.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    inventory["compiled_numbering_evidence"] = dict(
        file="formalization/compiled-numbering-review.json", sha256=sha(output),
        source_sha256=inventory["source_sha256"], pdf_sha256=fingerprint,
        annotated_main_sha256=annotated_sha, page_count=len(pages), numbered_items=len(checks))
    inventory["numbering_source"] = (
        f"All {len(checks)} source numbers are confirmed by current auxiliary labels and actual headings "
        f"in the {len(pages)}-page annotated PDF, SHA-256 {fingerprint}. See compiled-numbering-review.json.")
    path.write_text(json.dumps(inventory, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"PASS: {len(checks)} actual PDF headings and {evidence['auxiliary_label_checks']} auxiliary labels")


if __name__ == "__main__":
    main()
