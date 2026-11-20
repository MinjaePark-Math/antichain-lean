"""Check deterministic release gates and frozen evidence; does not prove mathematics.

The claim statuses, explicit external parameters, and proof-idea
layout are checked mechanically. Mathematical source correspondence still
requires the separately recorded independent review.
"""
from __future__ import annotations
import hashlib
import gzip
import json
from pathlib import Path
import re
from paper_snapshot import check_paper_receipt
from tex_markup import AUTHOR_TOKEN, canonical_tex, clean_companion_tex

ROOT = Path(__file__).resolve().parents[1]
if not (ROOT / "release").exists() and (ROOT / "publish/antichain-lean/release").exists():
    ROOT = ROOT / "publish/antichain-lean"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def audit_development_note(report):
    return (
        f"Fresh complete production build and exhaustive type/value/transitive-axiom audit passed at {report['checked_at']}: "
        f"{len(report['source_sha256']) - 1} modules plus the root, {report['theorem_count']} theorems "
        f"and {report['declaration_count']} declarations. The exact current source-facing certificates "
        "are listed here. Independent statement and written-proof correspondence were reviewed separately; "
        "any external mathematical theorem parameter is listed separately for that claim.")


def check_paper_numbering_snapshot(paper, inventory, evidence_path):
    """Require numbering evidence for the actual current PDF, not a prior build."""
    record = inventory.get("compiled_numbering_evidence", {})
    if (record.get("file") != "formalization/compiled-numbering-review.json"
            or not evidence_path.is_file() or record.get("sha256") != sha(evidence_path)):
        raise RuntimeError("Missing or stale compiled numbering review")
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    bindings = dict(source_sha256=inventory["source_sha256"], pdf_sha256=sha(paper / "main.pdf"),
                    annotated_main_sha256=sha(paper / "main.tex"),
                    numbered_items=len(inventory["statements"]))
    if evidence.get("status") != "passed" or any(
            record.get(key) != value or evidence.get(key) != value for key, value in bindings.items()):
        raise RuntimeError("Compiled numbering review describes a different manuscript or PDF")
    page_count = evidence.get("page_count")
    if (type(page_count) is not int or page_count <= 0 or record.get("page_count") != page_count
            or evidence.get("pdf_snapshot_stable") is not True):
        raise RuntimeError("Incomplete PDF numbering snapshot or page count")
    checks = evidence.get("checks", [])
    if len(checks) != len(inventory["statements"]) or len({row["id"] for row in checks}) != len(checks):
        raise RuntimeError("Missing or repeated compiled numbering checks")
    by_id = {row["id"]: {key: value for key, value in row.items() if key != "id"} for row in checks}
    for row in inventory["statements"]:
        check = row.get("compiled_number_check", {})
        if (by_id.get(row["id"]) != check or check.get("number") != row["number"]
                or check.get("fresh_source_check") is not True
                or check.get("matches_reconstructed_number") is not True
                or check.get("compiled_pdf_sha256") != bindings["pdf_sha256"]
                or check.get("source_sha256") != bindings["source_sha256"]
                or check.get("annotated_main_sha256") != bindings["annotated_main_sha256"]
                or check.get("compiled_page_count") != evidence.get("page_count")
                or check.get("evidence_file") != "formalization/compiled-numbering-review.json"):
            raise RuntimeError(f"Stale or incomplete compiled statement number: {row['id']}")
        heading = check.get("pdf_heading")
        pages = check.get("pdf_heading_pages")
        page = check.get("page")
        heading_pattern = r"^" + row["kind"].capitalize() + r"\s*" + re.escape(row["number"]) + r"(?:\s*\([^\n]*\))?\."
        if (not isinstance(heading, str) or not re.match(heading_pattern, heading)
                or not isinstance(pages, list) or not pages
                or any(type(p) is not int or not 1 <= p <= page_count for p in pages)
                or pages != sorted(set(pages)) or not isinstance(page, str) or not page.isdecimal()
                or int(page) not in pages):
            raise RuntimeError(f"Actual PDF heading/page evidence missing: {row['id']}")
        if check.get("label"):
            pattern = (r"^\\newlabel\{" + re.escape(check["label"]) + r"\}\{\{" +
                       re.escape(row["number"]) + r"\}\{" + re.escape(page) + r"\}")
            if (check.get("evidence_kind") != "fresh_auxiliary_label_and_pdf_heading"
                    or not re.match(pattern, check.get("auxiliary_line", ""))):
                raise RuntimeError(f"Actual auxiliary-label evidence missing: {row['id']}")
        elif check.get("evidence_kind") != "fresh_pdf_heading_and_source_counter":
            raise RuntimeError(f"Actual unlabelled heading evidence missing: {row['id']}")
    if evidence.get("auxiliary_label_checks") != sum(bool(row.get("label")) for row in checks):
        raise RuntimeError("Auxiliary-label evidence count differs")


def read_evidence(path):
    compressed = path.with_suffix(path.suffix + ".gz")
    if compressed.exists():
        with gzip.open(compressed, "rt", encoding="utf-8") as source:
            return json.load(source)
    return json.loads(path.read_text(encoding="utf-8"))


def iter_json_object_entries(source, chunk_size=65536):
    """Stream a JSON object's entries without retaining the complete object.

    Incomplete large keys/values grow the next read geometrically, so repeatedly
    retrying the standard decoder does not rescan a large entry quadratically.
    Consumed prefixes are discarded only when more input is needed.
    """
    if chunk_size <= 0:
        raise ValueError("JSON chunk size must be positive")

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise RuntimeError(f"Duplicate JSON object key: {key}")
            result[key] = value
        return result

    decoder = json.JSONDecoder(object_pairs_hook=unique_object)
    buffer, position, eof = "", 0, False

    def fill(size):
        nonlocal buffer, position, eof
        if eof:
            return False
        more = source.read(size)
        if not more:
            eof = True
            return False
        buffer = buffer[position:] + more
        position = 0
        return True

    def peek():
        nonlocal position
        while True:
            while position < len(buffer) and buffer[position] in " \t\r\n":
                position += 1
            if position < len(buffer):
                return buffer[position]
            if not fill(chunk_size):
                return ""

    def decode_value():
        nonlocal position
        size = chunk_size
        while True:
            try:
                value, end = decoder.raw_decode(buffer, position)
            except json.JSONDecodeError as exc:
                if not fill(size):
                    raise RuntimeError("Malformed or truncated frozen-type JSON") from exc
                size *= 2
            else:
                position = end
                return value

    if peek() != "{":
        raise RuntimeError("Frozen-type JSON must be a root object")
    position += 1
    seen = set()
    if peek() == "}":
        position += 1
    else:
        while True:
            if peek() != '"':
                raise RuntimeError("Expected a frozen-type JSON object key")
            name = decode_value()
            if not isinstance(name, str) or name in seen:
                raise RuntimeError(f"Duplicate or invalid frozen-type key: {name}")
            seen.add(name)
            if peek() != ":":
                raise RuntimeError("Expected a colon after a frozen-type key")
            position += 1
            if not peek():
                raise RuntimeError("Truncated frozen-type JSON value")
            value = decode_value()
            yield name, value
            next_char = peek()
            if next_char == "}":
                position += 1
                break
            if next_char != ",":
                raise RuntimeError("Expected a comma or closing frozen-type object")
            position += 1
    if peek():
        raise RuntimeError("Trailing data after frozen-type JSON object")


def check_frozen_types(path, actual, *, chunk_size=65536):
    """Compare every complete frozen type while retaining only one entry."""
    compressed = path.with_suffix(path.suffix + ".gz")
    selected = compressed if compressed.exists() else path
    opener = gzip.open if compressed.exists() else open
    seen = set()
    try:
        with opener(selected, "rt", encoding="utf-8") as source:
            for name, entry in iter_json_object_entries(source, chunk_size):
                if name in seen or name not in actual:
                    raise RuntimeError(f"Frozen declaration set changed: {name}")
                seen.add(name)
                keys = ("type_sha256", "type_expression", "universe_parameters")
                if not isinstance(entry, dict) or any(key not in entry for key in keys):
                    raise RuntimeError(f"Incomplete or invalid frozen type entry: {name}")
                if any(entry[key] != actual[name][key] for key in keys):
                    raise RuntimeError(f"Frozen type changed: {name}")
    except (OSError, EOFError, UnicodeError) as exc:
        raise RuntimeError(f"Unreadable or truncated frozen-type evidence: {selected}") from exc
    if seen != set(actual):
        raise RuntimeError("Frozen declaration set changed: missing declarations")


def tex_escaped(text, index):
    previous = index - 1
    while previous >= 0 and text[previous] == "\\":
        previous -= 1
    return (index - previous - 1) % 2 == 1


def uncomment_tex(text):
    """Ignore comments without changing line or character offsets."""
    active = list(text)
    comment = False
    for index, char in enumerate(text):
        if char == "\n":
            comment = False
        elif comment:
            active[index] = " "
        elif char == "%" and not tex_escaped(text, index):
            active[index] = " "
            comment = True
    return "".join(active)


def check_tex_groups(text, description):
    active = uncomment_tex(text)
    stack = []
    for index, char in enumerate(active):
        if tex_escaped(active, index):
            continue
        if char == "{":
            stack.append(index)
        elif char == "}":
            if not stack:
                raise RuntimeError(f"Unbalanced TeX closing group in {description}")
            stack.pop()
    if stack:
        raise RuntimeError(f"Unclosed TeX group in {description}")


def active_proofs(text):
    """Return active proof environments, excluding commented legacy proofs."""
    active = uncomment_tex(text)
    token = r"\\(begin|end)\{proof\}(?:\[([^\]]*)\])?"
    current = None
    proofs = []
    for match in re.finditer(token, active):
        if tex_escaped(active, match.start()):
            continue
        if match[1] == "begin":
            if current is not None:
                raise RuntimeError("Nested proof environments need a new layout review")
            current = (match.start(), match[2])
        else:
            if current is None:
                raise RuntimeError("Active end{proof} has no matching begin")
            proofs.append((current[0], match.end(), current[1]))
            current = None
    if current is not None:
        raise RuntimeError("Unclosed active proof environment")
    return proofs


def check_complete_claims(rows, expected_rows, actual):
    """Enforce the final status/type policy, independently of generator tables."""
    originals = {row["id"]: row for row in expected_rows}
    proved_ids = {row["id"] for row in expected_rows if row["is_proved_assertion"]}
    checked_ids = {row["id"] for row in rows if row["lean_status"] in ("fully_verified", "verified_modulo_cited")}
    if checked_ids != proved_ids:
        raise RuntimeError("Each in-scope assertion needs a complete or explicitly conditional certificate")
    for row in rows:
        if row["is_proved_assertion"] != originals[row["id"]]["is_proved_assertion"]:
            raise RuntimeError(f"Assertion classification changed: {row['id']}")
        for field in ("kind", "number"):
            if field in originals[row["id"]] and row.get(field) != originals[row["id"]][field]:
                raise RuntimeError(f"Reviewed assertion {field} changed: {row['id']}")
        if row["id"] not in proved_ids:
            continue
        inputs = row.get("external_inputs")
        if (inputs != originals[row["id"]].get("external_inputs")
                or (inputs != [] and inputs != ["IIDFiniteVarianceCLT"])
                or bool(inputs) != (row["lean_status"] == "verified_modulo_cited")):
            raise RuntimeError(f"External mathematical premises disagree with reviewed status: {row['id']}")
        if inputs and row["id"] != "ANT-COORDINATE-CLT":
            raise RuntimeError(f"Unexpected iid CLT dependency: {row['id']}")
        names = row.get("lean_declarations", [])
        if not names or len(names) != len(set(names)):
            raise RuntimeError(f"Missing or repeated complete certificates: {row['id']}")
        if set(row.get("verified_type_sha256", {})) != set(names):
            raise RuntimeError(f"Complete certificate types are not all frozen: {row['id']}")
        cited_type_found = False
        for name in names:
            if name not in actual:
                raise RuntimeError(f"Missing complete certificate: {row['id']}: {name}")
            entry = actual[name]
            # Search the actual frozen type, not declaration names or proof
            # implementation text. A direct geometry producer may conclude the
            # legacy record, but it is not a mapped paper assertion certificate.
            for field in ("type_expression", "readable_type"):
                value = entry.get(field)
                if not isinstance(value, str) or not value:
                    raise RuntimeError(f"Missing full declaration type: {name}: {field}")
                if re.search(r"\b(?:HumphreysAlcoveInput|DKWInput)\b", value):
                    raise RuntimeError(f"Former external input survives in mapped certificate type: {row['id']}: {name}")
                cited_type_found |= bool(re.search(r"\bIIDFiniteVarianceCLT\b", value))
        if cited_type_found != bool(inputs):
            raise RuntimeError(f"Audited certificate type disagrees with the cited-input ledger: {row['id']}")


def check_proof_idea_layout(original, draft, expected_rows):
    """Check reviewed proof removal and retained assertions, not proof semantics."""
    check_tex_groups(original, "reviewed original manuscript")
    check_tex_groups(draft, "annotated draft")
    original_proofs = active_proofs(original)
    original_active = uncomment_tex(original)
    lines = original.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    reviewed = set()
    for row in expected_rows:
        first, last = row.get("proof_start_line"), row.get("proof_end_line")
        if first is None and last is None:
            continue
        if not first or not last or not 1 <= first <= last <= len(lines):
            raise RuntimeError(f"Invalid reviewed proof range: {row['id']}")
        begin, end = offsets[first - 1], offsets[last]
        matches = [proof for proof in original_proofs if begin <= proof[0] and proof[1] <= end]
        if len(matches) != 1:
            raise RuntimeError(f"Reviewed proof range does not contain one active proof: {row['id']}")
        proof = matches[0]
        if (original_active[begin:proof[0]].strip()
                or original_active[proof[1]:end].strip() or proof in reviewed):
            raise RuntimeError(f"Reviewed proof range overlaps retained source or another proof: {row['id']}")
        reviewed.add(proof)
    if reviewed != set(original_proofs):
        raise RuntimeError("Some original active full proofs have no reviewed removal range")
    draft_proofs = active_proofs(draft)
    proved_count = sum(row["is_proved_assertion"] for row in expected_rows)
    cited_count = sum(bool(row.get("external_inputs")) for row in expected_rows)
    headings = [heading for _, _, heading in draft_proofs]
    if (len(headings) != proved_count
            or headings.count("Proof idea; fully Lean-verified") != proved_count - cited_count
            or headings.count("Proof idea; modulo the iid central limit theorem") != cited_count):
        raise RuntimeError("The active draft proof ideas must reflect each reviewed verification status")
    gauge = next((row for row in expected_rows if row["id"] == "ANT-SYMMETRIC-GAUGE-NORM"), None)
    if gauge is not None:
        match = re.search(r"The quantity .*?applied in both orders\)\.",
                          clean_companion_tex(original), re.S)
        if match is None:
            raise RuntimeError("The reviewed gauge assertion needs a new explicit retention rule")
        assertion = match.group()
        check_tex_groups(assertion, "retained gauge assertion")
        normalize = lambda text: re.sub(r"\s+", " ", text).strip()
        if normalize(uncomment_tex(draft)).count(normalize(assertion)) != 1:
            raise RuntimeError("The gauge norm/height-width assertion was dropped or duplicated with its enclosing proof")
    if any(row["id"] == "ANT-RANK-HAUSDORFF" for row in expected_rows):
        pattern = r"\\begin\{equation\}\s*\\label\{eq:rank-displacement\}.*?\\end\{equation\}"
        old_equations = re.findall(pattern, uncomment_tex(original), re.S)
        new_equations = re.findall(pattern, uncomment_tex(draft), re.S)
        if (len(old_equations) != 1 or len(new_equations) != 1
                or canonical_tex(old_equations[0]) != canonical_tex(new_equations[0])):
            raise RuntimeError("The rank-cloud remark requires the exact retained displacement equation")
        if re.search(r"D_n\s*=\s*\\max_k", uncomment_tex(draft)) is None:
            raise RuntimeError("The proof idea must define the retained rank displacement D_n")
    return len(original_proofs), len(draft_proofs)


def check_proof_correspondence(root, coverage, inventory, report, actual):
    """Bind reviewed method labels and complete readable alternatives to bytes.

    This checks provenance and completeness, not the semantic review judgments.
    """
    ledger = json.loads((root / "formalization/proof-correspondence.json").read_text(encoding="utf-8"))
    if ledger["source_sha256"] != coverage["source_sha256"]:
        raise RuntimeError("Proof-method correspondence describes a different manuscript")
    if (ledger["lean_source_sha256"] != report["source_sha256"]
            or ledger["configuration_sha256"] != report["configuration_sha256"]
            or ledger["audit_source_sha256"] != report["audit_source_sha256"]
            or ledger["retained_audit_checked_at"] != report["checked_at"]):
        raise RuntimeError("Proof-method correspondence is not bound to the audited Lean snapshot")
    all_rows = coverage["statements"] + coverage.get("additional_claims", [])
    proved = {row["id"]: row for row in all_rows if row["is_proved_assertion"]}
    entries = ledger["entries"]
    if len(entries) != len(proved) or {entry["id"] for entry in entries} != set(proved):
        raise RuntimeError("Missing or repeated proof-method comparisons")
    alternatives = {}
    readable_proofs = {}
    for entry in entries:
        sid = entry["id"]
        row = proved[sid]
        if entry["statement_match"] != "same" or entry["statement_sha256"] != row["statement_sha256"]:
            raise RuntimeError(f"A written statement is not the reviewed verified statement: {sid}")
        if (entry["certificate_declarations"] != row["lean_declarations"]
                or entry["certificate_type_sha256"] != row["verified_type_sha256"]):
            raise RuntimeError(f"A proof comparison changed its complete Lean certificates: {sid}")
        if row.get("proof_method") != entry["proof_method"]:
            raise RuntimeError(f"Paper and ledger disagree about proof method: {sid}")
        for name in entry["lean_declarations"]:
            if name not in actual:
                raise RuntimeError(f"Unaudited proof-method reference: {sid}: {name}")
        if entry["proof_method"] == "alternative_argument":
            label = entry.get("human_proof_label")
            if not label or label in alternatives:
                raise RuntimeError(f"Missing or repeated readable alternative: {sid}")
            alternatives[label] = entry["human_proof_file"]
        elif entry["proof_method"] not in {"same_argument", "expanded_argument", "no_separate_proof"}:
            raise RuntimeError(f"Unknown proof-method classification: {sid}")
        if entry.get("human_proof_label"):
            label = entry["human_proof_label"]
            if label in readable_proofs:
                raise RuntimeError(f"Repeated readable proof: {label}")
            readable_proofs[label] = entry["human_proof_file"]
    for filename, fingerprint in ledger["branch_review_files"].items():
        if sha(root / "formalization" / filename) != fingerprint:
            raise RuntimeError(f"Independent proof review changed: {filename}")
    seen_labels = set()
    full_proofs = 0
    for filename, fingerprint in ledger["human_proof_files"].items():
        source = root / "formalization" / filename
        if sha(source) != fingerprint:
            raise RuntimeError(f"Reviewed readable proof changed: {filename}")
        expected = clean_companion_tex(source.read_text(encoding="utf-8"))
        text = (root / "paper" / filename).read_text(encoding="utf-8")
        if text != expected:
            raise RuntimeError(f"The paper does not contain the complete reviewed proof: {filename}")
        check_tex_groups(text, filename)
        proofs = active_proofs(text)
        if any(heading != "Complete proof following the Lean argument" for _, _, heading in proofs):
            raise RuntimeError(f"An alternative is not presented as a complete proof: {filename}")
        labels = re.findall(r"\\label\{(leanproof:[^}]+)\}", text)
        if len(labels) != len(proofs):
            raise RuntimeError(f"A readable proof has no unique subsection label: {filename}")
        for label in labels:
            if label in seen_labels or readable_proofs.get(label) != filename:
                raise RuntimeError(f"Readable proof/ledger label mismatch: {label}")
            seen_labels.add(label)
        full_proofs += len(proofs)
    if seen_labels != set(readable_proofs) or not set(alternatives) <= seen_labels:
        raise RuntimeError("A reviewed readable proof is missing or untracked")
    for path in (root / "paper").rglob("*.tex"):
        if AUTHOR_TOKEN.search(path.read_text(encoding="utf-8")):
            raise RuntimeError(f"Editorial markup remains in the verification document: {path.name}")
    draft = (root / "paper/main.tex").read_text(encoding="utf-8")
    if draft.count("\\verificationcomparison{") != len(proved):
        raise RuntimeError("The paper does not distinguish statements and proof methods for every claim")
    for entry in entries:
        texts = {
            "same_argument": "Statement matches. The written proof and Lean use the same argument.",
            "expanded_argument": "Statement matches. Lean follows the written argument with additional formal details.",
            "no_separate_proof": "Statement matches. The draft gives no separate proof; the checked deduction is described below.",
            "alternative_argument": "Statement matches. Lean uses a different argument. Complete proof: Appendix~\\ref{" + (entry.get("human_proof_label") or "") + "}.",
        }
        badge = re.search(r"\\verificationstatus\{" + re.escape(entry["id"]) + r"\}\{[^}]*\}\s*"
                          r"\\verificationcomparison\{([^\n]*)\}", draft)
        if badge is None or badge[1] != texts[entry["proof_method"]]:
            raise RuntimeError(f"Visible proof-method note does not match its reviewed classification: {entry['id']}")
    if "\\input{verification-full-proofs}" not in draft:
        raise RuntimeError("The complete readable alternative proofs are not included in the document")
    return full_proofs


def main():
    manifest = json.loads((ROOT / "release/source-manifest.json").read_text(encoding="utf-8"))
    for path, expected in manifest["files"].items():
        if sha(ROOT / path) != expected:
            raise RuntimeError(f"Frozen source changed: {path}. Rebuild and review the release.")
    coverage = json.loads((ROOT / "formalization/coverage.json").read_text(encoding="utf-8"))
    if sha(ROOT / "source/main.tex") != coverage["source_sha256"]:
        raise RuntimeError("Reviewed manuscript fingerprint mismatch")
    report_path = ROOT / "logs/verification.json"
    fresh = report_path.exists()
    report = (json.loads(report_path.read_text(encoding="utf-8")) if fresh else
              read_evidence(ROOT / "release/verification.json"))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if report.get("status") != "passed" or set(report.get("allowed_axioms", [])) != allowed:
        raise RuntimeError("Audit evidence has not passed the stated logical policy")
    for declaration in report["declarations"]:
        if declaration["kind"] == "axiom" or declaration["unsafe"] or set(declaration["axioms"]) - allowed:
            raise RuntimeError(f"Unapproved audited declaration: {declaration['name']}")
        computed = hashlib.sha256(declaration["type_expression"].encode()).hexdigest()
        if declaration["type_sha256"] != computed:
            raise RuntimeError(f"Type expression fingerprint mismatch: {declaration['name']}")
    for path, expected in report["source_sha256"].items():
        if sha(ROOT / path) != expected:
            raise RuntimeError(f"Audit source mismatch: {path}")
    source_set = {p.relative_to(ROOT).as_posix() for p in (ROOT / "Antichain").rglob("*.lean")} | {"Antichain.lean"}
    if source_set != set(report["source_sha256"]):
        raise RuntimeError("Audit source set mismatch")
    if report.get("audit_source_sha256") and sha(ROOT / "scripts/axiom_audit.lean") != report["audit_source_sha256"]:
        raise RuntimeError("Audit collector source mismatch")
    configurations = report.get("configuration_sha256", {})
    if coverage.get("schema_version", 1) >= 2 and set(configurations) != {
            "lean-toolchain", "lakefile.lean", "lake-manifest.json", "verify.py"}:
        raise RuntimeError("Missing frozen dependency configuration or verifier")
    for path, expected in configurations.items():
        if sha(ROOT / path) != expected:
            raise RuntimeError(f"Audited configuration mismatch: {path}")
    actual = {r["name"]: r for r in report["declarations"]}
    check_frozen_types(ROOT / "release/statement-types.json", actual)
    draft = (ROOT / "paper/main.tex").read_text(encoding="utf-8")
    original = (ROOT / "source/main.tex").read_text(encoding="utf-8")
    inventory = json.loads((ROOT / "formalization/statement-inventory.json").read_text(encoding="utf-8"))
    evidence = inventory.get("verification_evidence", {})
    expected_evidence = dict(
        status="passed", checked_at=report["checked_at"],
        toolchain=report["toolchain"], mathlib_revision=report["mathlib_revision"],
        production_modules=len(report["source_sha256"]) - 1, root_module="Antichain",
        theorem_count=report["theorem_count"], declaration_count=report["declaration_count"],
        allowed_axioms=report["allowed_axioms"], source_sha256=coverage["source_sha256"],
        fully_verified_assertions=coverage["counts"]["fully_verified"],
        external_mathematical_inputs=coverage["counts"]["verified_modulo_cited"])
    if (inventory["source_sha256"] != coverage["source_sha256"]
            or any(evidence.get(key) != value for key, value in expected_evidence.items())):
        raise RuntimeError("Inventory retains stale kernel counts, source or audit provenance")
    rows = coverage["statements"] + coverage.get("additional_claims", [])
    expected_rows = inventory["statements"] + inventory.get("additional_claims", [])
    for row in expected_rows + rows:
        if row["is_proved_assertion"] and row.get("development_note") != audit_development_note(report):
            raise RuntimeError(f"Stale per-claim audit provenance: {row['id']}")
    if len(rows) != len(expected_rows) or {r["id"] for r in rows} != {r["id"] for r in expected_rows}:
        raise RuntimeError("Paper inventory and coverage disagree")
    if sum(r["is_proved_assertion"] for r in coverage["statements"]) != inventory["counts"]["proved_assertions"]:
        raise RuntimeError("Numbered assertion count mismatch")
    if coverage.get("schema_version", 1) >= 2:
        check_paper_receipt(ROOT / "paper")
        check_paper_numbering_snapshot(ROOT / "paper", inventory,
                                      ROOT / "formalization/compiled-numbering-review.json")
    originals = {r["id"]: r for r in expected_rows}
    check_complete_claims(rows, expected_rows, actual)
    for row in rows:
        if row["statement_sha256"] != originals[row["id"]]["statement_sha256"]:
            raise RuntimeError(f"Statement fingerprint changed: {row['id']}")
        if draft.count("\\verificationstatus{" + row["id"] + "}") != 1:
            raise RuntimeError(f"Missing or repeated status marker: {row['id']}")
        visible_status = {
            "fully_verified": "Fully Lean-verified",
            "verified_modulo_cited": "Lean-verified assuming the iid CLT",
            "cited_context": "Cited variational context (outside Lean scope)",
        }.get(row["lean_status"])
        if visible_status and (
                "\\verificationstatus{" + row["id"] + "}{" + visible_status + "}") not in draft:
            raise RuntimeError(f"Visible badge differs from reviewed status: {row['id']}")
        for name, expected in row.get("verified_type_sha256", {}).items():
            if name not in actual or actual[name]["type_sha256"] != expected:
                raise RuntimeError(f"Bad paper/declaration mapping: {row['id']}: {name}")
    # All original active theorem statements are preserved, even when a full proof
    # is replaced by a proof idea. Compare normalized raw environment text.
    pattern = r"\\begin\{(theorem|proposition|lemma|remark|question|conjecture|corollary)\}.*?\\end\{\1\}"
    def statements(text):
        return [canonical_tex(m.group()) for m in re.finditer(pattern, uncomment_tex(text), re.S)]
    if statements(original) != statements(draft):
        raise RuntimeError("An original assertion was changed")
    full = sum(r["lean_status"] == "fully_verified" for r in rows)
    if draft.count("\\begin{proof}[Proof idea; fully Lean-verified]") != full:
        raise RuntimeError("Proof-idea count differs from full status count")
    removed, sketches = check_proof_idea_layout(original, draft, expected_rows)
    readable_proofs = check_proof_correspondence(ROOT, coverage, inventory, report, actual)
    print(f"PASS: {len(rows)} statement mappings; {full} complete assertions without external inputs; "
          f"{coverage['counts']['verified_modulo_cited']} explicit cited-input certificates; "
          f"{removed} original proofs replaced by {sketches} proof ideas; frozen sources/types agree.")
    print(f"PASS: editorial markup removed; {sketches} proof-method labels; {readable_proofs} complete readable proofs.")
    print("These are deterministic release gates; independent mathematical correspondence review remains separate.")
    if not fresh:
        print("Checked saved audit evidence. Run python verify.py for a fresh Lean build.")


if __name__ == "__main__":
    main()
