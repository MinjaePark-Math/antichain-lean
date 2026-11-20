"""Compile all source modules and audit every declaration's transitive axioms.

Normal use: python verify.py
Read-only shared dependency cache: python verify.py --dependency-root PATH
The latter uses the pinned Lean compiler directly; it never runs Lake inside
the supplied cache. No cached Antichain object is accepted without recompiling.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, as_completed, wait
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "logs"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PIN = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_tokens(source: str) -> str:
    """Remove nested Lean comments and string literals before the extra lexical guard."""
    output = []
    index = depth = 0
    quoted = False
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
        elif quoted:
            if source[index] == "\\":
                index += 2
            elif source[index] == '"':
                quoted = False
                index += 1
            else:
                index += 1
        elif pair == "/-":
            depth = 1
            output.append(" ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            index = len(source) if end < 0 else end
            output.append(" ")
        elif source[index] == '"':
            quoted = True
            output.append(" ")
            index += 1
        else:
            output.append(source[index])
            index += 1
    return "".join(output)


def run(cmd: list[str], name: str, env=None, *, capture=True) -> str:
    # Complete structural types can be very large. Stream the unabridged
    # compiler evidence to disk instead of duplicating it in subprocess pipes.
    path = LOGS / name
    with path.open("w", encoding="utf-8", newline="\n") as output:
        p = subprocess.run(cmd, cwd=ROOT, env=env, text=True, encoding="utf-8",
                           errors="replace", stdout=output, stderr=subprocess.STDOUT)
    if p.returncode:
        with path.open("rb") as source:
            source.seek(max(0, path.stat().st_size - 12000))
            tail = source.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"{name} failed ({p.returncode}):\n{tail}")
    with path.open(encoding="utf-8") as source:
        for line in source:
            if re.search(r"^[^\n]*:\d+:\d+: (?:error:|warning: declaration uses 'sorry')", line):
                raise RuntimeError(f"Compiler reported an invalid proof; see {name}")
    return path.read_text(encoding="utf-8") if capture else ""


def compile_project(modules, compiler, env, source_hashes, deferred, jobs):
    """Recompile all sources, starting a module only after its local imports finish."""
    pending = {
        name: set(re.findall(r"^import (Antichain(?:\.\S+)?)", path.read_text(encoding="utf-8"), re.M))
        for name, path in modules.items()
    }
    ordinary = set(modules) - deferred - {"Antichain"}
    done = set()

    def compile_module(module):
        path = modules[module]
        out = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        source = path.read_bytes()
        if re.search(r"\b(?:sorry|admit|axiom|native_decide|implemented_by|unsafe)\b",
                     code_tokens(source.decode("utf-8"))):
            raise RuntimeError(f"Disallowed proof escape in {path.name}")
        compiled_hash = hashlib.sha256(source).hexdigest()
        print(f"Compiling {module}", flush=True)
        run(compiler + ["-o", str(out), str(path)], f"build-{module}.log", env, capture=False)
        if digest(path) != compiled_hash:
            raise RuntimeError(f"Source changed while compiling {module}; rerun verification")
        return path.relative_to(ROOT).as_posix(), compiled_hash

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        active = {}
        while pending or active:
            ready = [name for name, imports in pending.items() if imports <= done
                     and (name not in deferred or ordinary <= done)]
            for name in ready[: jobs - len(active)]:
                active[pool.submit(compile_module, name)] = name
                del pending[name]
            if not active:
                raise RuntimeError("Circular or missing local import")
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in finished:
                path, fingerprint = future.result()
                source_hashes[path] = fingerprint
                done.add(active.pop(future))


def read_audit_shard(path: Path):
    """Read every full declaration payload and the collector's completion count."""
    rows, summaries = [], []
    with path.open(encoding="utf-8") as evidence:
        for line in evidence:
            if "AUDIT_JSON " in line:
                rows.append(json.loads(line.split("AUDIT_JSON ", 1)[1]))
            elif "AUDIT_SUMMARY " in line:
                summaries.append(json.loads(line.split("AUDIT_SUMMARY ", 1)[1]))
    if len(summaries) != 1:
        raise RuntimeError(f"Missing or repeated audit completion summary: {path.name}")
    return rows, summaries[0]


def merge_audit_shards(shards, jobs):
    """Require a disjoint, complete union of the actual module-defined inventory."""
    if len(shards) != jobs:
        raise RuntimeError("Missing audit worker results")
    indices, totals, rows, summaries = set(), set(), [], []
    for worker_rows, summary in shards:
        keys = ("shard_index", "shard_count", "total_project_declarations", "selected_declarations")
        if any(type(summary.get(key)) is not int for key in keys):
            raise RuntimeError("Invalid audit shard counts")
        index, count, total, selected = (summary[key] for key in keys)
        if count != jobs or not 0 <= index < jobs or index in indices:
            raise RuntimeError("Incorrect or duplicate audit shard index")
        if total <= 0 or not 0 <= selected <= total or selected != len(worker_rows):
            raise RuntimeError("Audit shard declaration count mismatch")
        indices.add(index)
        totals.add(total)
        rows.extend(worker_rows)
        summaries.append(summary)
    if indices != set(range(jobs)) or len(totals) != 1:
        raise RuntimeError("Audit workers disagree on the project inventory")
    expected = next(iter(totals))
    if len(rows) != expected or len({row["name"] for row in rows}) != expected:
        raise RuntimeError("Incomplete or overlapping declaration audit")
    return sorted(rows, key=lambda row: row["name"]), sorted(summaries, key=lambda s: s["shard_index"])


def audit_project(compiler, env, jobs):
    """Run independent exact collectors; no dependency or axiom results are approximated."""
    def worker(index):
        worker_env = env.copy()
        worker_env["ANTICHAIN_AUDIT_SHARD_COUNT"] = str(jobs)
        worker_env["ANTICHAIN_AUDIT_SHARD_INDEX"] = str(index)
        log_name = f"axioms-and-types-shard-{index + 1}-of-{jobs}.log"
        run(compiler + [str(ROOT / "scripts/axiom_audit.lean")], log_name, worker_env, capture=False)
        result = read_audit_shard(LOGS / log_name)
        if result[1].get("shard_index") != index or result[1].get("shard_count") != jobs:
            raise RuntimeError(f"Audit worker returned the wrong shard: {log_name}")
        print(f"Completed audit shard {index + 1}/{jobs}", flush=True)
        return result

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = [pool.submit(worker, index) for index in range(jobs)]
        shards = [future.result() for future in as_completed(futures)]
    return merge_audit_shards(shards, jobs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--audit-jobs", type=int, choices=range(1, 9), default=2,
                        help="Independent exact audit shards (default: 2; use 1 for lower memory)")
    parser.add_argument("--build-jobs", type=int, choices=range(1, 13), default=1,
                        help="Maximum independent Lean compilation workers (default: 1)")
    parser.add_argument("--compile-last", action="append", default=[], metavar="MODULE",
                        help="Defer a leaf module until other source modules compile")
    parser.add_argument("--lake", default=shutil.which("lake") or str(
        Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")))
    args = parser.parse_args()
    LOGS.mkdir(exist_ok=True)
    (LOGS / "verification.json").unlink(missing_ok=True)
    snapshot_names = ("lean-toolchain", "lakefile.lean", "lake-manifest.json", "verify.py")
    configuration_hashes = {name: digest(ROOT / name) for name in snapshot_names}
    pin = (ROOT / "lean-toolchain").read_text().strip()
    if pin != "leanprover/lean4:v4.24.0":
        raise RuntimeError("Unexpected Lean toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != PIN:
        raise RuntimeError("Unexpected Mathlib revision")
    if PIN not in (ROOT / "lakefile.lean").read_text(encoding="utf-8"):
        raise RuntimeError("Lake configuration does not declare the pinned Mathlib revision")
    sources = sorted(ROOT.glob("Antichain/**/*.lean")) + [ROOT / "Antichain.lean"]
    # Each compiled module and the final audit must describe the same source.
    # Direct compilation records each hash immediately before compiling it,
    # allowing an independent branch to finish before it is first built.
    source_hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sources}
    audit_source_hash = digest(ROOT / "scripts/axiom_audit.lean")
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in sources}
    expected = set(modules) - {"Antichain"}
    imported = set(re.findall(r"^import (Antichain\.\S+)",
                             (ROOT / "Antichain.lean").read_text(encoding="utf-8"), re.M))
    if expected != imported:
        raise RuntimeError(f"Root imports incomplete: {expected ^ imported}")
    deferred = set(args.compile_last)
    if not deferred <= expected:
        raise RuntimeError("Unknown deferred module")
    for module, path in modules.items():
        if module not in deferred | {"Antichain"}:
            imports = set(re.findall(r"^import (Antichain(?:\.\S+)?)", path.read_text(encoding="utf-8"), re.M))
            if imports & deferred:
                raise RuntimeError("A deferred module must be a leaf of the project import graph")
    for p in sources:
        # Conservative source check complements, and does not replace, axiom inspection.
        if re.search(r"\b(?:sorry|admit|axiom|native_decide|implemented_by|unsafe)\b",
                     code_tokens(p.read_text(encoding="utf-8"))):
            raise RuntimeError(f"Disallowed proof escape in {p.name}")
    env = os.environ.copy()
    env["GIT_OPTIONAL_LOCKS"] = "0"
    dependency_revisions = {}
    if args.dependency_root:
        dep = args.dependency_root.resolve()
        for package in manifest["packages"]:
            directory = dep / package["name"]
            result = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                                    text=True, capture_output=True, encoding="utf-8")
            if result.returncode or result.stdout.strip() != package["rev"]:
                raise RuntimeError(f"Dependency pin mismatch: {package['name']}")
            # Read-only review of tracked source status; cached build outputs are untracked.
            result = subprocess.run(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
                                    text=True, capture_output=True, encoding="utf-8")
            if result.returncode or result.stdout.strip():
                raise RuntimeError(f"Tracked dependency source modified: {package['name']}")
            dependency_revisions[package["name"]] = package["rev"]
        lean = args.lean or Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.24.0" / "bin" / ("lean.exe" if os.name == "nt" else "lean")
        paths = [ROOT / ".lake/build/lib/lean", ROOT]
        paths += [dep / p["name"] / ".lake/build/lib/lean" for p in manifest["packages"]]
        env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
        compiler = [str(lean)]
        version = run(compiler + ["--version"], "toolchain.log", env)
    else:
        version = run([args.lake, "env", "lean", "--version"], "toolchain.log", env)
        run([args.lake, "build"], "build.log", env)
        compiler = [args.lake, "env", "lean"]
        for package in manifest["packages"]:
            directory = ROOT / ".lake/packages" / package["name"]
            result = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                                    text=True, capture_output=True, encoding="utf-8", env=env)
            if result.returncode or result.stdout.strip() != package["rev"]:
                raise RuntimeError(f"Dependency pin mismatch: {package['name']}")
            result = subprocess.run(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
                                    text=True, capture_output=True, encoding="utf-8", env=env)
            if result.returncode or result.stdout.strip():
                raise RuntimeError(f"Tracked dependency source modified: {package['name']}")
            dependency_revisions[package["name"]] = package["rev"]
    if "version 4.24.0" not in version or "797c613eb9b6d4ec95db23e3e00af9ac6657f24b" not in version:
        raise RuntimeError("Compiler version/commit mismatch")
    compile_project(modules, compiler, env, source_hashes, deferred, args.build_jobs)
    print(f"Auditing all declaration types and transitive axioms in {args.audit_jobs} exact shard(s)", flush=True)
    rows, audit_summaries = audit_project(compiler, env, args.audit_jobs)
    for row in rows:
        if row["kind"] == "axiom" or row["unsafe"] or set(row["axioms"]) - ALLOWED:
            raise RuntimeError(f"Unapproved declaration: {row['name']}")
        row["type_sha256"] = hashlib.sha256(row["type_expression"].encode()).hexdigest()
    if set(modules) - {r["module"] for r in rows} - {"Antichain"}:
        raise RuntimeError("Some project modules were not audited")
    final_sources = sorted(ROOT.glob("Antichain/**/*.lean")) + [ROOT / "Antichain.lean"]
    if ({p.relative_to(ROOT).as_posix(): digest(p) for p in final_sources} != source_hashes
            or digest(ROOT / "scripts/axiom_audit.lean") != audit_source_hash
            or {name: digest(ROOT / name) for name in snapshot_names} != configuration_hashes):
        raise RuntimeError("Project sources changed during verification; rerun on the finished snapshot")
    report = dict(schema_version=1, status="passed", checked_at=datetime.now(timezone.utc).isoformat(),
                  toolchain=pin, mathlib_revision=PIN, compiler=version.strip(),
                  build_mode="direct_pinned_compiler_read_only_dependencies" if args.dependency_root else "lake_with_fresh_module_compilation",
                  dependency_revisions=dependency_revisions,
                  theorem_count=sum(r["kind"] == "theorem" for r in rows),
                  declaration_count=len(rows), allowed_axioms=sorted(ALLOWED),
                  audit_jobs=args.audit_jobs, audit_shards=audit_summaries,
                  source_sha256=source_hashes, declarations=rows,
                  configuration_sha256=configuration_hashes,
                  audit_source_sha256=audit_source_hash,
                  scope="Kernel checks of every project declaration, with complete types and transitive axioms. Manuscript correspondence and explicit cited-input conditions are reviewed separately in the coverage ledger.")
    with (LOGS / "verification.json").open("w", encoding="utf-8", newline="\n") as output:
        json.dump(report, output, indent=2, ensure_ascii=False)
        output.write("\n")
    print(f"PASS: {report['theorem_count']} theorems; {len(rows)} declarations; types and transitive axioms audited.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as exc:
        sys.exit(str(exc))
