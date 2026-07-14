#!/usr/bin/env python3
"""Fail closed on the public proof surface and frozen certificate contract."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "certificate" / "manifest.json"

EXPECTED_FILES = {
    ".gitignore",
    "LICENSE.md",
    "README.md",
    "certificate/admission.txt",
    "certificate/hashimoto.txt",
    "certificate/manifest.json",
    "certificate/roots/repeat_phase_roots_s0.bin",
    "certificate/roots/repeat_phase_roots_s1.bin",
    "kernel/repeat_interval_check.cu",
    "kernel/repeat_phase_probe.cu",
    "kernel/repeat_scalar_upper.cu",
    "kernel/skeleton_winding_kernel.cpp",
    "kernel/verify_repeat_phase_roots.py",
    "paper/Li_Erdos_1212_Minimal_Closure_2026.pdf",
    "paper/erdos1212_minimal_closure.tex",
    "paper/theorem-map.json",
    "scripts/build_paper.ps1",
    "scripts/verify_full_certificate.ps1",
    "scripts/verify_publication.py",
}


def fail(message: str) -> None:
    raise SystemExit(f"[publication:error] {message}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def visible_files() -> set[str]:
    ignored_parts = {".git", "build", "payload", "tmp", "__pycache__"}
    ignored_suffixes = {".aux", ".fdb_latexmk", ".fls", ".log", ".out", ".toc"}
    files: set[str] = set()
    for path in ROOT.rglob("*"):
        if not path.is_file() or any(part in ignored_parts for part in path.parts):
            continue
        if path.suffix in ignored_suffixes:
            continue
        files.add(path.relative_to(ROOT).as_posix())
    return files


def check_public_surface(manifest: dict) -> None:
    actual = visible_files()
    if actual != EXPECTED_FILES:
        fail(f"public surface drift: missing={sorted(EXPECTED_FILES-actual)}, extra={sorted(actual-EXPECTED_FILES)}")

    forbidden_paths = ["research", "audit", "chain-status", "data", "src", "publication"]
    for relative in forbidden_paths:
        if (ROOT / relative).exists():
            fail(f"internal or exploratory path is present: {relative}")

    for entry in manifest["repository_files"]:
        path = ROOT / entry["path"]
        if not path.is_file():
            fail(f"missing hash-pinned file: {entry['path']}")
        if path.stat().st_size != entry["bytes"]:
            fail(f"length drift: {entry['path']}")
        digest = sha256(path)
        if digest != entry["sha256"]:
            fail(f"hash drift: {entry['path']} {digest}")

    tex = (ROOT / "paper" / "erdos1212_minimal_closure.tex").read_text(encoding="utf-8")
    required = [
        r"\\label\{thm:fixed-contour-cancellation\}",
        r"\\label\{thm:certified-translation-kernel\}",
        r"\\label\{thm:large-repeat-tail\}",
        r"\\label\{thm:repeat-twelve-interval\}",
        r"\\label\{thm:erdos1212-close\}",
        r"0\.91717912709094451",
        r"0\.933\+0\.067=1",
    ]
    for pattern in required:
        if re.search(pattern, tex) is None:
            fail(f"required closure text missing: {pattern}")

    forbidden_text = {
        r"(?i)frontier": "frontier language",
        r"(?i)route-selection": "route-selection language",
        r"(?i)research/": "internal research path",
        r"(?i)chain-status": "internal chain-status path",
        r"(?i)ledger": "internal ledger language",
    }
    for pattern, description in forbidden_text.items():
        if re.search(pattern, tex):
            fail(f"{description} found in manuscript")

    public_documents = [
        ROOT / "README.md",
        ROOT / "certificate" / "admission.txt",
        ROOT / "certificate" / "hashimoto.txt",
        ROOT / "paper" / "erdos1212_minimal_closure.tex",
    ]
    for path in public_documents:
        text = path.read_text(encoding="utf-8")
        if re.search(r"(?i)(?:research/|chain-status|route-selection|frontier)", text):
            fail(f"private process language found in {path.relative_to(ROOT)}")

    theorem_map = json.loads((ROOT / "paper" / "theorem-map.json").read_text(encoding="utf-8"))
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    for item in theorem_map:
        if item["label"] not in labels:
            fail(f"theorem-map label absent: {item['label']}")
        for evidence in item["evidence"]:
            if evidence.startswith(("thm:", "lem:", "prop:")):
                if evidence not in labels:
                    fail(f"mapped proof dependency absent: {evidence}")
            elif not (ROOT / evidence).is_file():
                fail(f"mapped evidence absent: {evidence}")

    admission = (ROOT / "certificate" / "admission.txt").read_text(encoding="utf-8")
    exact_lines = [
        "states=55076704",
        "interval_ratio_max_ru=0.91717912709094451",
        "failures=0",
        "positive_over_zero=0",
        "negative_uppers=0",
        "nonfinite=0",
        "common_cone_interval=PASS",
        "R-REPEAT-12: EVIDENCE_CLOSED",
        "COMMON-CONE: CERTIFIED",
    ]
    for line in exact_lines:
        if line not in admission:
            fail(f"admission transcript missing: {line}")


def check_roots() -> None:
    verifier = ROOT / "kernel" / "verify_repeat_phase_roots.py"
    cases = [
        ("repeat_phase_roots_s0.bin", "13,17,19,23,29"),
        ("repeat_phase_roots_s1.bin", "31,37,41,43,47,53,59"),
    ]
    for name, primes in cases:
        command = [sys.executable, str(verifier), str(ROOT / "certificate" / "roots" / name), primes]
        result = subprocess.run(command, text=True, capture_output=True)
        if result.returncode or "root_component_error_lt_4u32=PASS" not in result.stdout:
            fail(f"exact root verification failed for {name}: {result.stdout}{result.stderr}")


def check_payload(manifest: dict, payload: Path) -> None:
    for entry in manifest["external_payload"]:
        path = payload / entry["name"]
        if not path.is_file():
            fail(f"missing payload: {entry['name']}")
        if path.stat().st_size != entry["bytes"]:
            fail(f"payload length drift: {entry['name']}")
        digest = sha256(path)
        if digest != entry["sha256"]:
            fail(f"payload hash drift: {entry['name']} {digest}")
    print(f"[payload:ok] files={len(manifest['external_payload'])}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--payload", type=Path)
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    check_public_surface(manifest)
    check_roots()
    if args.payload is not None:
        check_payload(manifest, args.payload.resolve())
    print("[publication:ok] surface=19 roots=824 closure=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
