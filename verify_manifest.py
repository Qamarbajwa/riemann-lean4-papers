#!/usr/bin/env python3
"""
Single-source-of-truth manifest generator and integrity verifier for the
14-Hub Riemann Zeta Blueprint suite and 64 modular Lean 4 Mathlib4 PR units.

Usage:
  python verify_manifest.py --generate   # Regenerate manifest.json from ZENODO_FINAL_PUBLICATION_HUB
  python verify_manifest.py              # Verify manifest.json, SHA256SUMS.txt, and 64 PR staging files
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from typing import Any, Dict, List


ROOT = pathlib.Path(__file__).resolve().parent


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generate_manifest() -> Dict[str, Any]:
    hub_root = ROOT / "ZENODO_FINAL_PUBLICATION_HUB"
    if not hub_root.is_dir():
        raise RuntimeError(f"ZENODO_FINAL_PUBLICATION_HUB not found under {ROOT}")

    hubs: List[Dict[str, Any]] = []
    for meta_path in sorted(hub_root.glob("*/ZENODO_COPY_PASTE_METADATA.txt")):
        folder = meta_path.parent
        txt = meta_path.read_text(encoding="utf-8")
        hub_num = folder.name.split("_", 1)[0]
        title = re.search(r"Title\s*:\s*(.+)", txt).group(1).strip()
        version = re.search(r"Version\s*:\s*(v[0-9.]+)", txt).group(1).strip()
        doi = re.search(r"Version DOI\s*:\s*(10\.5281/zenodo\.\d+)", txt).group(1).strip()

        pdf_files = sorted(folder.glob("*.pdf"))
        zip_files = sorted(folder.glob("*.zip"))
        entry: Dict[str, Any] = {
            "hub": hub_num,
            "folder": folder.name,
            "title": title,
            "version": version,
            "doi": doi,
            "pdf": {
                "filename": pdf_files[0].name,
                "sha256": sha256_file(pdf_files[0]),
            } if pdf_files else None,
            "zip": {
                "filename": zip_files[0].name,
                "sha256": sha256_file(zip_files[0]),
            } if zip_files else None,
        }
        hubs.append(entry)

    mod_dir = ROOT / "RiemannBlueprint" / "RiemannBlueprint" / "Modules"
    mod_files = sorted(f.name for f in mod_dir.glob("*.lean"))
    return {
        "schema_version": "1.0",
        "lean_toolchain": "leanprover/lean4:v4.35.0",
        "modular_units_count": len(mod_files),
        "canonical_hubs_count": len(hubs),
        "hubs": hubs,
        "lean_modules": mod_files,
    }


TEXT_EXTS = {".tex", ".bib", ".bbl", ".md", ".py", ".json", ".lean", ".txt", ".csv"}


def verify_sha256sums(sums_file: pathlib.Path) -> int:
    checked = 0
    for line in sums_file.read_text(encoding="utf-8-sig").splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) < 2:
            continue
        expected, fname = parts[0], parts[1]
        target = sums_file.parent / fname
        if not target.is_file():
            raise AssertionError(f"Missing file listed in {sums_file}: {fname}")
        raw = target.read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        if actual != expected and target.suffix.lower() in TEXT_EXTS:
            lf_hash = hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest()
            crlf_hash = hashlib.sha256(raw.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")).hexdigest()
            if expected in (lf_hash, crlf_hash):
                actual = expected
        if actual != expected:
            raise AssertionError(f"SHA-256 mismatch for {target}: expected {expected}, got {actual}")
        checked += 1
    return checked


def verify_manifest() -> None:
    manifest_path = ROOT / "manifest.json"
    if not manifest_path.is_file():
        raise AssertionError(f"Missing {manifest_path}")
    data = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert data["canonical_hubs_count"] == 14, f"Expected 14 hubs, got {data['canonical_hubs_count']}"
    assert data["modular_units_count"] == 64, f"Expected 64 modules, got {data['modular_units_count']}"
    assert len(data["hubs"]) == 14
    mod_list = data.get("lean_modules", [])
    assert len(mod_list) == 64

    # Check standalone Modules/ directory when running inside the root workspace
    modules_dir = ROOT / "RiemannBlueprint" / "RiemannBlueprint" / "Modules"
    if modules_dir.is_dir():
        for mod in mod_list:
            assert (modules_dir / mod).is_file(), f"Missing Lean module: {modules_dir / mod}"
    assert not (ROOT / "05_mathlib4_pr_staging").exists(), "05_mathlib4_pr_staging must be removed"
    for forbidden in ("push_carved_prs_to_mathlib4.py", "manage_mathlib4_pr_queue.py", "ZULIP_PR_REVIEW_MESSAGES.md", "PR_SUBMISSION_GUIDE.md"):
        assert not (ROOT / "MATHLIB4_PR_STAGING" / forbidden).exists(), f"Forbidden PR automation file still exists: {forbidden}"

    # Verify PDF SHA-256 parity across all present mirrors
    pdf_checks = 0
    for hub in data["hubs"]:
        pdf_info = hub.get("pdf")
        if not pdf_info:
            continue
        fname, expected_sha = pdf_info["filename"], pdf_info["sha256"]
        for cand in ROOT.rglob(fname):
            if ".git" in cand.parts or "ZENODO_RELEASE_" in str(cand):
                continue
            actual = sha256_file(cand)
            assert actual == expected_sha, f"PDF SHA-256 mismatch at {cand}: {actual} != {expected_sha}"
            pdf_checks += 1

    # Verify any SHA256SUMS.txt manifests inside Paper I / Paper L packages
    sums_checks = 0
    for sums_file in sorted(ROOT.rglob("SHA256SUMS.txt")):
        if ".git" in sums_file.parts or "ZENODO_RELEASE_" in str(sums_file) or "JAR_SUBMISSION_PACKAGE" in sums_file.parts:
            continue
        sums_checks += verify_sha256sums(sums_file)

    print(
        f"MANIFEST OK: hubs={data['canonical_hubs_count']}, "
        f"lean_modules={data['modular_units_count']}, "
        f"pdf_mirrors_verified={pdf_checks}, sha256sums_entries_verified={sums_checks}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate or verify manifest.json")
    parser.add_argument("--generate", action="store_true", help="Generate manifest.json from Hub metadata")
    args = parser.parse_args()
    if args.generate:
        data = generate_manifest()
        out = ROOT / "manifest.json"
        out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        print(f"Generated {out} ({data['canonical_hubs_count']} hubs, {data['modular_units_count']} Lean modules)")
    verify_manifest()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
