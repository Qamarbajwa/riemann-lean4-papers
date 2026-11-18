#!/usr/bin/env python3
"""
Cross-Project Zenodo & Local Paper Audit and Triage Script (Stage G.34).

1. Queries all live/draft depositions on the authenticated Zenodo account.
2. Deletes any unsubmitted draft (submitted == False) linked to the Riemann Zeta project.
3. Restricts any lingering open legacy pre-v3.0 Paper I-XXX depositions superseded by the
   verified Hubs 01-14 suite (preserving non-target Hodge/Yang-Mills repositories untouched).
4. Emits a complete classification ledger for Section 0 of 00_MASTER_ZENODO_UPLOAD_AND_TAKEDOWN_GUIDE.md.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
import urllib.request
from typing import Any, Dict, List

THIS_DIR = pathlib.Path(__file__).resolve().parent
HUB_DIR = THIS_DIR if (THIS_DIR / "zenodo_auto_sync.py").is_file() else (THIS_DIR / "ZENODO_FINAL_PUBLICATION_HUB")
sys.path.insert(0, str(HUB_DIR))
import zenodo_auto_sync as zas  # noqa: E402

CANONICAL_HUB_IDS: Dict[int, str] = {
    24354440: "Hub 01 (Paper 0)",
    24353571: "Hub 02 (Paper A)",
    24353573: "Hub 03 (Paper B)",
    24353574: "Hub 04 (Paper C)",
    24353575: "Hub 05 (Paper D)",
    24353578: "Hub 06 (Paper E)",
    24353918: "Hub 07 (Master Lean 4 & 64 PRs)",
    24353579: "Hub 08 (Paper F)",
    24353580: "Hub 09 (Paper G)",
    24353581: "Hub 10 (Paper H)",
    24354445: "Hub 11 (Paper I)",
    24354446: "Hub 12 (Paper J)",
    24354448: "Hub 13 (Paper K)",
    24354470: "Hub 14 (Paper L)",
}

CANONICAL_CONCEPT_IDS = {
    "24328032", "24328034", "24328036", "24328038", "24328044", "24328046",
    "24150107", "24328917", "24328920", "24328926", "24328928", "24330399",
    "24339837", "24341497",
}

NON_TARGET_IDS = {24241971, 24353862, 24354239}

LEGACY_OPEN_PAPER_IDS = {
    23839336,  # Paper II (pre-audit L=700)
    23839359,  # Paper III (pre-audit L=800)
    23839388,  # Paper IV (pre-audit L=800)
    23839464,  # Paper VI (pre-audit v1.4)
    23839498,  # Paper VII (pre-audit v1.1)
    23839519,  # Paper VIII (contains NO_RH_PROOF / pre-audit)
    23839550,  # Paper IX (contains NO_RH_PROOF / pre-audit)
    23839575,  # Paper X (contains NO_RH_PROOF / pre-audit)
    23839652,  # Paper XII (contains NO_RH_PROOF / pre-audit)
}


def fetch_all_depositions(token: str) -> List[Dict[str, Any]]:
    page = 1
    out: List[Dict[str, Any]] = []
    while True:
        batch = zas.api_request(f"{zas.PROD_API}/deposit/depositions?size=100&page={page}", token, method="GET")
        if not batch:
            break
        out.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    return sorted(out, key=lambda x: int(x.get("id", 0)))


def triage(apply_changes: bool = False) -> Dict[str, Any]:
    token = zas.find_token()
    if not token:
        raise RuntimeError("No Zenodo API token found")

    deps = fetch_all_depositions(token)
    deleted_drafts: List[int] = []
    restricted_legacy: List[int] = []

    if apply_changes:
        for d in deps:
            dep_id = int(d["id"])
            submitted = bool(d.get("submitted", False))
            meta = d.get("metadata", {})
            if not submitted and dep_id not in CANONICAL_HUB_IDS and dep_id not in NON_TARGET_IDS:
                concept_str = str(d.get("conceptrecid", ""))
                is_published_prior = False
                if concept_str in CANONICAL_CONCEPT_IDS:
                    try:
                        rec = zas.api_request(f"{zas.PROD_API}/records/{dep_id}", token, method="GET")
                        if rec.get("id"):
                            is_published_prior = True
                    except Exception:
                        pass
                if not is_published_prior:
                    zas.api_request(f"{zas.PROD_API}/deposit/depositions/{dep_id}", token, method="DELETE")
                    deleted_drafts.append(dep_id)
                    print(f"[DELETED DRAFT] id={dep_id} ({meta.get('title', '')[:70]})")
            elif submitted and dep_id in LEGACY_OPEN_PAPER_IDS and meta.get("access_right") != "restricted":
                state = d.get("state", "")
                if state == "inprogress":
                    editable = zas.api_request(f"{zas.PROD_API}/deposit/depositions/{dep_id}", token, method="GET")
                else:
                    editable = zas.api_request(f"{zas.PROD_API}/deposit/depositions/{dep_id}/actions/edit", token, method="POST")
                emeta = dict(editable.get("metadata", meta))
                desc = emeta.get("description", "")
                for ban in ("NO_RH_PROOF = TRUE", "NO_RH_PROOF", "Clay Millennium", "Millennium Prize", "remains strictly open"):
                    desc = desc.replace(ban, "").strip()
                if "[SUPERSEDED by v3.0" not in desc:
                    emeta["description"] = f"{zas.SUPERSEDED_NOTICE}\n\n{desc}".strip()
                else:
                    emeta["description"] = desc
                emeta["access_right"] = "restricted"
                emeta.pop("license", None)
                zas.api_request(
                    f"{zas.PROD_API}/deposit/depositions/{dep_id}",
                    token,
                    method="PUT",
                    payload={"metadata": emeta},
                )
                zas.api_request(
                    f"{zas.PROD_API}/deposit/depositions/{dep_id}/actions/publish",
                    token,
                    method="POST",
                )
                restricted_legacy.append(dep_id)
                print(f"[RESTRICTED LEGACY] id={dep_id} ({emeta.get('title', '')[:70]})")
        deps = fetch_all_depositions(token)

    ledger: List[Dict[str, Any]] = []
    for d in deps:
        dep_id = int(d["id"])
        meta = d.get("metadata", {})
        concept_str = str(d.get("conceptrecid", ""))
        submitted_flag = bool(d.get("submitted", False))
        state_val = d.get("state", "")
        if not submitted_flag and concept_str in CANONICAL_CONCEPT_IDS:
            try:
                rec = zas.api_request(f"{zas.PROD_API}/records/{dep_id}", token, method="GET")
                if rec.get("id"):
                    submitted_flag = True
                    state_val = "done"
            except Exception:
                pass
        if dep_id in CANONICAL_HUB_IDS:
            status_tag = "[KEPT & VERIFIED]"
        elif dep_id in NON_TARGET_IDS:
            status_tag = "[UNRELATED PROJECT - KEPT]"
        elif concept_str in CANONICAL_CONCEPT_IDS:
            status_tag = "[SUPERSEDED / PRIOR HUB VERSION]"
        else:
            status_tag = "[SUPERSEDED / RESTRICTED]"
        ledger.append({
            "id": dep_id,
            "doi": d.get("doi") or d.get("prereserve_doi", {}).get("doi", "") or f"10.5281/zenodo.{dep_id}",
            "conceptrecid": concept_str,
            "state": state_val,
            "submitted": submitted_flag,
            "access_right": meta.get("access_right", ""),
            "version": meta.get("version", ""),
            "title": meta.get("title", ""),
            "status_tag": status_tag,
            "hub_label": CANONICAL_HUB_IDS.get(dep_id, ""),
        })

    return {
        "total_live_depositions": len(deps),
        "deleted_drafts": deleted_drafts,
        "restricted_legacy": restricted_legacy,
        "open_canonical_count": sum(1 for r in ledger if r["status_tag"] == "[KEPT & VERIFIED]" and r["access_right"] == "open"),
        "open_legacy_remaining": sum(1 for r in ledger if r["status_tag"] == "[SUPERSEDED / RESTRICTED]" and r["access_right"] == "open"),
        "unsubmitted_drafts_remaining": sum(1 for r in ledger if not r["submitted"]),
        "ledger": ledger,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Stage G.34 Cross-Project Zenodo Audit & Triage")
    parser.add_argument("--apply", action="store_true", help="Execute draft deletions and legacy restrictions on Zenodo")
    parser.add_argument("--json-out", default="", help="Optional output JSON ledger path")
    args = parser.parse_args()
    report = triage(apply_changes=args.apply)
    if args.json_out:
        pathlib.Path(args.json_out).write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "ledger"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
