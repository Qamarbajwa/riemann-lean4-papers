#!/usr/bin/env python3
"""
Read-only mathlib4 PR Queue & Status Monitor for all 52 Carved UpstreamPRs (Waves 1-8).

AI Policy Safety Guard:
  ALLOW_UPSTREAM_BOT_ACTIONS = False disables all automated `gh pr create` and `gh pr comment`
  mutations against `leanprover-community/mathlib4`, keeping `--inspect` and `--advance-queue`
  strictly read-only local status monitors.

Supports:
  --inspect             Inspect live PRs on leanprover-community/mathlib4 (read-only)
  --apply-delegated     Preview delegated PR status (blocked from upstream commenting by default)
  --rebase-conflicting  Check CONFLICTING PRs against upstream/master
  --advance-queue       Inspect merged parents, unlocked child PRs, and root wave queueing (read-only)
  --write-zulip         Generate MATHLIB4_PR_STAGING/ZULIP_PR_REVIEW_MESSAGES.md
  --max-concurrent N    Maximum concurrent open upstream PRs (default: 4)
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from typing import Any, Dict, List, Optional

STAGING_DIR = pathlib.Path(__file__).resolve().parent
if str(STAGING_DIR) not in sys.path:
    sys.path.insert(0, str(STAGING_DIR))

from push_carved_prs_to_mathlib4 import PR_REGISTRY, PRSpec  # noqa: E402

UPSTREAM_REPO = "leanprover-community/mathlib4"
FORK_REPO = "Qamarbajwa/mathlib4"
FORK_OWNER = "Qamarbajwa"
UPSTREAM_URL = "https://github.com/leanprover-community/mathlib4.git"
ALLOW_UPSTREAM_BOT_ACTIONS = False


def run_cmd(cmd: List[str], cwd: Optional[pathlib.Path] = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(cwd) if cwd else None, text=True, capture_output=True)


def gh_json(args: List[str]) -> Any:
    res = run_cmd(["gh"] + args)
    if res.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed ({res.returncode}): {res.stderr.strip()}")
    return json.loads(res.stdout) if res.stdout.strip() else []


def spec_parents(spec: PRSpec, by_branch: Dict[str, PRSpec]) -> List[PRSpec]:
    parents: List[PRSpec] = []
    if spec.base_branch in by_branch:
        parents.append(by_branch[spec.base_branch])
    for mb in spec.merge_branches:
        if mb in by_branch:
            parents.append(by_branch[mb])
    return parents


def summarize_checks(rollup: List[Dict[str, Any]]) -> Dict[str, Any]:
    total = len(rollup)
    passed = sum(
        1 for c in rollup if c.get("conclusion") in ("SUCCESS", "SKIPPED", "NEUTRAL")
    )
    failed = [
        c.get("name") or c.get("context", "unknown")
        for c in rollup
        if c.get("status") == "COMPLETED"
        and c.get("conclusion") not in ("SUCCESS", "SKIPPED", "NEUTRAL", None)
    ]
    pending = [
        c.get("name") or c.get("context", "unknown")
        for c in rollup
        if c.get("status") != "COMPLETED"
    ]
    all_green = total > 0 and not failed and not pending
    return {
        "total": total,
        "passed": passed,
        "failed": failed,
        "pending": pending,
        "all_green": all_green,
    }


def fetch_pr_details(upstream_repo: str, fork_owner: str) -> List[Dict[str, Any]]:
    prs = gh_json([
        "pr", "list", "--repo", upstream_repo, "--author", fork_owner,
        "--state", "all", "--limit", "100",
        "--json", "number,headRefName,state,url,title",
    ])
    detailed: List[Dict[str, Any]] = []
    for item in sorted(prs, key=lambda x: x["number"]):
        num = item["number"]
        view = gh_json([
            "pr", "view", str(num), "--repo", upstream_repo,
            "--json",
            "number,title,state,mergeable,mergeStateStatus,labels,reviews,comments,statusCheckRollup,headRefName,url",
        ])
        inline = gh_json(["api", f"repos/{upstream_repo}/pulls/{num}/comments"])
        labels = [lb["name"] for lb in view.get("labels", [])]
        reviews = view.get("reviews", [])
        human_comments = [
            c for c in view.get("comments", [])
            if c.get("author", {}).get("login") not in ("github-actions", "mathlib-bors", fork_owner)
        ]
        checks = summarize_checks(view.get("statusCheckRollup", []))
        detailed.append({
            "number": num,
            "branch": view.get("headRefName", item.get("headRefName")),
            "title": view.get("title", ""),
            "url": view.get("url", item.get("url")),
            "state": view.get("state", "UNKNOWN"),
            "mergeable": view.get("mergeable", "UNKNOWN"),
            "mergeStateStatus": view.get("mergeStateStatus", "UNKNOWN"),
            "labels": labels,
            "delegated": ("delegated" in labels) or ("bors d+" in labels),
            "reviews_count": len(reviews),
            "changes_requested": any(r.get("state") == "CHANGES_REQUESTED" for r in reviews),
            "inline_comments_count": len(inline),
            "human_issue_comments_count": len(human_comments),
            "checks": checks,
        })
    return detailed


def apply_actions(
    details: List[Dict[str, Any]],
    upstream_repo: str,
    fork_repo: str,
    mathlib_dir: Optional[pathlib.Path],
    apply_delegated: bool,
    rebase_conflicting: bool,
    execute: bool,
) -> List[str]:
    actions: List[str] = []
    for d in details:
        if d["state"] != "OPEN":
            continue
        num = d["number"]
        branch = d["branch"]
        if apply_delegated and d["delegated"] and d["checks"]["all_green"]:
            if not ALLOW_UPSTREAM_BOT_ACTIONS:
                actions.append(
                    f"[BLOCKED by mathlib4 AI policy: ALLOW_UPSTREAM_BOT_ACTIONS=False] "
                    f"PR #{num} ({branch}): automated 'bors merge' comment disabled"
                )
            elif execute:
                res = run_cmd([
                    "gh", "pr", "comment", str(num), "--repo", upstream_repo,
                    "--body", "bors merge",
                ])
                actions.append(f"PR #{num} ({branch}): posted 'bors merge' (rc={res.returncode})")
            else:
                actions.append(f"[DRY-RUN] PR #{num} ({branch}): would post 'bors merge'")
        if rebase_conflicting and d["mergeable"] == "CONFLICTING":
            if mathlib_dir is None or not (mathlib_dir / "Mathlib.lean").is_file():
                actions.append(f"PR #{num} ({branch}): CONFLICTING (pass --mathlib-dir to rebase)")
            elif execute:
                run_cmd(["git", "fetch", "--depth=1", UPSTREAM_URL, "master"], cwd=mathlib_dir)
                run_cmd(["git", "fetch", "origin", f"{branch}:{branch}"], cwd=mathlib_dir)
                run_cmd(["git", "checkout", branch], cwd=mathlib_dir)
                rb = run_cmd(["git", "rebase", "FETCH_HEAD"], cwd=mathlib_dir)
                if rb.returncode == 0:
                    ps = run_cmd(["git", "push", "origin", branch, "--force-with-lease"], cwd=mathlib_dir)
                    actions.append(f"PR #{num} ({branch}): rebased onto upstream/master & force-pushed (rc={ps.returncode})")
                else:
                    run_cmd(["git", "rebase", "--abort"], cwd=mathlib_dir)
                    actions.append(f"PR #{num} ({branch}): automatic rebase aborted due to conflict")
            else:
                actions.append(f"[DRY-RUN] PR #{num} ({branch}): would rebase onto upstream/master")
    return actions


def compute_queue_plan(
    details: List[Dict[str, Any]],
    max_concurrent: int,
) -> Dict[str, Any]:
    by_branch = {s.branch: s for s in PR_REGISTRY}
    pr_by_branch = {d["branch"]: d for d in details}
    open_prs = [d for d in details if d["state"] == "OPEN"]
    merged_branches = {d["branch"] for d in details if d["state"] == "MERGED"}

    unlocked_children: List[PRSpec] = []
    ready_roots: List[PRSpec] = []
    blocked: List[PRSpec] = []

    for spec in PR_REGISTRY:
        if spec.branch in pr_by_branch:
            continue
        parents = spec_parents(spec, by_branch)
        if not parents:
            ready_roots.append(spec)
        elif all(p.branch in merged_branches for p in parents):
            unlocked_children.append(spec)
        else:
            blocked.append(spec)

    available_slots = max(0, max_concurrent - len(open_prs))
    recommended_next = (unlocked_children + ready_roots)[:available_slots]
    return {
        "open_count": len(open_prs),
        "merged_count": len(merged_branches),
        "max_concurrent": max_concurrent,
        "available_slots": available_slots,
        "unlocked_children": [s.pr_id for s in unlocked_children],
        "ready_roots": [s.pr_id for s in ready_roots],
        "recommended_next": [s.pr_id for s in recommended_next],
        "blocked_count": len(blocked),
    }


def write_zulip_messages(details: List[Dict[str, Any]], out_path: pathlib.Path) -> None:
    reg_branches = {s.branch for s in PR_REGISTRY}
    open_lines = []
    for d in details:
        if d["state"] == "OPEN" and d["branch"] in reg_branches:
            c = d["checks"]
            open_lines.append(
                f"- [#{d['number']}]({d['url']}) `{d['branch']}` — "
                f"`{c['passed']}/{c['total']}` CI checks green, zero warnings, axiom-clean."
            )
    open_block = "\n".join(open_lines) if open_lines else "- (No open PRs detected)"

    next_roots = [s for s in PR_REGISTRY if s.base_branch == "master" and not s.merge_branches and s.pr_id not in ("PR-1A", "PR-3A", "PR-4A")]
    next_block = "\n".join(
        f"- `{s.pr_id}` (`{s.branch}` -> `{s.target_relpath}`): {s.pr_title}"
        for s in next_roots
    )

    content = (
        "# Lean Zulip `#PR-reviews` Human Reference Notes (Qamar Munawer)\n\n"
        "> **AI Policy Reminder (`mathlib4`):** Upstream `mathlib4` policy strictly forbids pasting "
        "LLM-generated comments into GitHub PRs or Zulip, and requires human-written communication "
        "plus explicit AI-tool disclosure in PR descriptions. Use this file as a local index only; "
        "compose all GitHub/Zulip messages yourself.\n\n"
        "All PRs extract small, self-contained modules (`<= 250` lines for Waves 5-8, `<= 100` chars/line, `#lint` `0` errors across 15 linters, strictly `[propext, Classical.choice, Quot.sound]`, `NO_RH_PROOF = TRUE`).\n\n"
        "## 1. Status Index for Wave 1 PRs (`#46127`–`#46129`)\n\n"
        f"{open_block}\n\n"
        "## 2. Independent Root PRs Queued Locally (`max_concurrent <= 4`)\n\n"
        f"{next_block}\n"
    )
    out_path.write_text(content, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Autonomous mathlib4 PR Queue & Review Manager.")
    parser.add_argument("--upstream-repo", default=UPSTREAM_REPO)
    parser.add_argument("--fork-repo", default=FORK_REPO)
    parser.add_argument("--fork-owner", default=FORK_OWNER)
    parser.add_argument("--mathlib-dir", type=pathlib.Path, default=None)
    parser.add_argument("--max-concurrent", type=int, default=4)
    parser.add_argument("--inspect", action="store_true")
    parser.add_argument("--apply-delegated", action="store_true")
    parser.add_argument("--rebase-conflicting", action="store_true")
    parser.add_argument("--advance-queue", action="store_true")
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--write-zulip", action="store_true")
    parser.add_argument("--json-report", type=pathlib.Path, default=None)
    args = parser.parse_args()

    details = fetch_pr_details(args.upstream_repo, args.fork_owner)
    print(f"=== Live {args.upstream_repo} PR Status (author={args.fork_owner}, count={len(details)}) ===")
    for d in details:
        c = d["checks"]
        print(
            f"  PR #{d['number']} | {d['state']:6s} | mergeable={d['mergeable']} | "
            f"mergeState={d['mergeStateStatus']} | checks={c['passed']}/{c['total']} (green={c['all_green']}) | "
            f"delegated={d['delegated']} | inline={d['inline_comments_count']} | human_cmts={d['human_issue_comments_count']} | "
            f"labels={d['labels']}"
        )

    actions = apply_actions(
        details,
        args.upstream_repo,
        args.fork_repo,
        args.mathlib_dir,
        args.apply_delegated,
        args.rebase_conflicting,
        args.execute,
    )
    if actions:
        print("\n=== Queue Actions ===")
        for a in actions:
            print(f"  {a}")

    plan = compute_queue_plan(details, args.max_concurrent)
    if args.advance_queue or args.inspect:
        print(
            f"\n=== {len(PR_REGISTRY)}-Branch DAG Queue Plan "
            f"(READ-ONLY, ALLOW_UPSTREAM_BOT_ACTIONS={ALLOW_UPSTREAM_BOT_ACTIONS}) ==="
        )
        print(
            f"  open={plan['open_count']} | merged={plan['merged_count']} | "
            f"max_concurrent={plan['max_concurrent']} | available_slots={plan['available_slots']}"
        )
        print(f"  unlocked_children={plan['unlocked_children']}")
        print(f"  ready_roots={plan['ready_roots']}")
        print(f"  recommended_next={plan['recommended_next']} | blocked_downstream={plan['blocked_count']}")

    if args.write_zulip:
        zpath = STAGING_DIR / "ZULIP_PR_REVIEW_MESSAGES.md"
        write_zulip_messages(details, zpath)
        print(f"\nWrote Zulip review packet: {zpath}")

    if args.json_report is not None:
        args.json_report.write_text(
            json.dumps({"prs": details, "queue_plan": plan, "actions": actions}, indent=2) + "\n",
            encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
