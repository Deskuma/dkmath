#!/usr/bin/env python3
"""Simple assistant driver: one iteration of (build -> find unknowns -> find defs -> insert -> report).

Prototype: not a production tool. Works by calling the project's `lean-build.sh` in
the `lean/dk_math` folder by default. Falls back to parsing arbitrary stderr for
lines like `path/to/file.lean:LINE:COL: Unknown identifier `NAME``.

Usage example:
  python assistant_driver.py --build-target DkMath.FLT.docs.StandAlone.a \
    --insert-target lean/dk_math/DkMath/FLT/docs/StandAlone/a.lean --auto

"""
from pathlib import Path
import subprocess
import re
import sys
import json
from typing import List, Dict, Any

# import helpers from theorem_picker by adding parent to sys.path
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from theorem_picker import (
    find_definitions_by_name,
    insert_snippet_into_text,
    find_project_root,
)


UNKNOWN_RE = re.compile(
    r"(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+):\s+Unknown identifier `(?P<ident>[^`]+)`"
)


def run_build(root: Path, build_target: str = None) -> subprocess.CompletedProcess:
    build_dir = root / "lean" / "dk_math"
    cmd = ["./lean-build.sh"]
    if build_target:
        cmd.append(build_target)
    proc = subprocess.run(cmd, cwd=str(build_dir), capture_output=True, text=True)
    return proc


def parse_unknowns(build_proc: subprocess.CompletedProcess) -> List[Dict[str, Any]]:
    out = build_proc.stderr + "\n" + build_proc.stdout
    matches = []
    for m in UNKNOWN_RE.finditer(out):
        matches.append(
            {
                "file": m.group("file"),
                "line": int(m.group("line")),
                "col": int(m.group("col")),
                "ident": m.group("ident"),
            }
        )
    return matches


def choose_candidate(
    candidates: List[Dict[str, Any]],
    select_index: int = None,
    interactive: bool = False,
):
    if not candidates:
        return None
    if len(candidates) == 1:
        return candidates[0]
    # present summary
    summary = []
    for i, d in enumerate(candidates):
        summary.append(
            {
                "index": i,
                "file": d.get("file"),
                "preview": (
                    d.get("snippet", "").splitlines()[0] if d.get("snippet") else ""
                ),
            }
        )
    print("Multiple candidates found:")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    if select_index is not None:
        if 0 <= select_index < len(candidates):
            return candidates[select_index]
        else:
            print(f"select_index {select_index} out of range; using first candidate")
            return candidates[0]
    if interactive and sys.stdin.isatty():
        try:
            sel = input(
                f"Select candidate index [0-{len(candidates)-1}] (enter for 0): "
            )
            if sel.strip() == "":
                return candidates[0]
            si = int(sel.strip())
            if 0 <= si < len(candidates):
                return candidates[si]
        except Exception:
            pass
    # default
    return candidates[0]


def insert_and_report(
    root: Path,
    unknown: Dict[str, Any],
    select_index: int = None,
    interactive: bool = False,
    apply: bool = False,
):
    file = unknown["file"]
    line = unknown["line"]
    ident = unknown["ident"]
    # resolve file path relative to root if not absolute
    fpath = Path(file)
    if not fpath.is_file():
        # try relative to root
        candidate = root / file
        if candidate.is_file():
            fpath = candidate
        else:
            print(f"Cannot locate file for unknown: {file}")
            return {"ok": False, "reason": "file_not_found"}

    # search repo for definitions matching ident
    candidates = find_definitions_by_name(root, ident)
    if not candidates:
        return {"ok": False, "reason": "no_candidates", "ident": ident}

    chosen = choose_candidate(
        candidates, select_index=select_index, interactive=interactive
    )
    if not chosen:
        return {"ok": False, "reason": "no_selection"}

    snippet = chosen["snippet"]
    # insert before the error line to make definition available earlier
    insert_line = max(1, line - 1)
    orig_text = fpath.read_text(encoding="utf-8")
    new_text, patch = insert_snippet_into_text(orig_text, snippet, insert_line)
    report = {
        "file": str(fpath),
        "ident": ident,
        "candidate_file": chosen.get("file"),
        "patch": patch,
    }
    if apply:
        # write to a .inserted file first
        outp = fpath.with_suffix(fpath.suffix + ".inserted")
        outp.write_text(new_text, encoding="utf-8")
        report["applied_to"] = str(outp)
    return report


def main(argv=None):
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--build-target", help="Build target to pass to lean-build.sh", nargs="?"
    )
    parser.add_argument(
        "--insert-target",
        help="(Optional) file to insert into. By default uses file from build error.",
        nargs="?",
    )
    parser.add_argument(
        "--select-index",
        type=int,
        help="Auto-select candidate index if multiple.",
        nargs="?",
    )
    parser.add_argument(
        "--interactive", action="store_true", help="Interactive candidate selection"
    )
    parser.add_argument(
        "--apply", action="store_true", help="Write inserted file instead of dry-run"
    )
    args = parser.parse_args(argv)

    root = find_project_root(Path(__file__).resolve().parent.parent)
    print(f"Project root: {root}")
    proc = run_build(root, args.build_target)
    if proc.returncode == 0:
        print("Build succeeded — nothing to do.")
        return 0
    unknowns = parse_unknowns(proc)
    if not unknowns:
        print("No Unknown identifier errors found in build output.")
        print("Build stderr:\n", proc.stderr)
        return 2

    reports = []
    for u in unknowns:
        rep = insert_and_report(
            root,
            u,
            select_index=args.select_index,
            interactive=args.interactive,
            apply=args.apply,
        )
        reports.append(rep)

    print("Iteration report:\n", json.dumps(reports, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
