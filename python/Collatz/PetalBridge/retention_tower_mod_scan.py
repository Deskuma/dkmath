#!/usr/bin/env python3
"""Scan the Collatz delayed-retention residue tower up to a power-of-two modulus.

The Lean file `DkMath.Collatz.PetalBridge` proves the first concrete levels of
the following observation:

    (2^d - 1) mod 2^d
      splits inside mod 2^(d+1) into
        (2^d - 1) and (2^(d+1) - 1),

and one exact height-one Collatz step `(3n + 1) / 2` sends those two children to
the recovery and continuation residues modulo `2^(d-1)`.

This script produces CSV evidence through `mod 1024` by default.  It is an
observation tool only; the Lean theorems remain the source of truth.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class TowerRow:
    depth: int
    parent_modulus: int
    parent_residue: int
    child_modulus: int
    recovery_child: int
    continuation_child: int
    target_modulus: int
    recovery_target: int
    continuation_target: int
    expected_recovery_target: int
    expected_continuation_target: int
    recovery_ok: bool
    continuation_ok: bool


def one_height_step(residue: int) -> int:
    """The visible height-one odd Collatz step for residues in `7 mod 8`."""
    return (3 * residue + 1) // 2


def scan(max_modulus: int) -> list[TowerRow]:
    rows: list[TowerRow] = []
    depth = 3
    while 2 ** (depth + 1) <= max_modulus:
        parent_modulus = 2**depth
        parent_residue = parent_modulus - 1
        child_modulus = 2 ** (depth + 1)
        recovery_child = parent_residue
        continuation_child = child_modulus - 1
        target_modulus = parent_modulus
        recovery_target = one_height_step(recovery_child) % target_modulus
        continuation_target = one_height_step(continuation_child) % target_modulus
        expected_recovery_target = 2 ** (depth - 1) - 1
        expected_continuation_target = parent_residue
        rows.append(
            TowerRow(
                depth=depth,
                parent_modulus=parent_modulus,
                parent_residue=parent_residue,
                child_modulus=child_modulus,
                recovery_child=recovery_child,
                continuation_child=continuation_child,
                target_modulus=target_modulus,
                recovery_target=recovery_target,
                continuation_target=continuation_target,
                expected_recovery_target=expected_recovery_target,
                expected_continuation_target=expected_continuation_target,
                recovery_ok=recovery_target == expected_recovery_target,
                continuation_ok=continuation_target == expected_continuation_target,
            )
        )
        depth += 1
    return rows


def write_csv(rows: list[TowerRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(TowerRow.__dataclass_fields__))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def write_summary(rows: list[TowerRow], path: Path, max_modulus: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    all_ok = all(row.recovery_ok and row.continuation_ok for row in rows)
    lines = [
        "# Collatz PetalBridge Retention Tower Scan",
        "",
        f"- max modulus: `{max_modulus}`",
        f"- scanned levels: `{len(rows)}`",
        f"- all transitions matched expected law: `{all_ok}`",
        "",
        "## Law",
        "",
        "For depth `d >= 3`:",
        "",
        "```text",
        "parent:       2^d - 1 mod 2^d",
        "recovery:     2^d - 1 mod 2^(d+1)",
        "continuation: 2^(d+1) - 1 mod 2^(d+1)",
        "",
        "T1(recovery)     = 2^(d-1) - 1 mod 2^d",
        "T1(continuation) = 2^d - 1 mod 2^d",
        "```",
        "",
        "where `T1(x) = (3*x + 1) / 2` is the exact height-one visible step.",
        "",
        "## Table",
        "",
        "| d | parent | recovery child | continuation child | recovery target | continuation target | ok |",
        "|---:|---:|---:|---:|---:|---:|:---:|",
    ]
    for row in rows:
        ok = row.recovery_ok and row.continuation_ok
        lines.append(
            "| "
            f"{row.depth} | "
            f"{row.parent_residue} mod {row.parent_modulus} | "
            f"{row.recovery_child} mod {row.child_modulus} | "
            f"{row.continuation_child} mod {row.child_modulus} | "
            f"{row.recovery_target} mod {row.target_modulus} | "
            f"{row.continuation_target} mod {row.target_modulus} | "
            f"{ok} |"
        )
    lines.extend(
        [
            "",
            "## Lean Inference",
            "",
            "The table supports replacing one-off named arithmetic anchors by the",
            "existing generic residue theorem whenever the call site can tolerate",
            "the power-of-two parameters.  For readability, the concrete Lean",
            "aliases remain useful at the active frontier levels.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-modulus", type=int, default=1024)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("python/Collatz/PetalBridge/results"),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = scan(args.max_modulus)
    csv_path = args.out_dir / "retention_tower_mod_scan.csv"
    summary_path = args.out_dir / "retention_tower_mod_scan.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path, args.max_modulus)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
