#!/usr/bin/env python3
"""Scan whether selected source pressure depths form a prefix.

Checkpoint 124 separates the proved nesting of all-ones carriers from the
stronger, still experimental question:

    if a deeper depth is selected by pressure, are all shallower depths selected?

This script observes that question directly and records integer pressure
margins

    2 * continuation_mass(depth) - retention_mass(depth)

for a finite depth range.  Positive margin is the Python counterpart of the
Lean theorem `isSourcePressureDepth_iff_margin_pos`.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class PrefixRow:
    n: int
    steps: int
    r_start: int
    depth_len: int
    selected_depths: str
    selected_count: int
    selected_depths_are_prefix: bool
    selected_depths_are_consecutive: bool
    frontier_depth: int
    max_selected_depth: int
    missing_selected_depths: str
    min_selected_margin: int
    max_unselected_margin: int
    margin_profile: str


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count


def accelerated_step(n: int) -> tuple[int, int]:
    value = 3 * n + 1
    height = v2(value)
    return value >> height, height


def orbit_labels(n: int, steps: int) -> list[int]:
    labels: list[int] = []
    current = n
    for _ in range(steps):
        labels.append(current)
        current, _height = accelerated_step(current)
    return labels


def count_residue(values: list[int], modulus: int, residue: int) -> int:
    return sum(1 for value in values if value % modulus == residue)


def retention_mass(labels: list[int], depth: int) -> int:
    return count_residue(labels, 2**depth, 2**depth - 1)


def continuation_mass(labels: list[int], depth: int) -> int:
    return count_residue(labels, 2 ** (depth + 1), 2 ** (depth + 1) - 1)


def margin_at(labels: list[int], depth: int) -> int:
    return 2 * continuation_mass(labels, depth) - retention_mass(labels, depth)


def depths_are_consecutive(depths: list[int]) -> bool:
    return all(right == left + 1 for left, right in zip(depths, depths[1:]))


def depths_are_prefix(depths: list[int], r_start: int) -> bool:
    if not depths:
        return True
    return depths[0] == r_start and depths_are_consecutive(depths)


def missing_depths_from_prefix(depths: list[int], r_start: int) -> list[int]:
    if not depths:
        return []
    selected = set(depths)
    return [depth for depth in range(r_start, max(depths) + 1) if depth not in selected]


def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PrefixRow:
    labels = orbit_labels(n, steps)
    depths = list(range(r_start, r_start + depth_len))
    margins = {depth: margin_at(labels, depth) for depth in depths}
    selected = [depth for depth in depths if margins[depth] > 0]
    unselected = [depth for depth in depths if margins[depth] <= 0]
    missing = missing_depths_from_prefix(selected, r_start)
    frontier = max(selected, default=r_start - 1) + 1
    return PrefixRow(
        n=n,
        steps=steps,
        r_start=r_start,
        depth_len=depth_len,
        selected_depths=";".join(str(depth) for depth in selected),
        selected_count=len(selected),
        selected_depths_are_prefix=depths_are_prefix(selected, r_start),
        selected_depths_are_consecutive=depths_are_consecutive(selected),
        frontier_depth=frontier,
        max_selected_depth=max(selected, default=0),
        missing_selected_depths=";".join(str(depth) for depth in missing),
        min_selected_margin=min((margins[depth] for depth in selected), default=0),
        max_unselected_margin=max((margins[depth] for depth in unselected), default=0),
        margin_profile=";".join(f"{depth}:{margins[depth]}" for depth in depths),
    )


def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[PrefixRow]:
    return [row_for(n, steps, r_start, depth_len) for n in range(1, max_n + 1, 2)]


def write_csv(rows: list[PrefixRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=list(PrefixRow.__dataclass_fields__),
            lineterminator="\n",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def write_summary(rows: list[PrefixRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nonempty = [row for row in rows if row.selected_count > 0]
    prefix = [row for row in rows if row.selected_depths_are_prefix]
    nonempty_prefix = [row for row in nonempty if row.selected_depths_are_prefix]
    consecutive = [row for row in rows if row.selected_depths_are_consecutive]
    nonempty_consecutive = [row for row in nonempty if row.selected_depths_are_consecutive]
    prefix_failures = [row for row in rows if not row.selected_depths_are_prefix]
    max_selected_count = max((row.selected_count for row in rows), default=0)
    max_selected_depth = max((row.max_selected_depth for row in rows), default=0)
    max_frontier = max((row.frontier_depth for row in rows), default=0)
    samples = sorted(
        nonempty,
        key=lambda row: (-row.selected_count, row.n),
    )[:12]
    failure_samples = prefix_failures[:12]
    lines = [
        "# Collatz Selected Pressure Prefix Scan",
        "",
        f"- rows: `{len(rows)}`",
        f"- nonempty selected rows: `{len(nonempty)}`",
        f"- prefix rows: `{len(prefix)}`",
        f"- nonempty prefix rows: `{len(nonempty_prefix)}` / `{len(nonempty)}`",
        f"- consecutive rows: `{len(consecutive)}`",
        f"- nonempty consecutive rows: `{len(nonempty_consecutive)}` / `{len(nonempty)}`",
        f"- prefix failure rows: `{len(prefix_failures)}`",
        f"- max selected count: `{max_selected_count}`",
        f"- max selected depth: `{max_selected_depth}`",
        f"- max frontier depth: `{max_frontier}`",
        "",
        "## Top Selected Samples",
        "",
        "| n | selected depths | frontier | min selected margin | max unselected margin | margins |",
        "|---:|---|---:|---:|---:|---|",
    ]
    for row in samples:
        lines.append(
            "| "
            f"{row.n} | {row.selected_depths} | {row.frontier_depth} | "
            f"{row.min_selected_margin} | {row.max_unselected_margin} | "
            f"{row.margin_profile} |"
        )
    lines.extend(
        [
            "",
            "## Prefix Failure Samples",
            "",
            "| n | selected depths | missing | margins |",
            "|---:|---|---|---|",
        ]
    )
    if failure_samples:
        for row in failure_samples:
            lines.append(
                "| "
                f"{row.n} | {row.selected_depths} | "
                f"{row.missing_selected_depths} | {row.margin_profile} |"
            )
    else:
        lines.append("| - | none observed | - | - |")
    lines.extend(
        [
            "",
            "## Reading",
            "",
            "A positive margin is the experimental counterpart of Lean's",
            "`IsSourcePressureDepth`.  Prefix rows support the frontier reading:",
            "selected pressure depths form an initial tower segment rather than",
            "independent budget carriers.",
            "",
            "This is observational only.  Checkpoint 124 proves carrier nesting and",
            "margin equivalence, but does not prove pressure-prefix monotonicity.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=9999)
    parser.add_argument("--steps", type=int, default=128)
    parser.add_argument("--r-start", type=int, default=2)
    parser.add_argument("--depth-len", type=int, default=10)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("python/Collatz/PetalBridge/results"),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = scan(args.max_n, args.steps, args.r_start, args.depth_len)
    csv_path = args.out_dir / "selected_pressure_prefix_scan.csv"
    summary_path = args.out_dir / "selected_pressure_prefix_scan.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
