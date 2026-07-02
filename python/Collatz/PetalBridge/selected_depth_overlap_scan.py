#!/usr/bin/env python3
"""Scan overlap between selected source pressure depths.

Checkpoint 122 proves that `pressureDepthCount >= 2` gives two selected
pressure-depth witnesses, but it does not claim that the corresponding budget
carriers are independent.

This script observes the missing question on concrete Collatz windows:

    for selected depths d1, d2,
    how much do their continuation-label index sets overlap?

The output is experimental data for choosing the next Lean predicate, such as
`SelectedDepthsAddressSeparated` or `DisjointTowerTargets`.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path


@dataclass(frozen=True)
class OverlapRow:
    n: int
    steps: int
    r_start: int
    depth_len: int
    selected_depths: str
    selected_count: int
    selected_depths_are_prefix: bool
    selected_depths_are_consecutive: bool
    max_selected_depth: int
    missing_selected_depths: str
    max_pairwise_overlap: int
    min_pairwise_overlap: int
    total_pair_count: int
    disjoint_pair_count: int
    has_disjoint_pair: bool
    first_pair: str
    first_pair_overlap: int
    first_pair_left_mass: int
    first_pair_right_mass: int


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


def continuation_indices(labels: list[int], depth: int) -> set[int]:
    modulus = 2 ** (depth + 1)
    residue = modulus - 1
    return {i for i, value in enumerate(labels) if value % modulus == residue}


def retention_indices(labels: list[int], depth: int) -> set[int]:
    modulus = 2**depth
    residue = modulus - 1
    return {i for i, value in enumerate(labels) if value % modulus == residue}


def selected_depths(labels: list[int], r_start: int, depth_len: int) -> list[int]:
    selected: list[int] = []
    for j in range(depth_len):
        depth = r_start + j
        continuation = continuation_indices(labels, depth)
        retention = retention_indices(labels, depth)
        if len(retention) < 2 * len(continuation):
            selected.append(depth)
    return selected


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


def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OverlapRow:
    labels = orbit_labels(n, steps)
    depths = selected_depths(labels, r_start, depth_len)
    index_sets = {depth: continuation_indices(labels, depth) for depth in depths}
    missing = missing_depths_from_prefix(depths, r_start)
    pair_stats: list[tuple[int, int, int]] = []
    for left, right in combinations(depths, 2):
        pair_stats.append((left, right, len(index_sets[left] & index_sets[right])))
    if pair_stats:
        overlaps = [overlap for _left, _right, overlap in pair_stats]
        first_left, first_right, first_overlap = pair_stats[0]
        first_pair = f"{first_left}:{first_right}"
        first_left_mass = len(index_sets[first_left])
        first_right_mass = len(index_sets[first_right])
        max_overlap = max(overlaps)
        min_overlap = min(overlaps)
        disjoint_pair_count = sum(1 for overlap in overlaps if overlap == 0)
    else:
        first_pair = ""
        first_overlap = 0
        first_left_mass = 0
        first_right_mass = 0
        max_overlap = 0
        min_overlap = 0
        disjoint_pair_count = 0
    return OverlapRow(
        n=n,
        steps=steps,
        r_start=r_start,
        depth_len=depth_len,
        selected_depths=";".join(str(depth) for depth in depths),
        selected_count=len(depths),
        selected_depths_are_prefix=depths_are_prefix(depths, r_start),
        selected_depths_are_consecutive=depths_are_consecutive(depths),
        max_selected_depth=max(depths, default=0),
        missing_selected_depths=";".join(str(depth) for depth in missing),
        max_pairwise_overlap=max_overlap,
        min_pairwise_overlap=min_overlap,
        total_pair_count=len(pair_stats),
        disjoint_pair_count=disjoint_pair_count,
        has_disjoint_pair=disjoint_pair_count > 0,
        first_pair=first_pair,
        first_pair_overlap=first_overlap,
        first_pair_left_mass=first_left_mass,
        first_pair_right_mass=first_right_mass,
    )


def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[OverlapRow]:
    return [row_for(n, steps, r_start, depth_len) for n in range(1, max_n + 1, 2)]


def write_csv(rows: list[OverlapRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=list(OverlapRow.__dataclass_fields__),
            lineterminator="\n",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def write_summary(rows: list[OverlapRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    multi = [row for row in rows if row.selected_count >= 2]
    with_disjoint = [row for row in multi if row.has_disjoint_pair]
    all_overlap = [row for row in multi if not row.has_disjoint_pair]
    prefix_rows = [row for row in rows if row.selected_depths_are_prefix]
    consecutive_rows = [row for row in rows if row.selected_depths_are_consecutive]
    nonempty = [row for row in rows if row.selected_count > 0]
    nonempty_prefix = [row for row in nonempty if row.selected_depths_are_prefix]
    nonempty_consecutive = [row for row in nonempty if row.selected_depths_are_consecutive]
    max_selected = max((row.selected_count for row in rows), default=0)
    max_selected_depth = max((row.max_selected_depth for row in rows), default=0)
    max_overlap = max((row.max_pairwise_overlap for row in rows), default=0)
    samples = sorted(
        multi,
        key=lambda row: (-row.selected_count, -row.disjoint_pair_count, row.n),
    )[:12]
    lines = [
        "# Collatz Selected Depth Overlap Scan",
        "",
        f"- rows: `{len(rows)}`",
        f"- rows with at least two selected depths: `{len(multi)}`",
        f"- rows with a disjoint selected-depth pair: `{len(with_disjoint)}`",
        f"- rows where every selected-depth pair overlaps: `{len(all_overlap)}`",
        f"- rows whose selected depths are a prefix from `r_start`: `{len(prefix_rows)}`",
        f"- nonempty prefix rows: `{len(nonempty_prefix)}` / `{len(nonempty)}`",
        f"- rows whose selected depths are consecutive: `{len(consecutive_rows)}`",
        f"- nonempty consecutive rows: `{len(nonempty_consecutive)}` / `{len(nonempty)}`",
        f"- max selected depth count: `{max_selected}`",
        f"- max selected depth: `{max_selected_depth}`",
        f"- max pairwise overlap: `{max_overlap}`",
        "",
        "## Top Multi-Witness Samples",
        "",
        "| n | selected depths | prefix | consecutive | missing | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |",
        "|---:|---|---|---|---|---:|---:|---:|---|---:|---|",
    ]
    for row in samples:
        lines.append(
            "| "
            f"{row.n} | {row.selected_depths} | {row.selected_depths_are_prefix} | "
            f"{row.selected_depths_are_consecutive} | {row.missing_selected_depths} | "
            f"{row.total_pair_count} | {row.disjoint_pair_count} | "
            f"{row.max_pairwise_overlap} | {row.first_pair} | {row.first_pair_overlap} | "
            f"{row.first_pair_left_mass}:{row.first_pair_right_mass} |"
        )
    lines.extend(
        [
            "",
            "## Reading",
            "",
            "A disjoint pair means two selected continuation index sets are disjoint",
            "in this finite orbit window.  This is only experimental evidence.",
            "",
            "If disjoint pairs are common, a future Lean predicate could target",
            "`DisjointTowerTargets`.  If all selected pairs overlap, the right",
            "formal condition may need to express nested selected-depth behavior.",
            "",
            "The prefix/consecutive fields test the next hypothesis: selected",
            "depths may form a visible initial tower segment.  A prefix row means",
            "`r_start, r_start+1, ..., max_selected_depth` are all selected.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=999)
    parser.add_argument("--steps", type=int, default=64)
    parser.add_argument("--r-start", type=int, default=2)
    parser.add_argument("--depth-len", type=int, default=8)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("python/Collatz/PetalBridge/results"),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = scan(args.max_n, args.steps, args.r_start, args.depth_len)
    csv_path = args.out_dir / "selected_depth_overlap_scan.csv"
    summary_path = args.out_dir / "selected_depth_overlap_scan.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
