#!/usr/bin/env python3
"""Scan pressure witnesses and delayed-remainder levels on Collatz windows.

This script mirrors the finite natural counts used by
`DkMath.Collatz.PetalBridge`:

* source pressure depth count
* first selected source-pressure depth
* source continuation mass at that depth
* shifted-tail remainder levels L1..L5

The output is observational data only.  It is meant to guide which Lean theorem
should be attempted next.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class OrbitPressureRow:
    n: int
    steps: int
    r_start: int
    depth_len: int
    sum_s: int
    pressure_depth_count: int
    first_pressure_j: int
    first_pressure_depth: int
    continuation_mass_at_first_pressure: int
    retention_mass_at_first_pressure: int
    l1_remainder: int
    l2_remainder: int
    l3_remainder: int
    l4_remainder: int
    l5_remainder: int
    falling_l1: int
    falling_l2: int
    falling_l3: int
    falling_l4: int
    falling_l5: int


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


def orbit_labels_and_heights(n: int, steps: int) -> tuple[list[int], list[int]]:
    labels: list[int] = []
    heights: list[int] = []
    current = n
    for _ in range(steps + 1):
        labels.append(current)
        next_value, height = accelerated_step(current)
        heights.append(height)
        current = next_value
    return labels, heights


def count_residue(values: list[int], modulus: int, residue: int) -> int:
    return sum(1 for value in values if value % modulus == residue)


def retention_mass(labels: list[int], steps: int, depth: int) -> int:
    return count_residue(labels[:steps], 2**depth, 2**depth - 1)


def continuation_mass(labels: list[int], steps: int, depth: int) -> int:
    return count_residue(labels[:steps], 2 ** (depth + 1), 2 ** (depth + 1) - 1)


def pressure_depths(labels: list[int], steps: int, r_start: int, depth_len: int) -> list[int]:
    selected: list[int] = []
    for j in range(depth_len):
        depth = r_start + j
        continuation = continuation_mass(labels, steps, depth)
        retention = retention_mass(labels, steps, depth)
        if retention < 2 * continuation:
            selected.append(j)
    return selected


def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OrbitPressureRow:
    labels, heights = orbit_labels_and_heights(n, steps)
    tail = labels[1 : steps + 1]
    selected = pressure_depths(labels, steps, r_start, depth_len)
    first_j = selected[0] if selected else -1
    first_depth = r_start + first_j if selected else -1
    first_continuation = (
        continuation_mass(labels, steps, first_depth) if selected else 0
    )
    first_retention = retention_mass(labels, steps, first_depth) if selected else 0
    return OrbitPressureRow(
        n=n,
        steps=steps,
        r_start=r_start,
        depth_len=depth_len,
        sum_s=sum(heights[:steps]),
        pressure_depth_count=len(selected),
        first_pressure_j=first_j,
        first_pressure_depth=first_depth,
        continuation_mass_at_first_pressure=first_continuation,
        retention_mass_at_first_pressure=first_retention,
        l1_remainder=count_residue(tail[:steps], 8, 7),
        l2_remainder=count_residue(tail[:steps], 16, 15),
        l3_remainder=count_residue(tail[:steps], 32, 31),
        l4_remainder=count_residue(tail[:steps], 64, 63),
        l5_remainder=count_residue(tail[:steps], 128, 127),
        falling_l1=count_residue(tail[:steps], 8, 3),
        falling_l2=count_residue(tail[:steps], 16, 7),
        falling_l3=count_residue(tail[:steps], 32, 15),
        falling_l4=count_residue(tail[:steps], 64, 31),
        falling_l5=count_residue(tail[:steps], 128, 63),
    )


def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[OrbitPressureRow]:
    rows: list[OrbitPressureRow] = []
    for n in range(1, max_n + 1, 2):
        rows.append(row_for(n, steps, r_start, depth_len))
    return rows


def write_csv(rows: list[OrbitPressureRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(OrbitPressureRow.__dataclass_fields__))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def write_summary(rows: list[OrbitPressureRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with_pressure = [row for row in rows if row.pressure_depth_count > 0]
    deep_l5 = [row for row in rows if row.l5_remainder > 0]
    max_pressure = max((row.pressure_depth_count for row in rows), default=0)
    max_l5 = max((row.l5_remainder for row in rows), default=0)
    sample = sorted(
        with_pressure,
        key=lambda row: (
            -row.pressure_depth_count,
            -row.continuation_mass_at_first_pressure,
            row.n,
        ),
    )[:12]
    lines = [
        "# Collatz Orbit Pressure Remainder Scan",
        "",
        f"- rows: `{len(rows)}`",
        f"- rows with pressure witness: `{len(with_pressure)}`",
        f"- rows with L5 remainder: `{len(deep_l5)}`",
        f"- max pressure depth count: `{max_pressure}`",
        f"- max L5 remainder: `{max_l5}`",
        "",
        "## Top Pressure Samples",
        "",
        "| n | sumS | pressure count | first depth | cont mass | ret mass | L1 | L2 | L3 | L4 | L5 |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in sample:
        lines.append(
            "| "
            f"{row.n} | {row.sum_s} | {row.pressure_depth_count} | "
            f"{row.first_pressure_depth} | "
            f"{row.continuation_mass_at_first_pressure} | "
            f"{row.retention_mass_at_first_pressure} | "
            f"{row.l1_remainder} | {row.l2_remainder} | {row.l3_remainder} | "
            f"{row.l4_remainder} | {row.l5_remainder} |"
        )
    lines.extend(
        [
            "",
            "## Reading",
            "",
            "`pressure_depth_count > 0` marks at least one local source continuation",
            "pressure witness.  The Lean checkpoint 121 bridge turns the depth-two",
            "one-range version into a positive mass plus delayed-budget pair.",
            "",
            "The L1..L5 columns record the shifted-tail all-ones delayed remainders.",
            "They should be read as possible retained mass, not as independent",
            "budget entries.",
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
    csv_path = args.out_dir / "orbit_pressure_remainder_scan.csv"
    summary_path = args.out_dir / "orbit_pressure_remainder_scan.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
