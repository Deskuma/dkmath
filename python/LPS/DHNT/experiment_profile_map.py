#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Row:
    big: int
    body: int
    residual: int
    is_cube1: bool
    is_cube2: bool
    profile: str
    has_type_i_nontrivial: bool
    type_i_repr: str
    cube2_repr: str


def is_perfect_cube(n: int) -> tuple[bool, int | None]:
    if n < 0:
        return False, None
    root = round(n ** (1 / 3))
    candidates = [root - 1, root, root + 1]
    for candidate in candidates:
        if candidate >= 0 and candidate**3 == n:
            return True, candidate
    return False, None


def find_two_cube_repr(n: int, max_base: int) -> tuple[bool, tuple[int, int] | None]:
    if n < 0:
        return False, None
    for a in range(0, max_base + 1):
        a3 = a**3
        if a3 > n:
            break
        for b in range(a, max_base + 1):
            value = a3 + b**3
            if value == n:
                return True, (a, b)
            if value > n:
                break
    return False, None


def type_i_nontrivial_repr(n: int) -> str:
    reps: list[str] = []
    if n > 1:
        reps.append(f"{n}^1")
    upper = int(n**0.5) + 2
    for a in range(2, upper):
        power = a * a
        b = 2
        while power <= n:
            if power == n:
                reps.append(f"{a}^{b}")
                break
            b += 1
            power *= a
    unique = sorted(set(reps), key=lambda x: (x.count("^"), len(x), x))
    nontrivial = [r for r in unique if not r.endswith("^1")]
    if nontrivial:
        return ";".join(nontrivial)
    return ""


def classify_residuals(
    big: int, body_values: Iterable[int], max_base: int
) -> list[Row]:
    rows: list[Row] = []
    for body in body_values:
        residual = big - body
        if residual < 0:
            continue

        cube1, cube_root = is_perfect_cube(residual)
        cube2, pair = find_two_cube_repr(residual, max_base=max_base)

        if cube1:
            profile = "ObservedMinOne-candidate"
        elif cube2:
            profile = "ObservedMinTwo-candidate"
        else:
            profile = "other"

        type_i_repr = type_i_nontrivial_repr(residual)
        has_type_i_nontrivial = type_i_repr != ""
        cube2_repr = f"{pair[0]}^3+{pair[1]}^3" if pair is not None else ""

        rows.append(
            Row(
                big=big,
                body=body,
                residual=residual,
                is_cube1=cube1,
                is_cube2=cube2,
                profile=profile,
                has_type_i_nontrivial=has_type_i_nontrivial,
                type_i_repr=type_i_repr,
                cube2_repr=cube2_repr,
            )
        )
    return rows


def write_csv(rows: list[Row], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "big",
                "body",
                "residual",
                "is_cube1",
                "is_cube2",
                "profile",
                "has_type_i_nontrivial",
                "type_i_repr",
                "cube2_repr",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.big,
                    row.body,
                    row.residual,
                    int(row.is_cube1),
                    int(row.is_cube2),
                    row.profile,
                    int(row.has_type_i_nontrivial),
                    row.type_i_repr,
                    row.cube2_repr,
                ]
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Fixed-Big profile map experiment: body -> residual -> "
            "(cube1/cube2/other) with CSV export"
        )
    )
    parser.add_argument("--big", type=int, required=True, help="Fixed Big value")
    parser.add_argument(
        "--body-start",
        type=int,
        default=0,
        help="Body scan start (inclusive)",
    )
    parser.add_argument(
        "--body-end",
        type=int,
        default=None,
        help="Body scan end (inclusive). default: big",
    )
    parser.add_argument(
        "--max-base",
        type=int,
        default=100,
        help="Upper bound for two-cube search bases",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output CSV path (default: docs/profile_map_big_<big>.csv)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    body_end = args.big if args.body_end is None else args.body_end
    if body_end < args.body_start:
        raise ValueError("body-end must be >= body-start")

    output_path = (
        args.output
        if args.output is not None
        else Path(__file__).parent / "docs" / f"profile_map_big_{args.big}.csv"
    )

    body_values = range(args.body_start, body_end + 1)
    rows = classify_residuals(args.big, body_values, max_base=args.max_base)
    write_csv(rows, output_path)

    print(f"Wrote {len(rows)} rows -> {output_path}")


if __name__ == "__main__":
    main()
