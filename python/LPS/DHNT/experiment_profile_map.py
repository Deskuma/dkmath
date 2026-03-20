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


@dataclass(frozen=True)
class BoundarySwitch:
    big: int
    from_body: int
    from_residual: int
    from_profile: str
    to_body: int
    to_residual: int
    to_profile: str


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


def non_other_rows(rows: list[Row]) -> list[Row]:
    return [row for row in rows if row.profile != "other"]


def boundary_switches(rows: list[Row]) -> list[BoundarySwitch]:
    filtered = non_other_rows(rows)
    switches: list[BoundarySwitch] = []
    previous: Row | None = None
    for current in filtered:
        if previous is not None and previous.profile != current.profile:
            switches.append(
                BoundarySwitch(
                    big=current.big,
                    from_body=previous.body,
                    from_residual=previous.residual,
                    from_profile=previous.profile,
                    to_body=current.body,
                    to_residual=current.residual,
                    to_profile=current.profile,
                )
            )
        previous = current
    return switches


def write_non_other_csv(rows: list[Row], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "big",
                "body",
                "residual",
                "profile",
                "cube2_repr",
                "has_type_i_nontrivial",
                "type_i_repr",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.big,
                    row.body,
                    row.residual,
                    row.profile,
                    row.cube2_repr,
                    int(row.has_type_i_nontrivial),
                    row.type_i_repr,
                ]
            )


def write_boundary_csv(switches: list[BoundarySwitch], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "big",
                "from_body",
                "from_residual",
                "from_profile",
                "to_body",
                "to_residual",
                "to_profile",
            ]
        )
        for sw in switches:
            writer.writerow(
                [
                    sw.big,
                    sw.from_body,
                    sw.from_residual,
                    sw.from_profile,
                    sw.to_body,
                    sw.to_residual,
                    sw.to_profile,
                ]
            )


def write_summary_csv(summary_rows: list[dict[str, int]], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "big",
                "rows_total",
                "count_observed_min_one_candidate",
                "count_observed_min_two_candidate",
                "count_other",
            ]
        )
        for row in summary_rows:
            writer.writerow(
                [
                    row["big"],
                    row["rows_total"],
                    row["count_observed_min_one_candidate"],
                    row["count_observed_min_two_candidate"],
                    row["count_other"],
                ]
            )


def parse_big_list(raw: str) -> list[int]:
    values: list[int] = []
    for piece in raw.split(","):
        token = piece.strip()
        if not token:
            continue
        value = int(token)
        if value < 0:
            raise ValueError("big values must be >= 0")
        values.append(value)
    if not values:
        raise ValueError("--big-list is empty")
    return values


def resolve_target_bigs(args: argparse.Namespace) -> list[int]:
    targets: list[int] = []
    if args.big is not None:
        if args.big < 0:
            raise ValueError("--big must be >= 0")
        targets.append(args.big)

    if args.big_list is not None:
        targets.extend(parse_big_list(args.big_list))

    if args.cube_m_start is not None or args.cube_m_end is not None:
        if args.cube_m_start is None or args.cube_m_end is None:
            raise ValueError("--cube-m-start and --cube-m-end must be set together")
        if args.cube_m_start < 0 or args.cube_m_end < 0:
            raise ValueError("cube m range must be >= 0")
        if args.cube_m_end < args.cube_m_start:
            raise ValueError("cube m end must be >= cube m start")
        targets.extend([m**3 for m in range(args.cube_m_start, args.cube_m_end + 1)])

    unique_targets = sorted(set(targets))
    if not unique_targets:
        raise ValueError(
            "No target Big values. Set --big, --big-list, or --cube-m-start/--cube-m-end"
        )
    return unique_targets


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Fixed-Big profile map experiment: body -> residual -> "
            "(cube1/cube2/other) with CSV export"
        )
    )
    parser.add_argument("--big", type=int, default=None, help="Fixed Big value")
    parser.add_argument(
        "--big-list",
        type=str,
        default=None,
        help="Comma-separated Big values, e.g. 27,64,125,216",
    )
    parser.add_argument(
        "--cube-m-start",
        type=int,
        default=None,
        help="Start m for cube series Big=m^3",
    )
    parser.add_argument(
        "--cube-m-end",
        type=int,
        default=None,
        help="End m for cube series Big=m^3",
    )
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
        help="Output CSV path for single --big run",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).parent / "docs",
        help="Output directory for batch files (default: ./docs)",
    )
    parser.add_argument(
        "--emit-summary",
        action="store_true",
        help="Write summary CSV for batch run",
    )
    parser.add_argument(
        "--emit-non-other",
        action="store_true",
        help="Write aggregated profile!=other CSV for batch run",
    )
    parser.add_argument(
        "--emit-boundary",
        action="store_true",
        help="Write aggregated boundary-switch CSV for batch run",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    target_bigs = resolve_target_bigs(args)
    is_single_run = (
        len(target_bigs) == 1 and args.big is not None and args.output is not None
    )

    all_non_other: list[Row] = []
    all_switches: list[BoundarySwitch] = []
    summary_rows: list[dict[str, int]] = []

    for big in target_bigs:
        body_end = big if args.body_end is None else args.body_end
        if body_end < args.body_start:
            raise ValueError("body-end must be >= body-start")

        output_path = (
            args.output
            if is_single_run
            else args.output_dir / f"profile_map_big_{big}.csv"
        )

        body_values = range(args.body_start, body_end + 1)
        rows = classify_residuals(big, body_values, max_base=args.max_base)
        write_csv(rows, output_path)

        non_other = non_other_rows(rows)
        switches = boundary_switches(rows)
        all_non_other.extend(non_other)
        all_switches.extend(switches)

        count_one = sum(1 for row in rows if row.profile == "ObservedMinOne-candidate")
        count_two = sum(1 for row in rows if row.profile == "ObservedMinTwo-candidate")
        count_other = sum(1 for row in rows if row.profile == "other")
        summary_rows.append(
            {
                "big": big,
                "rows_total": len(rows),
                "count_observed_min_one_candidate": count_one,
                "count_observed_min_two_candidate": count_two,
                "count_other": count_other,
            }
        )

        print(f"Wrote {len(rows)} rows -> {output_path}")

    if args.emit_summary:
        summary_path = args.output_dir / "profile_map_summary.csv"
        write_summary_csv(summary_rows, summary_path)
        print(f"Wrote summary -> {summary_path}")

    if args.emit_non_other:
        non_other_path = args.output_dir / "profile_map_non_other.csv"
        write_non_other_csv(all_non_other, non_other_path)
        print(f"Wrote non-other rows -> {non_other_path}")

    if args.emit_boundary:
        boundary_path = args.output_dir / "profile_map_boundary_switches.csv"
        write_boundary_csv(all_switches, boundary_path)
        print(f"Wrote boundary switches -> {boundary_path}")


if __name__ == "__main__":
    main()
