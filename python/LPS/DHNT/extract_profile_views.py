#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path


def parse_big_list(raw: str | None) -> list[int] | None:
    if raw is None:
        return None
    values: list[int] = []
    for token in raw.split(","):
        part = token.strip()
        if not part:
            continue
        values.append(int(part))
    return values if values else None


def read_summary(path: Path) -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(
                {
                    "big": int(row["big"]),
                    "rows_total": int(row["rows_total"]),
                    "count_one": int(row["count_observed_min_one_candidate"]),
                    "count_two": int(row["count_observed_min_two_candidate"]),
                    "count_other": int(row["count_other"]),
                }
            )
    return rows


def read_boundary(path: Path) -> list[dict[str, int | str]]:
    rows: list[dict[str, int | str]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            from_body = int(row["from_body"])
            to_body = int(row["to_body"])
            from_residual = int(row["from_residual"])
            to_residual = int(row["to_residual"])
            rows.append(
                {
                    "big": int(row["big"]),
                    "from_body": from_body,
                    "from_residual": from_residual,
                    "from_profile": row["from_profile"],
                    "to_body": to_body,
                    "to_residual": to_residual,
                    "to_profile": row["to_profile"],
                    "delta_body": to_body - from_body,
                    "delta_residual": to_residual - from_residual,
                }
            )
    return rows


def filter_by_big_order(rows: list[dict], big_order: list[int]) -> list[dict]:
    order_set = set(big_order)
    filtered = [row for row in rows if int(row["big"]) in order_set]
    rank = {big: i for i, big in enumerate(big_order)}
    filtered.sort(key=lambda row: (rank[int(row["big"])], int(row.get("to_body", 0))))
    return filtered


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def make_delta_first_appearance(
    boundary_rows: list[dict[str, int | str]], big_order: list[int]
) -> list[dict[str, object]]:
    by_big: dict[int, set[int]] = defaultdict(set)
    for row in boundary_rows:
        by_big[int(row["big"])].add(int(row["delta_body"]))

    seen: set[int] = set()
    out: list[dict[str, object]] = []
    for big in big_order:
        current = sorted(by_big.get(big, set()))
        new_vals = sorted(set(current) - seen)
        seen.update(current)
        out.append(
            {
                "big": big,
                "delta_body_set": "{" + ", ".join(map(str, current)) + "}",
                "new_delta_body": (
                    "{" + ", ".join(map(str, new_vals)) + "}" if new_vals else "∅"
                ),
                "cumulative_delta_body": "{" + ", ".join(map(str, sorted(seen))) + "}",
            }
        )
    return out


def make_growth_timeline(
    summary_rows: list[dict[str, int]],
    first_rows: list[dict[str, object]],
    big_order: list[int],
) -> list[dict[str, object]]:
    summary_map = {row["big"]: row for row in summary_rows}
    first_map = {int(row["big"]): row for row in first_rows}

    timeline: list[dict[str, object]] = []
    prev_one: int | None = None
    prev_two: int | None = None

    for big in big_order:
        if big not in summary_map:
            continue
        row = summary_map[big]
        one = row["count_one"]
        two = row["count_two"]
        delta_one = "-" if prev_one is None else f"+{one - prev_one}"
        delta_two = "-" if prev_two is None else f"+{two - prev_two}"
        timeline.append(
            {
                "big": big,
                "one_candidate": one,
                "delta_one": delta_one,
                "two_candidate": two,
                "delta_two": delta_two,
                "new_delta_body": first_map.get(big, {}).get("new_delta_body", "∅"),
            }
        )
        prev_one = one
        prev_two = two

    return timeline


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Extract compact analytical views from profile-map CSV outputs."
    )
    parser.add_argument(
        "--input-dir",
        type=Path,
        default=Path(__file__).parent / "docs",
        help="Directory containing profile_map_summary.csv and profile_map_boundary_switches.csv",
    )
    parser.add_argument(
        "--big-order",
        type=str,
        default=None,
        help="Comma-separated Big order for stage analysis (e.g. 27,64,125,216,343,512,729)",
    )
    parser.add_argument(
        "--output-prefix",
        type=str,
        default="profile_map",
        help="Prefix for generated CSV files",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    summary_path = args.input_dir / "profile_map_summary.csv"
    boundary_path = args.input_dir / "profile_map_boundary_switches.csv"

    if not summary_path.exists():
        raise FileNotFoundError(f"Missing summary CSV: {summary_path}")
    if not boundary_path.exists():
        raise FileNotFoundError(f"Missing boundary CSV: {boundary_path}")

    summary_rows = read_summary(summary_path)
    boundary_rows = read_boundary(boundary_path)

    big_order = parse_big_list(args.big_order)
    if big_order is None:
        big_order = sorted(row["big"] for row in summary_rows)

    filtered_summary = [row for row in summary_rows if row["big"] in set(big_order)]
    filtered_summary.sort(key=lambda row: big_order.index(row["big"]))
    filtered_boundary = filter_by_big_order(boundary_rows, big_order)

    boundary_delta_path = (
        args.input_dir / f"{args.output_prefix}_boundary_with_delta.csv"
    )
    write_csv(
        boundary_delta_path,
        [
            "big",
            "from_body",
            "from_residual",
            "from_profile",
            "to_body",
            "to_residual",
            "to_profile",
            "delta_body",
            "delta_residual",
        ],
        filtered_boundary,
    )

    first_rows = make_delta_first_appearance(filtered_boundary, big_order)
    first_path = args.input_dir / f"{args.output_prefix}_delta_first_appearance.csv"
    write_csv(
        first_path,
        ["big", "delta_body_set", "new_delta_body", "cumulative_delta_body"],
        first_rows,
    )

    timeline_rows = make_growth_timeline(filtered_summary, first_rows, big_order)
    timeline_path = args.input_dir / f"{args.output_prefix}_growth_timeline.csv"
    write_csv(
        timeline_path,
        [
            "big",
            "one_candidate",
            "delta_one",
            "two_candidate",
            "delta_two",
            "new_delta_body",
        ],
        timeline_rows,
    )

    print(f"Wrote boundary+deltas -> {boundary_delta_path}")
    print(f"Wrote delta first-appearance -> {first_path}")
    print(f"Wrote growth timeline -> {timeline_path}")


if __name__ == "__main__":
    main()
