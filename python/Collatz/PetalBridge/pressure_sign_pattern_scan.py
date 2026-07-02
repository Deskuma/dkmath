#!/usr/bin/env python3
"""Scan Collatz time profiles against pressure-depth sign patterns.

Checkpoint 130 returns from the one-dimensional Lean list API to experimental
pressure observation.  This script keeps the two axes visible:

* time index i:
  height_i, residual_i, first_failed_i
* pressure-depth index j:
  margin_j, selected_j, frontier_j, island_j

The output is observational data.  It is intended to guide the next Lean
predicate, not to assert a global pressure monotonicity theorem.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from collections import Counter, defaultdict
from pathlib import Path


@dataclass(frozen=True)
class PressureSignPatternRow:
    n: int
    steps: int
    r_start: int
    depth_len: int
    height_seq: str
    residual_shape_seq: str
    first_failed_depth_seq: str
    residual_mod_8_seq: str
    residual_mod_16_seq: str
    residual_mod_32_seq: str
    positive_depths: str
    positive_blocks: str
    positive_depth_count: int
    first_frontier_depth: int
    frontier_margin: int
    local_islands: str
    local_island_count: int
    sign_change_up_positions: str
    sign_change_up_count: int
    first_sign_change_pair: str
    residual_mod_16_first: int
    residual_mod_16_last: int
    residual_mod_16_mode: int
    residual_mod_32_first: int
    residual_mod_32_last: int
    residual_mod_32_mode: int
    max_positive_block_length: int
    max_margin_jump: int
    max_retention_drop: int
    max_continuation_drop: int
    margin_profile: str
    retention_profile: str
    continuation_profile: str


def join_ints(values: list[int]) -> str:
    return ";".join(str(value) for value in values)


def join_pairs(values: list[tuple[int, int]]) -> str:
    return ";".join(f"{left}:{right}" for left, right in values)


def join_blocks(blocks: list[tuple[int, int]]) -> str:
    return ";".join(
        f"{start}-{end}" if start != end else str(start) for start, end in blocks
    )


def mode_int(values: list[int]) -> int:
    if not values:
        return -1
    counts = Counter(values)
    return min(
        counts,
        key=lambda value: (-counts[value], value),
    )


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
        current, height = accelerated_step(current)
        heights.append(height)
    return labels, heights


def count_residue(values: list[int], modulus: int, residue: int) -> int:
    return sum(1 for value in values if value % modulus == residue)


def retention_mass(labels: list[int], steps: int, depth: int) -> int:
    return count_residue(labels[:steps], 2**depth, 2**depth - 1)


def continuation_mass(labels: list[int], steps: int, depth: int) -> int:
    return count_residue(labels[:steps], 2 ** (depth + 1), 2 ** (depth + 1) - 1)


def margin_at(labels: list[int], steps: int, depth: int) -> int:
    return 2 * continuation_mass(labels, steps, depth) - retention_mass(labels, steps, depth)


def consecutive_blocks(depths: list[int]) -> list[tuple[int, int]]:
    if not depths:
        return []
    blocks: list[tuple[int, int]] = []
    start = depths[0]
    prev = depths[0]
    for depth in depths[1:]:
        if depth == prev + 1:
            prev = depth
        else:
            blocks.append((start, prev))
            start = depth
            prev = depth
    blocks.append((start, prev))
    return blocks


def first_sign_change_pair(depths: list[int], r_start: int) -> tuple[int, int] | None:
    selected = set(depths)
    if not depths:
        return None
    for depth in range(r_start, max(depths)):
        if depth not in selected and depth + 1 in selected:
            return (depth, depth + 1)
    return None


def max_adjacent_drop(values: dict[int, int], depths: list[int]) -> int:
    drops = [values[d] - values[d + 1] for d in depths[:-1]]
    return max(drops, default=0)


def max_adjacent_jump(values: dict[int, int], depths: list[int]) -> int:
    jumps = [abs(values[d + 1] - values[d]) for d in depths[:-1]]
    return max(jumps, default=0)


def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPatternRow:
    labels, heights_all = orbit_labels_and_heights(n, steps)
    height_seq = heights_all[:steps]
    residual_shape_seq = labels[1 : steps + 1]
    first_failed_depth_seq = [height + 1 for height in height_seq]
    residual_mod_8_seq = [value % 8 for value in residual_shape_seq]
    residual_mod_16_seq = [value % 16 for value in residual_shape_seq]
    residual_mod_32_seq = [value % 32 for value in residual_shape_seq]

    depths = list(range(r_start, r_start + depth_len))
    extended_depths = list(range(r_start, r_start + depth_len + 1))
    margins = {depth: margin_at(labels, steps, depth) for depth in extended_depths}
    retentions = {
        depth: retention_mass(labels, steps, depth) for depth in extended_depths
    }
    continuations = {
        depth: continuation_mass(labels, steps, depth) for depth in extended_depths
    }
    positive_depths = [depth for depth in depths if margins[depth] > 0]
    blocks = consecutive_blocks(positive_depths)
    frontier = positive_depths[0] if positive_depths else -1
    frontier_margin = margins[frontier] if frontier >= 0 else 0
    local_islands = [
        depth
        for depth in depths
        if depth > r_start and margins[depth] > 0 and margins[depth - 1] <= 0 and margins[depth + 1] <= 0
    ]
    sign_change_up = [
        depth
        for depth in depths
        if margins[depth] <= 0 and margins[depth + 1] > 0
    ]
    sign_change_pair = first_sign_change_pair(positive_depths, r_start)
    block_lengths = [end - start + 1 for start, end in blocks]

    return PressureSignPatternRow(
        n=n,
        steps=steps,
        r_start=r_start,
        depth_len=depth_len,
        height_seq=join_ints(height_seq),
        residual_shape_seq=join_ints(residual_shape_seq),
        first_failed_depth_seq=join_ints(first_failed_depth_seq),
        residual_mod_8_seq=join_ints(residual_mod_8_seq),
        residual_mod_16_seq=join_ints(residual_mod_16_seq),
        residual_mod_32_seq=join_ints(residual_mod_32_seq),
        positive_depths=join_ints(positive_depths),
        positive_blocks=join_blocks(blocks),
        positive_depth_count=len(positive_depths),
        first_frontier_depth=frontier,
        frontier_margin=frontier_margin,
        local_islands=join_ints(local_islands),
        local_island_count=len(local_islands),
        sign_change_up_positions=join_ints(sign_change_up),
        sign_change_up_count=len(sign_change_up),
        first_sign_change_pair=(
            "" if sign_change_pair is None else f"{sign_change_pair[0]}->{sign_change_pair[1]}"
        ),
        residual_mod_16_first=residual_mod_16_seq[0] if residual_mod_16_seq else -1,
        residual_mod_16_last=residual_mod_16_seq[-1] if residual_mod_16_seq else -1,
        residual_mod_16_mode=mode_int(residual_mod_16_seq),
        residual_mod_32_first=residual_mod_32_seq[0] if residual_mod_32_seq else -1,
        residual_mod_32_last=residual_mod_32_seq[-1] if residual_mod_32_seq else -1,
        residual_mod_32_mode=mode_int(residual_mod_32_seq),
        max_positive_block_length=max(block_lengths, default=0),
        max_margin_jump=max_adjacent_jump(margins, depths),
        max_retention_drop=max_adjacent_drop(retentions, depths),
        max_continuation_drop=max_adjacent_drop(continuations, depths),
        margin_profile=join_pairs([(depth, margins[depth]) for depth in depths]),
        retention_profile=join_pairs([(depth, retentions[depth]) for depth in depths]),
        continuation_profile=join_pairs(
            [(depth, continuations[depth]) for depth in depths]
        ),
    )


def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[PressureSignPatternRow]:
    return [row_for(n, steps, r_start, depth_len) for n in range(1, max_n + 1, 2)]


def write_csv(rows: list[PressureSignPatternRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=list(PressureSignPatternRow.__dataclass_fields__),
            lineterminator="\n",
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def table_count_by(
    rows: list[PressureSignPatternRow],
    key_name: str,
    value_name: str,
    only_positive: bool = False,
) -> list[tuple[int, str]]:
    bucket: dict[int, Counter[int]] = defaultdict(Counter)
    for row in rows:
        if only_positive and row.positive_depth_count == 0:
            continue
        key = getattr(row, key_name)
        value = getattr(row, value_name)
        if value >= 0:
            bucket[key][value] += 1
    return [
        (key, ";".join(f"{value}:{count}" for value, count in sorted(counter.items())))
        for key, counter in sorted(bucket.items())
    ]


def count_list_field(rows: list[PressureSignPatternRow], field_name: str) -> Counter[int]:
    counter: Counter[int] = Counter()
    for row in rows:
        raw = getattr(row, field_name)
        if not raw:
            continue
        for value in raw.split(";"):
            if value:
                counter[int(value)] += 1
    return counter


def markdown_kv_counter(counter: Counter[int]) -> str:
    return "; ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def append_distribution_table(
    lines: list[str],
    title: str,
    rows: list[tuple[int, str]],
    key_label: str,
    value_label: str,
) -> None:
    lines.extend(["", f"## {title}", "", f"| {key_label} | {value_label} |", "|---:|---|"])
    if rows:
        for key, value in rows:
            lines.append(f"| {key} | {value} |")
    else:
        lines.append("| - | none |")


def write_summary(rows: list[PressureSignPatternRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nonempty = [row for row in rows if row.positive_depth_count > 0]
    with_island = [row for row in rows if row.local_island_count > 0]
    with_sign_change = [row for row in rows if row.sign_change_up_count > 0]
    block_rows_len_ge_1 = [row for row in rows if row.max_positive_block_length >= 1]
    block_rows_len_ge_2 = [row for row in rows if row.max_positive_block_length >= 2]
    block_rows_len_ge_4 = [row for row in rows if row.max_positive_block_length >= 4]
    block_length_counts = Counter(
        row.max_positive_block_length
        for row in rows
        if row.max_positive_block_length > 0
    )
    max_positive = max((row.positive_depth_count for row in rows), default=0)
    max_islands = max((row.local_island_count for row in rows), default=0)
    max_sign_changes = max((row.sign_change_up_count for row in rows), default=0)
    top_pressure = sorted(
        nonempty,
        key=lambda row: (-row.positive_depth_count, -row.frontier_margin, row.n),
    )[:12]
    top_islands = sorted(
        with_island,
        key=lambda row: (-row.local_island_count, -row.sign_change_up_count, row.n),
    )[:12]
    sign_samples = sorted(
        with_sign_change,
        key=lambda row: (-row.sign_change_up_count, -row.max_margin_jump, row.n),
    )[:12]

    lines = [
        "# Collatz Pressure Sign Pattern Scan - Checkpoint 130",
        "",
        f"- rows: `{len(rows)}`",
        f"- rows with positive pressure depths: `{len(nonempty)}`",
        f"- rows with local islands: `{len(with_island)}`",
        f"- rows with sign-change-up positions: `{len(with_sign_change)}`",
        "- positive block definition: `maximal consecutive positive-depth run, length >= 1`",
        f"- rows with positive blocks length >= 1: `{len(block_rows_len_ge_1)}`",
        f"- rows with positive blocks length >= 2: `{len(block_rows_len_ge_2)}`",
        f"- rows with positive blocks length >= 4: `{len(block_rows_len_ge_4)}`",
        f"- max positive depth count: `{max_positive}`",
        f"- max local island count: `{max_islands}`",
        f"- max sign-change-up count: `{max_sign_changes}`",
        f"- positive block length counts: `{markdown_kv_counter(block_length_counts)}`",
        "",
        "## Top Positive-Depth Samples",
        "",
        "| n | positive depths | blocks | frontier | frontier margin | islands | sign-up | margins |",
        "|---:|---|---|---:|---:|---|---|---|",
    ]
    for row in top_pressure:
        lines.append(
            "| "
            f"{row.n} | {row.positive_depths} | {row.positive_blocks} | "
            f"{row.first_frontier_depth} | {row.frontier_margin} | "
            f"{row.local_islands} | {row.sign_change_up_positions} | "
            f"{row.margin_profile} |"
        )

    lines.extend(
        [
            "",
            "## Local-Island Samples",
            "",
            "| n | islands | first sign-change pair | sign-up | height seq | first-failed seq | residual mod 16 |",
            "|---:|---|---|---|---|---|---|",
        ]
    )
    if top_islands:
        for row in top_islands:
            lines.append(
                "| "
                f"{row.n} | {row.local_islands} | {row.first_sign_change_pair} | "
                f"{row.sign_change_up_positions} | {row.height_seq} | "
                f"{row.first_failed_depth_seq} | {row.residual_mod_16_seq} |"
            )
    else:
        lines.append("| - | none observed | - | - | - | - | - |")

    lines.extend(
        [
            "",
            "## Sign-Change-Up Samples",
            "",
            "| n | sign-up | margin jump | retention drop | continuation drop | margins | retentions | continuations |",
            "|---:|---|---:|---:|---:|---|---|---|",
        ]
    )
    if sign_samples:
        for row in sign_samples:
            lines.append(
                "| "
                f"{row.n} | {row.sign_change_up_positions} | "
                f"{row.max_margin_jump} | {row.max_retention_drop} | "
                f"{row.max_continuation_drop} | {row.margin_profile} | "
                f"{row.retention_profile} | {row.continuation_profile} |"
            )
    else:
        lines.append("| - | none observed | 0 | 0 | 0 | - | - | - |")

    lines.extend(
        [
            "",
            "## Reading",
            "",
            "The scan keeps time profiles and pressure-depth profiles separate.  The",
            "current data should be used to decide whether the next Lean predicate is a",
            "positive block, a local-island existence predicate, or a frontier-below",
            "predicate.",
            "",
            "This is not evidence for an unconditional pressure-prefix theorem.  The",
            "presence of local islands and sign-change-up rows means pressure is a",
            "margin sign profile, not just carrier nesting.",
            "",
        ]
    )
    append_distribution_table(
        lines,
        "Frontier Depth By Residual Mod 16 First",
        table_count_by(rows, "residual_mod_16_first", "first_frontier_depth", True),
        "residual mod 16 first",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By Residual Mod 16 Mode",
        table_count_by(rows, "residual_mod_16_mode", "first_frontier_depth", True),
        "residual mod 16 mode",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By Residual Mod 32 First",
        table_count_by(rows, "residual_mod_32_first", "first_frontier_depth", True),
        "residual mod 32 first",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By Residual Mod 32 Mode",
        table_count_by(rows, "residual_mod_32_mode", "first_frontier_depth", True),
        "residual mod 32 mode",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By Residual Mod 16 First",
        table_count_by(rows, "residual_mod_16_first", "max_positive_block_length"),
        "residual mod 16 first",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By Residual Mod 32 First",
        table_count_by(rows, "residual_mod_32_first", "max_positive_block_length"),
        "residual mod 32 first",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Local Island Rows By Residual Mod 16 First",
        table_count_by(with_island, "residual_mod_16_first", "local_island_count"),
        "residual mod 16 first",
        "local island count rows",
    )
    append_distribution_table(
        lines,
        "Sign-Change-Up Rows By Residual Mod 16 First",
        table_count_by(with_sign_change, "residual_mod_16_first", "sign_change_up_count"),
        "residual mod 16 first",
        "sign-change-up count rows",
    )
    lines.extend(
        [
            "",
            "## Sign-Change-Up Depth Counts",
            "",
            f"- depth counts: `{markdown_kv_counter(count_list_field(rows, 'sign_change_up_positions'))}`",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=511)
    parser.add_argument("--steps", type=int, default=64)
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
    csv_path = args.out_dir / "pressure_sign_pattern_scan.csv"
    summary_path = args.out_dir / "pressure_sign_pattern_scan.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
