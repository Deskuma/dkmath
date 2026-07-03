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
    residual_all_ones_depth_seq: str
    residual_all_ones_depth_first: int
    residual_all_ones_depth_last: int
    residual_all_ones_depth_mode: int
    residual_all_ones_depth_max: int
    count_all_ones_depth_ge_4: int
    count_all_ones_depth_ge_5: int
    count_all_ones_depth_ge_6: int
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
    max_retention_drop_minus_2_continuation_drop: int
    sign_change_cause_labels: str
    sign_change_drop_details: str
    sign_change_pressure_decay_details: str
    local_island_pressure_decay_details: str
    margin_step_diff: str
    retention_drop_minus_2_continuation_drop: str
    margin_step_matches_net_drop: str
    margin_step_identity_failure_count: int
    net_drop_positive_count: int
    margin_jump_count: int
    margin_jump_iff_net_drop_failure_count: int
    current_margin: str
    net_drop: str
    current_margin_plus_net_drop: str
    next_margin: str
    crossing_matches_sign_change_up: str
    crossing_identity_failure_count: int
    sign_change_up_iff_crossing_failure_count: int
    sign_change_down_positions: str
    sign_change_down_count: int
    falling_matches_sign_change_down: str
    local_island_right_fall_failure_count: int
    sign_change_down_iff_falling_failure_count: int
    local_pressure_pulse_positions: str
    local_pressure_pulse_count: int
    local_island_to_pulse_failure_count: int
    interval_pulse_blocks: str
    interval_pulse_count: int
    positive_block_without_left_crossing_count: int
    positive_block_without_right_fall_count: int
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


def all_ones_depth(x: int) -> int:
    """Length of the low-bit all-ones suffix of x."""
    return v2(x + 1)


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


def classify_sign_change(retention_drop: int, continuation_drop: int) -> str:
    if retention_drop > 2 * continuation_drop:
        return "retention_drop_dominant"
    if continuation_drop == 0:
        return "continuation_hold"
    if abs(retention_drop - 2 * continuation_drop) <= 1:
        return "balanced"
    return "unclear"


def row_for(n: int, steps: int, r_start: int, depth_len: int) -> PressureSignPatternRow:
    labels, heights_all = orbit_labels_and_heights(n, steps)
    height_seq = heights_all[:steps]
    residual_shape_seq = labels[1 : steps + 1]
    first_failed_depth_seq = [height + 1 for height in height_seq]
    residual_mod_8_seq = [value % 8 for value in residual_shape_seq]
    residual_mod_16_seq = [value % 16 for value in residual_shape_seq]
    residual_mod_32_seq = [value % 32 for value in residual_shape_seq]
    residual_all_ones_depth_seq = [
        all_ones_depth(value) for value in residual_shape_seq
    ]

    depths = list(range(r_start, r_start + depth_len))
    extended_depths = list(range(r_start, r_start + depth_len + 1))
    margins = {depth: margin_at(labels, steps, depth) for depth in extended_depths}
    retentions = {
        depth: retention_mass(labels, steps, depth) for depth in extended_depths
    }
    continuations = {
        depth: continuation_mass(labels, steps, depth) for depth in extended_depths
    }
    margin_step_diffs = {
        depth: margins[depth + 1] - margins[depth] for depth in depths
    }
    retention_drop_minus_2_continuation_drops = {
        depth: (retentions[depth] - retentions[depth + 1])
        - 2 * (continuations[depth] - continuations[depth + 1])
        for depth in depths
    }
    margin_step_matches = {
        depth: margin_step_diffs[depth]
        == retention_drop_minus_2_continuation_drops[depth]
        for depth in depths
    }
    net_drop_positive = {
        depth: 0 < retention_drop_minus_2_continuation_drops[depth]
        for depth in depths
    }
    margin_jump_flags = {
        depth: margins[depth] < margins[depth + 1]
        for depth in depths
    }
    margin_jump_iff_net_drop = {
        depth: margin_jump_flags[depth] == net_drop_positive[depth]
        for depth in depths
    }
    current_margin_plus_net_drop = {
        depth: margins[depth] + retention_drop_minus_2_continuation_drops[depth]
        for depth in depths
    }
    crossing_identity_matches = {
        depth: current_margin_plus_net_drop[depth] == margins[depth + 1]
        for depth in depths
    }
    crossing_flags = {
        depth: margins[depth] <= 0 and 0 < current_margin_plus_net_drop[depth]
        for depth in depths
    }
    sign_change_up_flags = {
        depth: margins[depth] <= 0 and margins[depth + 1] > 0
        for depth in depths
    }
    sign_change_up_iff_crossing = {
        depth: sign_change_up_flags[depth] == crossing_flags[depth]
        for depth in depths
    }
    falling_flags = {
        depth: 0 < margins[depth] and current_margin_plus_net_drop[depth] <= 0
        for depth in depths
    }
    sign_change_down_flags = {
        depth: 0 < margins[depth] and margins[depth + 1] <= 0
        for depth in depths
    }
    sign_change_down_iff_falling = {
        depth: sign_change_down_flags[depth] == falling_flags[depth]
        for depth in depths
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
    sign_change_down = [
        depth
        for depth in depths
        if margins[depth] > 0 and margins[depth + 1] <= 0
    ]
    local_pressure_pulses = [
        depth
        for depth in depths
        if depth > r_start
        and crossing_flags[depth - 1]
        and falling_flags[depth]
    ]
    interval_pulse_blocks = [
        (start, end)
        for start, end in blocks
        if start > r_start
        and crossing_flags[start - 1]
        and falling_flags[end]
    ]
    positive_block_without_left_crossing_count = sum(
        1
        for start, _end in blocks
        if start > r_start and not crossing_flags[start - 1]
    )
    positive_block_without_right_fall_count = sum(
        1 for _start, end in blocks if not falling_flags[end]
    )
    sign_change_details: list[str] = []
    sign_change_pressure_decay_details: list[str] = []
    sign_change_labels: list[str] = []
    retention_drop_minus_2_continuation_drop_values: list[int] = []
    for depth in sign_change_up:
        retention_drop = retentions[depth] - retentions[depth + 1]
        continuation_drop = continuations[depth] - continuations[depth + 1]
        margin_jump = margins[depth + 1] - margins[depth]
        retention_drop_minus_2_continuation_drop = (
            retention_drop - 2 * continuation_drop
        )
        retention_drop_minus_2_continuation_drop_values.append(
            retention_drop_minus_2_continuation_drop
        )
        label = classify_sign_change(retention_drop, continuation_drop)
        sign_change_labels.append(label)
        sign_change_details.append(
            f"{depth}:ret={retention_drop},cont={continuation_drop},"
            f"diff={retention_drop_minus_2_continuation_drop},"
            f"jump={margin_jump},cause={label}"
        )
        sign_change_pressure_decay_details.append(
            f"j={depth},margin_j={margins[depth]},margin_next={margins[depth + 1]},"
            f"margin_jump={margin_jump},retention_j={retentions[depth]},"
            f"retention_next={retentions[depth + 1]},retention_drop={retention_drop},"
            f"continuation_j={continuations[depth]},"
            f"continuation_next={continuations[depth + 1]},"
            f"continuation_drop={continuation_drop},"
            f"retention_drop_minus_2_continuation_drop="
            f"{retention_drop_minus_2_continuation_drop},cause={label}"
        )
    local_island_pressure_decay_details = [
        f"n={n},island_depth={depth},left_edge_j={depth - 1},"
        f"margin_left={margins[depth - 1]},margin_island={margins[depth]},"
        f"margin_right={margins[depth + 1]},"
        f"retention_left={retentions[depth - 1]},"
        f"retention_island={retentions[depth]},"
        f"retention_right={retentions[depth + 1]},"
        f"continuation_left={continuations[depth - 1]},"
        f"continuation_island={continuations[depth]},"
        f"continuation_right={continuations[depth + 1]}"
        for depth in local_islands
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
        residual_all_ones_depth_seq=join_ints(residual_all_ones_depth_seq),
        residual_all_ones_depth_first=(
            residual_all_ones_depth_seq[0] if residual_all_ones_depth_seq else -1
        ),
        residual_all_ones_depth_last=(
            residual_all_ones_depth_seq[-1] if residual_all_ones_depth_seq else -1
        ),
        residual_all_ones_depth_mode=mode_int(residual_all_ones_depth_seq),
        residual_all_ones_depth_max=max(residual_all_ones_depth_seq, default=-1),
        count_all_ones_depth_ge_4=sum(
            1 for value in residual_all_ones_depth_seq if value >= 4
        ),
        count_all_ones_depth_ge_5=sum(
            1 for value in residual_all_ones_depth_seq if value >= 5
        ),
        count_all_ones_depth_ge_6=sum(
            1 for value in residual_all_ones_depth_seq if value >= 6
        ),
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
        max_retention_drop_minus_2_continuation_drop=max(
            retention_drop_minus_2_continuation_drop_values, default=0
        ),
        sign_change_cause_labels=";".join(sign_change_labels),
        sign_change_drop_details=";".join(sign_change_details),
        sign_change_pressure_decay_details=";".join(
            sign_change_pressure_decay_details
        ),
        local_island_pressure_decay_details=";".join(
            local_island_pressure_decay_details
        ),
        margin_step_diff=join_pairs(
            [(depth, margin_step_diffs[depth]) for depth in depths]
        ),
        retention_drop_minus_2_continuation_drop=join_pairs(
            [
                (depth, retention_drop_minus_2_continuation_drops[depth])
                for depth in depths
            ]
        ),
        margin_step_matches_net_drop=";".join(
            f"{depth}:{int(margin_step_matches[depth])}" for depth in depths
        ),
        margin_step_identity_failure_count=sum(
            1 for depth in depths if not margin_step_matches[depth]
        ),
        net_drop_positive_count=sum(
            1 for depth in depths if net_drop_positive[depth]
        ),
        margin_jump_count=sum(1 for depth in depths if margin_jump_flags[depth]),
        margin_jump_iff_net_drop_failure_count=sum(
            1 for depth in depths if not margin_jump_iff_net_drop[depth]
        ),
        current_margin=join_pairs([(depth, margins[depth]) for depth in depths]),
        net_drop=join_pairs(
            [
                (depth, retention_drop_minus_2_continuation_drops[depth])
                for depth in depths
            ]
        ),
        current_margin_plus_net_drop=join_pairs(
            [(depth, current_margin_plus_net_drop[depth]) for depth in depths]
        ),
        next_margin=join_pairs([(depth, margins[depth + 1]) for depth in depths]),
        crossing_matches_sign_change_up=";".join(
            f"{depth}:{int(sign_change_up_iff_crossing[depth])}"
            for depth in depths
        ),
        crossing_identity_failure_count=sum(
            1 for depth in depths if not crossing_identity_matches[depth]
        ),
        sign_change_up_iff_crossing_failure_count=sum(
            1 for depth in depths if not sign_change_up_iff_crossing[depth]
        ),
        sign_change_down_positions=join_ints(sign_change_down),
        sign_change_down_count=len(sign_change_down),
        falling_matches_sign_change_down=";".join(
            f"{depth}:{int(sign_change_down_iff_falling[depth])}"
            for depth in depths
        ),
        local_island_right_fall_failure_count=sum(
            1 for depth in local_islands if not sign_change_down_flags[depth]
        ),
        sign_change_down_iff_falling_failure_count=sum(
            1 for depth in depths if not sign_change_down_iff_falling[depth]
        ),
        local_pressure_pulse_positions=join_ints(local_pressure_pulses),
        local_pressure_pulse_count=len(local_pressure_pulses),
        local_island_to_pulse_failure_count=sum(
            1 for depth in local_islands if depth not in local_pressure_pulses
        ),
        interval_pulse_blocks=join_blocks(interval_pulse_blocks),
        interval_pulse_count=len(interval_pulse_blocks),
        positive_block_without_left_crossing_count=(
            positive_block_without_left_crossing_count
        ),
        positive_block_without_right_fall_count=(
            positive_block_without_right_fall_count
        ),
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


def count_label_field(rows: list[PressureSignPatternRow], field_name: str) -> Counter[str]:
    counter: Counter[str] = Counter()
    for row in rows:
        raw = getattr(row, field_name)
        if not raw:
            continue
        for value in raw.split(";"):
            if value:
                counter[value] += 1
    return counter


def markdown_kv_counter(counter: Counter[int]) -> str:
    return "; ".join(f"{key}:{counter[key]}" for key in sorted(counter))


def markdown_label_counter(counter: Counter[str]) -> str:
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
    max_margin_jump = max((row.max_margin_jump for row in rows), default=0)
    max_retention_drop = max((row.max_retention_drop for row in rows), default=0)
    max_continuation_drop = max(
        (row.max_continuation_drop for row in rows), default=0
    )
    max_retention_drop_minus_2_continuation_drop = max(
        (
            row.max_retention_drop_minus_2_continuation_drop
            for row in rows
        ),
        default=0,
    )
    rows_with_margin_step_identity_failure = sum(
        1 for row in rows if row.margin_step_identity_failure_count > 0
    )
    rows_with_net_drop_positive = sum(
        1 for row in rows if row.net_drop_positive_count > 0
    )
    rows_with_margin_jump = sum(1 for row in rows if row.margin_jump_count > 0)
    rows_with_margin_jump_iff_net_drop_failure = sum(
        1 for row in rows if row.margin_jump_iff_net_drop_failure_count > 0
    )
    rows_with_crossing_identity_failure = sum(
        1 for row in rows if row.crossing_identity_failure_count > 0
    )
    rows_with_sign_change_up_iff_crossing_failure = sum(
        1 for row in rows if row.sign_change_up_iff_crossing_failure_count > 0
    )
    rows_with_sign_change_down = sum(
        1 for row in rows if row.sign_change_down_count > 0
    )
    rows_with_local_island_right_fall_failure = sum(
        1 for row in rows if row.local_island_right_fall_failure_count > 0
    )
    rows_with_sign_change_down_iff_falling_failure = sum(
        1 for row in rows if row.sign_change_down_iff_falling_failure_count > 0
    )
    rows_with_local_pressure_pulse = sum(
        1 for row in rows if row.local_pressure_pulse_count > 0
    )
    rows_with_local_island_to_pulse_failure = sum(
        1 for row in rows if row.local_island_to_pulse_failure_count > 0
    )
    rows_with_interval_pulse = sum(
        1 for row in rows if row.interval_pulse_count > 0
    )
    rows_with_positive_block_without_left_crossing = sum(
        1 for row in rows
        if row.positive_block_without_left_crossing_count > 0
    )
    rows_with_positive_block_without_right_fall = sum(
        1 for row in rows
        if row.positive_block_without_right_fall_count > 0
    )
    rows_with_interval_pulse_left_crossing_failure = (
        rows_with_positive_block_without_left_crossing
    )
    rows_with_interval_pulse_right_falling_failure = (
        rows_with_positive_block_without_right_fall
    )
    all_ones_first_counts = Counter(
        row.residual_all_ones_depth_first
        for row in rows
        if row.residual_all_ones_depth_first >= 0
    )
    all_ones_mode_counts = Counter(
        row.residual_all_ones_depth_mode
        for row in rows
        if row.residual_all_ones_depth_mode >= 0
    )
    all_ones_max_counts = Counter(
        row.residual_all_ones_depth_max
        for row in rows
        if row.residual_all_ones_depth_max >= 0
    )
    cause_counts = count_label_field(rows, "sign_change_cause_labels")
    top_pressure = sorted(
        nonempty,
        key=lambda row: (-row.positive_depth_count, -row.frontier_margin, row.n),
    )[:12]
    top_all_ones = sorted(
        rows,
        key=lambda row: (
            -row.residual_all_ones_depth_max,
            -row.max_positive_block_length,
            row.n,
        ),
    )[:12]
    top_islands = sorted(
        with_island,
        key=lambda row: (-row.local_island_count, -row.sign_change_up_count, row.n),
    )[:12]
    sign_samples = sorted(
        with_sign_change,
        key=lambda row: (-row.sign_change_up_count, -row.max_margin_jump, row.n),
    )[:12]
    retention_drop_samples = sorted(
        with_sign_change,
        key=lambda row: (-row.max_retention_drop, -row.max_margin_jump, row.n),
    )[:12]

    lines = [
        "# Collatz Pressure Sign Pattern Scan",
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
        f"- largest margin jump: `{max_margin_jump}`",
        f"- largest retention drop: `{max_retention_drop}`",
        f"- largest continuation drop: `{max_continuation_drop}`",
        "- largest retention drop minus 2 continuation drop: "
        f"`{max_retention_drop_minus_2_continuation_drop}`",
        "- rows_with_margin_step_identity_failure: "
        f"`{rows_with_margin_step_identity_failure}`",
        f"- rows_with_net_drop_positive: `{rows_with_net_drop_positive}`",
        f"- rows_with_margin_jump: `{rows_with_margin_jump}`",
        "- rows_with_margin_jump_iff_net_drop_failure: "
        f"`{rows_with_margin_jump_iff_net_drop_failure}`",
        "- rows_with_crossing_identity_failure: "
        f"`{rows_with_crossing_identity_failure}`",
        "- rows_with_sign_change_up_iff_crossing_failure: "
        f"`{rows_with_sign_change_up_iff_crossing_failure}`",
        f"- rows_with_sign_change_down: `{rows_with_sign_change_down}`",
        "- rows_with_local_island_right_fall_failure: "
        f"`{rows_with_local_island_right_fall_failure}`",
        "- rows_with_sign_change_down_iff_falling_failure: "
        f"`{rows_with_sign_change_down_iff_falling_failure}`",
        f"- rows_with_local_pressure_pulse: `{rows_with_local_pressure_pulse}`",
        "- rows_with_local_island_to_pulse_failure: "
        f"`{rows_with_local_island_to_pulse_failure}`",
        f"- rows_with_interval_pulse: `{rows_with_interval_pulse}`",
        "- rows_with_positive_block_without_left_crossing: "
        f"`{rows_with_positive_block_without_left_crossing}`",
        "- rows_with_positive_block_without_right_fall: "
        f"`{rows_with_positive_block_without_right_fall}`",
        "- rows_with_interval_pulse_left_crossing_failure: "
        f"`{rows_with_interval_pulse_left_crossing_failure}`",
        "- rows_with_interval_pulse_right_falling_failure: "
        f"`{rows_with_interval_pulse_right_falling_failure}`",
        "- interval-pulse convention: left crossing is checked only for blocks "
        "with `start > r_start`; blocks beginning at the observed left boundary "
        "do not expose their previous depth in this scan.",
        f"- positive block length counts: `{markdown_kv_counter(block_length_counts)}`",
        f"- all-ones depth first counts: `{markdown_kv_counter(all_ones_first_counts)}`",
        f"- all-ones depth mode counts: `{markdown_kv_counter(all_ones_mode_counts)}`",
        f"- all-ones depth max counts: `{markdown_kv_counter(all_ones_max_counts)}`",
        f"- sign-change cause counts: `{markdown_label_counter(cause_counts)}`",
        "",
        "## Top Positive-Depth Samples",
        "",
        "| n | positive depths | blocks | max block | all-ones max | frontier | frontier margin | islands | sign-up | margins |",
        "|---:|---|---|---:|---:|---:|---:|---|---|---|",
    ]
    for row in top_pressure:
        lines.append(
            "| "
            f"{row.n} | {row.positive_depths} | {row.positive_blocks} | "
            f"{row.max_positive_block_length} | {row.residual_all_ones_depth_max} | "
            f"{row.first_frontier_depth} | {row.frontier_margin} | "
            f"{row.local_islands} | {row.sign_change_up_positions} | "
            f"{row.margin_profile} |"
        )

    lines.extend(
        [
            "",
            "## Deepest All-Ones Samples",
            "",
            "| n | all-ones depths | max | counts ge4/ge5/ge6 | max block | positive blocks | residual mod 32 |",
            "|---:|---|---:|---|---:|---|---|",
        ]
    )
    for row in top_all_ones:
        lines.append(
            "| "
            f"{row.n} | {row.residual_all_ones_depth_seq} | "
            f"{row.residual_all_ones_depth_max} | "
            f"{row.count_all_ones_depth_ge_4}/"
            f"{row.count_all_ones_depth_ge_5}/"
            f"{row.count_all_ones_depth_ge_6} | "
            f"{row.max_positive_block_length} | {row.positive_blocks} | "
            f"{row.residual_mod_32_seq} |"
        )

    lines.extend(
        [
            "",
            "## Local-Island Samples",
            "",
            "| n | islands | first sign-change pair | sign-up | causes | height seq | first-failed seq | all-ones depths | residual mod 16 |",
            "|---:|---|---|---|---|---|---|---|---|",
        ]
    )
    if top_islands:
        for row in top_islands:
            lines.append(
                "| "
                f"{row.n} | {row.local_islands} | {row.first_sign_change_pair} | "
                f"{row.sign_change_up_positions} | {row.sign_change_cause_labels} | "
                f"{row.height_seq} | {row.first_failed_depth_seq} | "
                f"{row.residual_all_ones_depth_seq} | {row.residual_mod_16_seq} |"
            )
    else:
        lines.append("| - | none observed | - | - | - | - | - | - | - |")

    lines.extend(
        [
            "",
            "## Sign-Change-Up Samples",
            "",
            "| n | sign-up | causes | margin jump | retention drop | continuation drop | drop details | margins | retentions | continuations |",
            "|---:|---|---|---:|---:|---:|---|---|---|---|",
        ]
    )
    if sign_samples:
        for row in sign_samples:
            lines.append(
                "| "
                f"{row.n} | {row.sign_change_up_positions} | "
                f"{row.sign_change_cause_labels} | "
                f"{row.max_margin_jump} | {row.max_retention_drop} | "
                f"{row.max_continuation_drop} | {row.sign_change_drop_details} | "
                f"{row.margin_profile} | {row.retention_profile} | "
                f"{row.continuation_profile} |"
            )
    else:
        lines.append("| - | none observed | - | 0 | 0 | 0 | - | - | - | - |")

    lines.extend(
        [
            "",
            "## Largest Retention-Drop Sign-Change Samples",
            "",
            "| n | sign-up | causes | retention drop | continuation drop | drop details | all-ones depths |",
            "|---:|---|---|---:|---:|---|---|",
        ]
    )
    if retention_drop_samples:
        for row in retention_drop_samples:
            lines.append(
                "| "
                f"{row.n} | {row.sign_change_up_positions} | "
                f"{row.sign_change_cause_labels} | {row.max_retention_drop} | "
                f"{row.max_continuation_drop} | {row.sign_change_drop_details} | "
                f"{row.residual_all_ones_depth_seq} |"
            )
    else:
        lines.append("| - | none observed | - | 0 | 0 | - | - |")

    lines.extend(
        [
            "",
            "## PressureDecay: Sign-Change-Up Rows",
            "",
            "| n | sign-change-up pressure-decay details |",
            "|---:|---|",
        ]
    )
    if with_sign_change:
        for row in with_sign_change:
            lines.append(
                f"| {row.n} | {row.sign_change_pressure_decay_details} |"
            )
    else:
        lines.append("| - | none observed |")

    lines.extend(
        [
            "",
            "## PressureDecay: Local-Island Rows",
            "",
            "| n | local-island pressure-decay details |",
            "|---:|---|",
        ]
    )
    if with_island:
        for row in with_island:
            lines.append(
                f"| {row.n} | {row.local_island_pressure_decay_details} |"
            )
    else:
        lines.append("| - | none observed |")

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
            "Checkpoint 132 adds the direct all-ones-depth observable",
            "`v2(residual + 1)`.  This separates the previous residue-class signal",
            "from the actual low-bit all-ones concentration inside the window.",
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
        "Positive Block Length By All-Ones Depth First",
        table_count_by(rows, "residual_all_ones_depth_first", "max_positive_block_length"),
        "all-ones depth first",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By All-Ones Depth Mode",
        table_count_by(rows, "residual_all_ones_depth_mode", "max_positive_block_length"),
        "all-ones depth mode",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By All-Ones Depth Max",
        table_count_by(rows, "residual_all_ones_depth_max", "max_positive_block_length"),
        "all-ones depth max",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By Count All-Ones Depth Ge 4",
        table_count_by(rows, "count_all_ones_depth_ge_4", "max_positive_block_length"),
        "count all-ones depth ge 4",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By Count All-Ones Depth Ge 5",
        table_count_by(rows, "count_all_ones_depth_ge_5", "max_positive_block_length"),
        "count all-ones depth ge 5",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Positive Block Length By Count All-Ones Depth Ge 6",
        table_count_by(rows, "count_all_ones_depth_ge_6", "max_positive_block_length"),
        "count all-ones depth ge 6",
        "max block length counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By All-Ones Depth First",
        table_count_by(rows, "residual_all_ones_depth_first", "first_frontier_depth", True),
        "all-ones depth first",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By All-Ones Depth Max",
        table_count_by(rows, "residual_all_ones_depth_max", "first_frontier_depth", True),
        "all-ones depth max",
        "frontier depth counts",
    )
    append_distribution_table(
        lines,
        "Frontier Depth By Count All-Ones Depth Ge 4",
        table_count_by(rows, "count_all_ones_depth_ge_4", "first_frontier_depth", True),
        "count all-ones depth ge 4",
        "frontier depth counts",
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
    append_distribution_table(
        lines,
        "Local Island Rows By All-Ones Depth First",
        table_count_by(with_island, "residual_all_ones_depth_first", "local_island_count"),
        "all-ones depth first",
        "local island count rows",
    )
    append_distribution_table(
        lines,
        "Local Island Rows By All-Ones Depth Max",
        table_count_by(with_island, "residual_all_ones_depth_max", "local_island_count"),
        "all-ones depth max",
        "local island count rows",
    )
    append_distribution_table(
        lines,
        "Local Island Rows By Count All-Ones Depth Ge 4",
        table_count_by(with_island, "count_all_ones_depth_ge_4", "local_island_count"),
        "count all-ones depth ge 4",
        "local island count rows",
    )
    append_distribution_table(
        lines,
        "Sign-Change-Up Rows By All-Ones Depth First",
        table_count_by(
            with_sign_change,
            "residual_all_ones_depth_first",
            "sign_change_up_count",
        ),
        "all-ones depth first",
        "sign-change-up count rows",
    )
    append_distribution_table(
        lines,
        "Sign-Change-Up Rows By All-Ones Depth Max",
        table_count_by(
            with_sign_change,
            "residual_all_ones_depth_max",
            "sign_change_up_count",
        ),
        "all-ones depth max",
        "sign-change-up count rows",
    )
    append_distribution_table(
        lines,
        "Sign-Change-Up Rows By Count All-Ones Depth Ge 4",
        table_count_by(
            with_sign_change,
            "count_all_ones_depth_ge_4",
            "sign_change_up_count",
        ),
        "count all-ones depth ge 4",
        "sign-change-up count rows",
    )
    lines.extend(
        [
            "",
            "## Sign-Change-Up Depth Counts",
            "",
            f"- depth counts: `{markdown_kv_counter(count_list_field(rows, 'sign_change_up_positions'))}`",
            f"- cause counts: `{markdown_label_counter(cause_counts)}`",
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
    parser.add_argument(
        "--name-suffix",
        default="",
        help="Optional suffix for output files, for example '_8191_k64'.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = scan(args.max_n, args.steps, args.r_start, args.depth_len)
    csv_path = args.out_dir / f"pressure_sign_pattern_scan{args.name_suffix}.csv"
    summary_path = args.out_dir / f"pressure_sign_pattern_scan{args.name_suffix}.md"
    write_csv(rows, csv_path)
    write_summary(rows, summary_path)
    print(f"wrote {csv_path}")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
