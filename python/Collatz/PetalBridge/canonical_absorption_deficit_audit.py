#!/usr/bin/env python3
"""Audit windows attaining the canonical reflected queue maximum.

This is the finite computational companion to the exact Lean theorem
``exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos``.  The
reflected queue carries the start of its currently maximizing suffix, so every
new record stores the complete half-open absorption ledger

    length - claim holes - terminal valuation.

The output is evidence over a finite root and block range.  It does not prove
uniform boundedness, eventual discharge, or any orbit-wide conclusion.
"""

from __future__ import annotations

import csv
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT_MAX = 16383
BLOCK_LIMIT = 4096

# cp-347 diagnostic only.  These counters observe spare successors while a
# root installs a new record window; they deliberately do not change the CSV
# surface inherited from cp-345.
SPARE_SIGN_DIAGNOSTIC = {
    "zero": 0,
    "positive": 0,
    "first_zero": None,
}


def v2(value: int) -> int:
    assert value > 0
    return (value & -value).bit_length() - 1


def accelerated_step(value: int) -> int:
    raw = 3 * value + 1
    return raw >> v2(raw)


def upper_carry(value: int) -> int:
    return (3 * value + 1) >> value.bit_length()


class Orbit:
    def __init__(self, root: int) -> None:
        assert root > 0 and root % 2 == 1
        self.states = [root]

    def state(self, time: int) -> int:
        while len(self.states) <= time:
            self.states.append(accelerated_step(self.states[-1]))
        return self.states[time]

    def exact_depth(self, time: int) -> int:
        return v2(self.state(time) + 1)

    def height(self, time: int) -> int:
        return v2(3 * self.state(time) + 1)

    def target(self, time: int) -> int:
        return time + self.exact_depth(time) - 1


@dataclass
class AuditRow:
    root: int
    blocks_audited: int
    reached_state_one_endpoint: bool
    maximum_queue: int
    terminal_block: int
    witness_start_block: int
    witness_block_count: int
    witness_length: int
    witness_claim_holes: int
    witness_terminal_valuation: int
    witness_absorption_deficit: int
    witness_positive_drift_mass: int
    witness_negative_drift_mass: int
    witness_dynamic_pressure_mass: int
    witness_saturated_count: int
    witness_negative_successor_count: int
    witness_spare_successor_count: int
    witness_zero_rigid_successor_count: int
    witness_tight_rigid_successor_count: int
    witness_terminal_successor_pending_count: int
    witness_spare_carrier_count: int
    witness_rigid_residual_count: int
    witness_selected_depth_histogram: str


def audit_root(root: int) -> AuditRow:
    orbit = Orbit(root)
    endpoint = orbit.target(0)
    previous_endpoint = -1
    queue = 0
    active_start = -1
    maximum_queue = 0
    record = (-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, "")
    prefix_lengths = [0]
    prefix_holes = [0]
    terminal_valuations: list[int] = []
    drifts: list[int] = []
    lengths: list[int] = []
    claims_by_block: list[int] = []
    reached_one = False

    blocks_audited = 0
    for block in range(BLOCK_LIMIT):
        start_time = previous_endpoint + 1
        length = endpoint - start_time + 1
        claims = sum(
            upper_carry(orbit.state(time)) == 2
            for time in range(start_time, endpoint + 1)
        )
        holes = length - claims
        terminal_valuation = orbit.height(endpoint) - 1
        drift = length - holes - terminal_valuation

        prefix_lengths.append(prefix_lengths[-1] + length)
        prefix_holes.append(prefix_holes[-1] + holes)
        terminal_valuations.append(terminal_valuation)
        drifts.append(drift)
        lengths.append(length)
        claims_by_block.append(claims)

        candidate = queue + drift
        if candidate > 0:
            if queue == 0:
                active_start = block
            queue = candidate
        else:
            queue = 0
            active_start = -1

        blocks_audited = block + 1
        if queue > 0:
            # Reflection is inactive inside the current positive excursion.
            # Check every positive queue state, not only record-breaking ones.
            assert active_start >= 0
            active_length = prefix_lengths[block + 1] - prefix_lengths[active_start]
            active_holes = prefix_holes[block + 1] - prefix_holes[active_start]
            active_valuation = sum(terminal_valuations[active_start : block + 1])
            assert active_length - active_holes - active_valuation == queue
            active_drifts = drifts[active_start : block + 1]
            positive_mass = sum(max(value, 0) for value in active_drifts)
            negative_mass = sum(max(-value, 0) for value in active_drifts)
            saturated = [
                index
                for index in range(active_start, block + 1)
                if claims_by_block[index] == lengths[index]
                and drifts[index] > 0
            ]
            dynamic_depths = [
                terminal_valuations[index]
                if index in saturated
                else terminal_valuations[index] - 1
                if terminal_valuations[index] >= 2
                else 0
                for index in range(active_start, block + 1)
                if drifts[index] > 0
            ]
            dynamic_pressure = sum(
                max(lengths[index] - depth, 0)
                - int(1 <= depth <= lengths[index])
                for index, depth in zip(
                    [
                        index
                        for index in range(active_start, block + 1)
                        if drifts[index] > 0
                    ],
                    dynamic_depths,
                    strict=True,
                )
            )
            assert queue == positive_mass - negative_mass
            assert positive_mass <= dynamic_pressure + len(saturated)

        if queue > maximum_queue:
            assert active_start >= 0
            q = active_start
            window_length = prefix_lengths[block + 1] - prefix_lengths[q]
            window_holes = prefix_holes[block + 1] - prefix_holes[q]
            window_valuation = sum(terminal_valuations[q : block + 1])
            deficit = window_length - window_holes - window_valuation
            assert deficit == queue
            window_indices = range(q, block + 1)
            positive_mass = sum(max(drifts[index], 0) for index in window_indices)
            negative_mass = sum(max(-drifts[index], 0) for index in window_indices)
            saturated = [
                index
                for index in window_indices
                if claims_by_block[index] == lengths[index] and drifts[index] > 0
            ]
            positive_indices = [index for index in window_indices if drifts[index] > 0]
            dynamic_depth_by_index = {
                index: terminal_valuations[index]
                if index in saturated
                else terminal_valuations[index] - 1
                if terminal_valuations[index] >= 2
                else 0
                for index in positive_indices
            }
            dynamic_pressure = sum(
                max(lengths[index] - depth, 0)
                - int(1 <= depth <= lengths[index])
                for index, depth in dynamic_depth_by_index.items()
            )
            depth_counts: dict[int, int] = {}
            for depth in dynamic_depth_by_index.values():
                depth_counts[depth] = depth_counts.get(depth, 0) + 1

            negative_successors = 0
            spare_successors = 0
            zero_rigid_successors = 0
            tight_rigid_successors = 0
            spare_carrier_count = 0
            pending = 0
            for index in saturated:
                if index == block:
                    # The successor lies outside the observed window.  Keep
                    # this temporal boundary explicit rather than fabricating
                    # a current-window payment.
                    pending += 1
                    continue
                successor = index + 1
                successor_drift = drifts[successor]
                selected_depth = (
                    1
                    if terminal_valuations[successor] == 1
                    else terminal_valuations[successor] - 1
                )
                selected_card = max(lengths[successor] - (selected_depth + 1), 0)
                successor_saturated = (
                    claims_by_block[successor] == lengths[successor]
                    and successor_drift > 0
                )
                drift_image_card = (
                    successor_drift
                    if successor_drift > 0 and not successor_saturated
                    else 0
                )
                spare_card = selected_card - drift_image_card
                assert spare_card >= 0
                if successor_drift < 0:
                    negative_successors += 1
                elif spare_card > 0:
                    spare_successors += 1
                    spare_carrier_count += spare_card
                    if successor_drift == 0:
                        SPARE_SIGN_DIAGNOSTIC["zero"] += 1
                        if SPARE_SIGN_DIAGNOSTIC["first_zero"] is None:
                            SPARE_SIGN_DIAGNOSTIC["first_zero"] = {
                                "root": root,
                                "window_start": q,
                                "window_end": block,
                                "predecessor": index,
                                "successor": successor,
                                "successor_drift": successor_drift,
                                "spare_card": spare_card,
                            }
                    else:
                        assert successor_drift > 0
                        SPARE_SIGN_DIAGNOSTIC["positive"] += 1
                elif successor_drift == 0 and selected_card == 0:
                    zero_rigid_successors += 1
                else:
                    assert successor_drift > 0
                    assert terminal_valuations[successor] == 1
                    assert claims_by_block[successor] == lengths[successor] - 1
                    tight_rigid_successors += 1
            assert (
                negative_successors
                + spare_successors
                + zero_rigid_successors
                + tight_rigid_successors
                + pending
                == len(saturated)
            )
            maximum_queue = queue
            record = (
                block,
                q,
                block - q + 1,
                window_length,
                window_holes,
                window_valuation,
                deficit,
                positive_mass,
                negative_mass,
                dynamic_pressure,
                len(saturated),
                negative_successors,
                spare_successors,
                zero_rigid_successors,
                tight_rigid_successors,
                pending,
                spare_carrier_count,
                zero_rigid_successors + tight_rigid_successors,
                ";".join(f"{depth}:{count}" for depth, count in sorted(depth_counts.items())),
            )

        if orbit.state(endpoint) == 1:
            reached_one = True
            break

        previous_endpoint = endpoint
        endpoint = orbit.target(endpoint + 1)

    return AuditRow(
        root=root,
        blocks_audited=blocks_audited,
        reached_state_one_endpoint=reached_one,
        maximum_queue=maximum_queue,
        terminal_block=record[0],
        witness_start_block=record[1],
        witness_block_count=record[2],
        witness_length=record[3],
        witness_claim_holes=record[4],
        witness_terminal_valuation=record[5],
        witness_absorption_deficit=record[6],
        witness_positive_drift_mass=record[7],
        witness_negative_drift_mass=record[8],
        witness_dynamic_pressure_mass=record[9],
        witness_saturated_count=record[10],
        witness_negative_successor_count=record[11],
        witness_spare_successor_count=record[12],
        witness_zero_rigid_successor_count=record[13],
        witness_tight_rigid_successor_count=record[14],
        witness_terminal_successor_pending_count=record[15],
        witness_spare_carrier_count=record[16],
        witness_rigid_residual_count=record[17],
        witness_selected_depth_histogram=record[18],
    )


def main() -> None:
    rows = [audit_root(root) for root in range(1, ROOT_MAX + 1, 2)]
    by_root = {row.root: row for row in rows}

    # Regressions inherited from the scalar queue audit, now with exact
    # absorption-window witnesses.
    assert by_root[7].maximum_queue == 1
    assert by_root[511].maximum_queue == 5
    assert all(
        row.maximum_queue == row.witness_absorption_deficit
        for row in rows
        if row.maximum_queue > 0
    )

    output_dir = Path(__file__).with_name("results")
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "canonical_excursion_mass_audit_345.csv"
    md_path = output_dir / "canonical_excursion_mass_audit_345.md"

    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
        writer.writeheader()
        writer.writerows(asdict(row) for row in rows)

    records = sorted(rows, key=lambda row: (-row.maximum_queue, row.root))[:20]
    reached = sum(row.reached_state_one_endpoint for row in rows)
    positive = sum(row.maximum_queue > 0 for row in rows)
    lines = [
        "# Canonical Excursion-Mass Audit (cp-345)",
        "",
        f"Odd roots: `1..{ROOT_MAX}`. Block limit: `{BLOCK_LIMIT}`.",
        "This is finite computational evidence, not a Lean theorem.",
        "",
        "## Summary",
        "",
        f"- roots audited: {len(rows)}",
        f"- roots reaching a state-one canonical endpoint: {reached}",
        f"- roots with a positive observed queue maximum: {positive}",
        f"- largest observed queue/deficit: {max(row.maximum_queue for row in rows)}",
        "- every positive queue state passed its active-window deficit identity",
        "- every positive queue state passed signed-mass decomposition",
        "- every positive queue state passed dynamic-pressure plus saturation domination",
        "- successor classifications cover only observed internal successors",
        "- a saturated terminal block is recorded as pending, not spent from the current window",
        "- the CSV stores the final maximum witness for each root",
        "- no uniform bound or eventual discharge follows from this table",
        "",
        "## Maximum-Deficit Windows",
        "",
        "| root | queue | terminal | start | blocks | length | holes | valuation | deficit |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    lines.extend(
        f"| {row.root} | {row.maximum_queue} | {row.terminal_block} | "
        f"{row.witness_start_block} | {row.witness_block_count} | "
        f"{row.witness_length} | {row.witness_claim_holes} | "
        f"{row.witness_terminal_valuation} | {row.witness_absorption_deficit} |"
        for row in records
    )
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(
        f"roots={len(rows)} reached_one={reached} positive_maximum={positive} "
        f"largest={max(row.maximum_queue for row in rows)}"
    )
    print(
        "record_window_internal_spare_by_successor_drift "
        f"zero={SPARE_SIGN_DIAGNOSTIC['zero']} "
        f"positive={SPARE_SIGN_DIAGNOSTIC['positive']}"
    )
    print(f"first_zero_drift_spare={SPARE_SIGN_DIAGNOSTIC['first_zero']}")
    for row in records[:10]:
        print(row)


if __name__ == "__main__":
    main()
