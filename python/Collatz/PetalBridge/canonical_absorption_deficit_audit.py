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


def audit_root(root: int) -> AuditRow:
    orbit = Orbit(root)
    endpoint = orbit.target(0)
    previous_endpoint = -1
    queue = 0
    active_start = -1
    maximum_queue = 0
    record = (-1, -1, 0, 0, 0, 0, 0)
    prefix_lengths = [0]
    prefix_holes = [0]
    terminal_valuations: list[int] = []
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

        candidate = queue + drift
        if candidate > 0:
            if queue == 0:
                active_start = block
            queue = candidate
        else:
            queue = 0
            active_start = -1

        blocks_audited = block + 1
        if queue > maximum_queue:
            assert active_start >= 0
            q = active_start
            window_length = prefix_lengths[block + 1] - prefix_lengths[q]
            window_holes = prefix_holes[block + 1] - prefix_holes[q]
            window_valuation = sum(terminal_valuations[q : block + 1])
            deficit = window_length - window_holes - window_valuation
            assert deficit == queue
            maximum_queue = queue
            record = (
                block,
                q,
                block - q + 1,
                window_length,
                window_holes,
                window_valuation,
                deficit,
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
    csv_path = output_dir / "canonical_absorption_deficit_audit_343.csv"
    md_path = output_dir / "canonical_absorption_deficit_audit_343.md"

    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
        writer.writeheader()
        writer.writerows(asdict(row) for row in rows)

    records = sorted(rows, key=lambda row: (-row.maximum_queue, row.root))[:20]
    reached = sum(row.reached_state_one_endpoint for row in rows)
    positive = sum(row.maximum_queue > 0 for row in rows)
    lines = [
        "# Canonical Absorption-Deficit Audit (cp-343)",
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
        "- every positive record is attained by the displayed finite window",
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
    for row in records[:10]:
        print(row)


if __name__ == "__main__":
    main()
