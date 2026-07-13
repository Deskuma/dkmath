#!/usr/bin/env python3
"""Finite audit of the anonymous canonical scalar repayment queue.

This mirrors UniversalPaymentScalarQueue.lean.  Every carry-two source is one
claim, every endpoint contributes ``height - 1`` fungible service slots, and
unused service is discarded.  No recovery-depth/capacity-level eligibility is
used.

The generated data is finite evidence.  In particular, it does not prove a
uniform queue bound, a uniform repayment lag, or convergence of any orbit.
"""

from __future__ import annotations

import csv
from collections import Counter
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
    state_one_endpoint_block: int
    queue_at_state_one_endpoint: int
    maximum_queue: int
    first_return_to_zero_after_positive: int
    longest_positive_excursion: int
    final_queue: int
    max_queue_block: int
    max_queue_block_length: int
    max_queue_block_claims: int
    max_queue_block_capacity: int
    max_queue_block_drift: int
    max_queue_endpoint_height: int
    max_queue_claim_depth_histogram: str


def depth_histogram(depths: list[int]) -> str:
    counts = Counter(depths)
    return ";".join(f"d{depth}:{counts[depth]}" for depth in sorted(counts)) or "none"


def audit_root(root: int) -> AuditRow:
    orbit = Orbit(root)
    endpoint = orbit.target(0)
    previous_endpoint = -1
    queue = 0
    maximum_queue = 0
    first_return = -1
    positive_run = 0
    longest_positive = 0
    has_been_positive = False
    state_one_block = -1
    queue_at_state_one = -1
    max_features = (-1, 0, 0, 0, 0, 0, "none")

    blocks_audited = 0
    for block in range(BLOCK_LIMIT):
        start = previous_endpoint + 1
        depths = [
            endpoint - time + 1
            for time in range(start, endpoint + 1)
            if upper_carry(orbit.state(time)) == 2
        ]
        claims = len(depths)
        height = orbit.height(endpoint)
        capacity = height - 1
        drift = claims - capacity
        queue = max(0, queue + drift)
        blocks_audited = block + 1

        if queue > 0:
            has_been_positive = True
            positive_run += 1
            longest_positive = max(longest_positive, positive_run)
        else:
            if has_been_positive and first_return < 0:
                first_return = block
            positive_run = 0

        if queue > maximum_queue:
            maximum_queue = queue
            max_features = (
                block,
                endpoint - start + 1,
                claims,
                capacity,
                drift,
                height,
                depth_histogram(depths),
            )

        if orbit.state(endpoint) == 1 and state_one_block < 0:
            state_one_block = block
            queue_at_state_one = queue
            break

        previous_endpoint = endpoint
        endpoint = orbit.target(endpoint + 1)

    return AuditRow(
        root=root,
        blocks_audited=blocks_audited,
        reached_state_one_endpoint=state_one_block >= 0,
        state_one_endpoint_block=state_one_block,
        queue_at_state_one_endpoint=queue_at_state_one,
        maximum_queue=maximum_queue,
        first_return_to_zero_after_positive=first_return,
        longest_positive_excursion=longest_positive,
        final_queue=queue,
        max_queue_block=max_features[0],
        max_queue_block_length=max_features[1],
        max_queue_block_claims=max_features[2],
        max_queue_block_capacity=max_features[3],
        max_queue_block_drift=max_features[4],
        max_queue_endpoint_height=max_features[5],
        max_queue_claim_depth_histogram=max_features[6],
    )


def main() -> None:
    rows = [audit_root(root) for root in range(1, ROOT_MAX + 1, 2)]

    # Exact scalar regressions mirrored by Lean.
    by_root = {row.root: row for row in rows}
    assert by_root[7].maximum_queue == 1
    assert by_root[511].maximum_queue == 5
    assert by_root[511].first_return_to_zero_after_positive == 2

    output_dir = Path(__file__).with_name("results")
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "canonical_scalar_queue_audit_316.csv"
    md_path = output_dir / "canonical_scalar_queue_audit_316.md"

    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
        writer.writeheader()
        writer.writerows(asdict(row) for row in rows)

    reached = [row for row in rows if row.reached_state_one_endpoint]
    queue_records = sorted(rows, key=lambda row: (-row.maximum_queue, row.root))[:20]
    excursion_records = sorted(
        rows, key=lambda row: (-row.longest_positive_excursion, row.root)
    )[:20]
    nonzero_at_one = [row for row in reached if row.queue_at_state_one_endpoint != 0]

    lines = [
        "# Canonical Scalar Queue Audit (cp-316)",
        "",
        f"Odd roots: `1..{ROOT_MAX}`. Block limit: `{BLOCK_LIMIT}`.",
        "This is finite computational evidence, not a Lean theorem.",
        "",
        "## Summary",
        "",
        f"- roots audited: {len(rows)}",
        f"- roots reaching a state-one canonical endpoint: {len(reached)}",
        f"- roots with nonzero queue there: {len(nonzero_at_one)}",
        f"- largest observed queue: {max(row.maximum_queue for row in rows)}",
        "- no uniform bound or uniform repayment lag follows from this table",
        "",
        "## Queue Records",
        "",
        "| root | max queue | block | length | claims | capacity | drift | height | depths |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    lines.extend(
        f"| {row.root} | {row.maximum_queue} | {row.max_queue_block} | "
        f"{row.max_queue_block_length} | {row.max_queue_block_claims} | "
        f"{row.max_queue_block_capacity} | {row.max_queue_block_drift} | "
        f"{row.max_queue_endpoint_height} | {row.max_queue_claim_depth_histogram} |"
        for row in queue_records
    )
    lines.extend(
        [
            "",
            "## Positive-Excursion Records",
            "",
            "| root | longest positive blocks | first return block | max queue | queue at one |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    lines.extend(
        f"| {row.root} | {row.longest_positive_excursion} | "
        f"{row.first_return_to_zero_after_positive} | {row.maximum_queue} | "
        f"{row.queue_at_state_one_endpoint} |"
        for row in excursion_records
    )
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"roots={len(rows)} reached_one={len(reached)} nonzero_at_one={len(nonzero_at_one)}")
    print("queue records:")
    for row in queue_records[:10]:
        print(row)
    print("positive excursion records:")
    for row in excursion_records[:10]:
        print(row)


if __name__ == "__main__":
    main()
