#!/usr/bin/env python3
"""Finite audit of the canonical depth/level repayment candidate.

This mirrors the Lean definitions used by UniversalPaymentDepthLedger:

* the state at time i is the i-th accelerated odd state;
* exact depth is v2(state + 1);
* endpoint height is v2(3 * state + 1);
* canonical endpoints iterate target(i) = i + exact_depth(i) - 1;
* every carry-two source in a block produces its endpoint-relative depth;
* an endpoint of height h exposes one slot at every level in [2, h].

The candidate eligibility rule sends depth one and depth two to level two,
and every delayed depth d >= 3 to level d, at the same or a later block.
The script is evidence only.  It does not turn a finite audit into a theorem.
"""

from __future__ import annotations

import csv
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


ROOTS = (7, 27, 31, 511)
CLAIM_BLOCKS = 1024
HORIZON_BLOCKS = 4096


def v2(value: int) -> int:
    assert value > 0
    return (value & -value).bit_length() - 1


def accelerated_step(value: int) -> int:
    raw = 3 * value + 1
    return raw >> v2(raw)


def bit_width(value: int) -> int:
    return value.bit_length()


def upper_carry(value: int) -> int:
    return (3 * value + 1) >> bit_width(value)


@dataclass(frozen=True)
class Claim:
    block: int
    depth: int

    @property
    def required_level(self) -> int:
        return 2 if self.depth <= 2 else self.depth


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


def canonical_endpoints(orbit: Orbit, count: int) -> list[int]:
    endpoints = [orbit.target(0)]
    while len(endpoints) < count:
        endpoints.append(orbit.target(endpoints[-1] + 1))
    return endpoints


def block_claims(orbit: Orbit, endpoints: list[int], block: int) -> list[Claim]:
    start = 0 if block == 0 else endpoints[block - 1] + 1
    endpoint = endpoints[block]
    return [
        Claim(block, endpoint - time + 1)
        for time in range(start, endpoint + 1)
        if upper_carry(orbit.state(time)) == 2
    ]


def audit_root(root: int) -> dict[str, int | bool]:
    orbit = Orbit(root)
    endpoints = canonical_endpoints(orbit, HORIZON_BLOCKS)
    claims_by_block = [
        block_claims(orbit, endpoints, block) for block in range(HORIZON_BLOCKS)
    ]

    prefix_queues: dict[int, deque[Claim]] = defaultdict(deque)
    stream_queues: dict[int, deque[Claim]] = defaultdict(deque)
    prefix_claims = 0
    prefix_paid = 0
    max_prefix_lag = 0
    max_stream_total = 0
    max_stream_level_two = 0
    collisions = 0
    collisions_one_level_two_slot = 0
    first_collision = "none"

    for block in range(HORIZON_BLOCKS):
        claims = claims_by_block[block]
        depths = {claim.depth for claim in claims}
        if 1 in depths and 2 in depths:
            collisions += 1
            if first_collision == "none":
                first_collision = (
                    f"b{block}:endpoint{endpoints[block]}:"
                    f"height{orbit.height(endpoints[block])}"
                )
            if orbit.height(endpoints[block]) == 2:
                collisions_one_level_two_slot += 1

        for claim in claims:
            stream_queues[claim.required_level].append(claim)
            if block < CLAIM_BLOCKS:
                prefix_queues[claim.required_level].append(claim)
                prefix_claims += 1

        for level in range(2, orbit.height(endpoints[block]) + 1):
            if prefix_queues[level]:
                claim = prefix_queues[level].popleft()
                prefix_paid += 1
                max_prefix_lag = max(max_prefix_lag, block - claim.block)
            if stream_queues[level]:
                stream_queues[level].popleft()

        max_stream_total = max(max_stream_total, sum(map(len, stream_queues.values())))
        max_stream_level_two = max(max_stream_level_two, len(stream_queues[2]))

    prefix_outstanding = sum(map(len, prefix_queues.values()))
    stream_outstanding = sum(map(len, stream_queues.values()))
    first_state_one_time = next(
        (time for time, state in enumerate(orbit.states) if state == 1), -1
    )
    prefix_outstanding_detail = ";".join(
        f"b{claim.block}:d{claim.depth}->l{level}"
        for level in sorted(prefix_queues)
        for claim in prefix_queues[level]
    )
    return {
        "root": root,
        "claim_blocks": CLAIM_BLOCKS,
        "horizon_blocks": HORIZON_BLOCKS,
        "prefix_claims": prefix_claims,
        "prefix_paid": prefix_paid,
        "prefix_outstanding": prefix_outstanding,
        "prefix_outstanding_detail": prefix_outstanding_detail or "none",
        "first_state_one_time": first_state_one_time,
        "prefix_max_lag": max_prefix_lag,
        "stream_outstanding": stream_outstanding,
        "stream_max_total_queue": max_stream_total,
        "stream_max_level_two_queue": max_stream_level_two,
        "depth1_depth2_collisions": collisions,
        "collisions_with_one_level_two_slot": collisions_one_level_two_slot,
        "first_depth1_depth2_collision": first_collision,
        "prefix_candidate_survived": prefix_outstanding == 0,
    }


def main() -> None:
    seven = Orbit(7)
    seven_endpoints = canonical_endpoints(seven, 2)
    assert [claim.depth for claim in block_claims(seven, seven_endpoints, 0)] == [3, 2]
    assert [claim.depth for claim in block_claims(seven, seven_endpoints, 1)] == [1]
    assert list(range(2, seven.height(seven_endpoints[0]) + 1)) == [2]
    assert list(range(2, seven.height(seven_endpoints[1]) + 1)) == [2, 3]

    rows = [audit_root(root) for root in ROOTS]
    output_dir = Path(__file__).with_name("results")
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "canonical_depth_eligibility_audit_315.csv"
    md_path = output_dir / "canonical_depth_eligibility_audit_315.md"

    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    headers = list(rows[0])
    lines = [
        "# Canonical Depth Eligibility Audit (cp-315)",
        "",
        f"Claim prefix: {CLAIM_BLOCKS} blocks. Capacity horizon: {HORIZON_BLOCKS} blocks.",
        "This is finite computational evidence, not a Lean theorem.",
        "",
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    lines.extend(
        "| " + " | ".join(str(row[key]) for key in headers) + " |" for row in rows
    )
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
