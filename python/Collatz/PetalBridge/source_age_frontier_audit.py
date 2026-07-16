#!/usr/bin/env python3
"""cp-337 bounded discovery audit for canonical source-age frontier flow.

The output is theorem-discovery evidence only.  It intentionally tracks actual
scalar-queue consumption rather than endpoint capacity, and it never promotes
a finite maximum or repayment lag to a universal claim.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT_MAX = 4095
BLOCK_LIMIT = 256
HORIZONS = range(5)
WINDOW_LENGTHS = range(1, 9)


def v2(value: int) -> int:
    assert value > 0
    return (value & -value).bit_length() - 1


def step(value: int) -> int:
    raw = 3 * value + 1
    return raw >> v2(raw)


def carry_two(value: int) -> bool:
    return (3 * value + 1) >> value.bit_length() == 2


class Orbit:
    def __init__(self, root: int) -> None:
        self.states = [root]

    def state(self, time: int) -> int:
        while len(self.states) <= time:
            self.states.append(step(self.states[-1]))
        return self.states[time]

    def target(self, time: int) -> int:
        return time + v2(self.state(time) + 1) - 1


def trace(root: int) -> list[dict[str, int | bool]]:
    orbit = Orbit(root)
    endpoint = orbit.target(0)
    previous_endpoint = -1
    queue = 0
    blocks: list[dict[str, int | bool]] = []
    for index in range(BLOCK_LIMIT):
        start = previous_endpoint + 1
        claims = sum(carry_two(orbit.state(i)) for i in range(start, endpoint + 1))
        service = v2(3 * orbit.state(endpoint) + 1) - 1
        consumed = min(queue + claims, service)
        length = endpoint - start + 1
        blocks.append(
            {
                "index": index,
                "start": start,
                "next_start": endpoint + 1,
                "claims": claims,
                "service": service,
                "consumed": consumed,
                "saturated": length == service + 1 and claims == length and service == 1,
            }
        )
        queue = queue + claims - consumed
        if orbit.state(endpoint) == 1:
            break
        previous_endpoint = endpoint
        endpoint = orbit.target(endpoint + 1)
    return blocks


def frontier(orbit: Orbit, block: dict[str, int | bool], horizon: int) -> int:
    low = max(0, int(block["start"]) - horizon)
    high = max(0, int(block["next_start"]) - horizon)
    arrivals = sum(carry_two(orbit.state(i)) for i in range(low, high))
    return arrivals - int(block["consumed"])


def main() -> None:
    summary: dict[str, object] = {
        "checkpoint": 337,
        "root_max": ROOT_MAX,
        "block_limit": BLOCK_LIMIT,
        "horizons": list(HORIZONS),
        "window_lengths": list(WINDOW_LENGTHS),
        "results": {},
    }
    results: dict[str, object] = {}
    for horizon in HORIZONS:
        max_increment = (-10**9, None)
        max_prefix = (-10**9, None)
        max_window = {length: (-10**9, None) for length in WINDOW_LENGTHS}
        saturated_patterns = []
        shortest_returns = []
        two_block_counterexample = None
        for root in range(1, ROOT_MAX + 1, 2):
            orbit = Orbit(root)
            blocks = trace(root)
            increments = [frontier(orbit, block, horizon) for block in blocks]
            prefix = 0
            for index, increment in enumerate(increments):
                if increment > max_increment[0]:
                    max_increment = (increment, [root, index])
                prefix += increment
                if prefix > max_prefix[0]:
                    max_prefix = (prefix, [root, index])
                for length in WINDOW_LENGTHS:
                    if index + length <= len(increments):
                        total = sum(increments[index : index + length])
                        if total > max_window[length][0]:
                            max_window[length] = (total, [root, index])
                if bool(blocks[index]["saturated"]):
                    pattern = increments[index : index + 8]
                    saturated_patterns.append([root, index, pattern])
                    running = 0
                    return_length = None
                    for offset, value in enumerate(increments[index:], start=1):
                        running += value
                        if running <= 0:
                            return_length = offset
                            break
                    if return_length is not None:
                        shortest_returns.append(return_length)
                    if (
                        two_block_counterexample is None
                        and len(pattern) >= 2
                        and sum(pattern[:2]) > 0
                    ):
                        two_block_counterexample = [root, index, pattern[:2]]
        results[str(horizon)] = {
            "maximum_frontier_increment": max_increment,
            "maximum_prefix_frontier_sum": max_prefix,
            "maximum_window_sums": {
                str(length): value for length, value in max_window.items()
            },
            "saturated_blocks_observed": len(saturated_patterns),
            "shortest_observed_return": min(shortest_returns, default=None),
            "longest_observed_return": max(shortest_returns, default=None),
            "two_block_nonpositive_counterexample": two_block_counterexample,
            "first_saturated_patterns": saturated_patterns[:12],
        }
    summary["results"] = results
    output = Path(__file__).with_name("results") / "source_age_frontier_audit_337.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
