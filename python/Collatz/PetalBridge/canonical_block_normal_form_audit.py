#!/usr/bin/env python3
"""cp-317 audit for canonical block normal form and queue-bound candidates.

The script validates the exact ``(L, u) -> oddPart(3^L*u - 1)`` transition,
checks the experimental queue/initial-width inequality, and measures collisions
in deliberately finite block signatures.  Its output is computational evidence,
not a Lean proof.
"""

from __future__ import annotations

import json
import random
from collections import defaultdict
from pathlib import Path

from canonical_scalar_queue_audit import BLOCK_LIMIT, Orbit, audit_root, upper_carry, v2


EXHAUSTIVE_MAX = 131_071
RANDOM_SEED = 0xD317
RANDOM_PER_WIDTH = 256
RANDOM_WIDTHS = (64, 128, 256, 512, 1024)
SIGNATURE_WIDTHS = (5, 6, 7, 8)


def odd_with_exact_width(rng: random.Random, width: int) -> int:
    return rng.getrandbits(width - 1) | (1 << (width - 1)) | 1


def block_trace(root: int) -> list[dict[str, int]]:
    orbit = Orbit(root)
    endpoint = orbit.target(0)
    previous_endpoint = -1
    queue = 0
    blocks: list[dict[str, int]] = []
    for block in range(BLOCK_LIMIT):
        start = previous_endpoint + 1
        x = orbit.state(start)
        length = v2(x + 1)
        assert endpoint == start + length - 1
        core = (x + 1) >> length
        assert core & 1 == 1
        terminal = pow(3, length) * core - 1
        terminal_valuation = v2(terminal)
        next_state = terminal >> terminal_valuation
        assert orbit.state(endpoint + 1) == next_state

        claims = sum(
            upper_carry(orbit.state(time)) == 2
            for time in range(start, endpoint + 1)
        )
        capacity = orbit.height(endpoint) - 1
        assert capacity == terminal_valuation
        drift = claims - capacity
        queue = max(0, queue + drift)
        blocks.append(
            {
                "block": block,
                "start": start,
                "endpoint": endpoint,
                "start_state": x,
                "length": length,
                "core": core,
                "terminal_valuation": terminal_valuation,
                "claims": claims,
                "capacity": capacity,
                "drift": drift,
                "queue": queue,
                "next_state": next_state,
            }
        )
        if orbit.state(endpoint) == 1:
            break
        previous_endpoint = endpoint
        endpoint = orbit.target(endpoint + 1)
    return blocks


def top_bits(value: int, width: int) -> int:
    shift = max(0, value.bit_length() - width)
    return value >> shift


def signature(block: dict[str, int], width: int) -> tuple[int, ...]:
    """A finite candidate signature; capped fields intentionally lose data."""
    cap = width
    return (
        min(block["length"], cap),
        block["core"] % (1 << width),
        top_bits(block["start_state"], width),
        min(block["terminal_valuation"], cap),
        min(block["claims"], cap),
    )


def signature_summary(traces: list[list[dict[str, int]]], width: int) -> dict[str, int]:
    drifts: dict[tuple[int, ...], set[int]] = defaultdict(set)
    successors: dict[tuple[int, ...], set[tuple[int, ...]]] = defaultdict(set)
    repeated_positive_segments = 0
    for blocks in traces:
        sigs = [signature(block, width) for block in blocks]
        prefix = [0]
        for block in blocks:
            prefix.append(prefix[-1] + block["drift"])
        positions: dict[tuple[int, ...], list[int]] = defaultdict(list)
        for i, (sig, block) in enumerate(zip(sigs, blocks)):
            drifts[sig].add(block["drift"])
            positions[sig].append(i)
            if i + 1 < len(sigs):
                successors[sig].add(sigs[i + 1])
        for indices in positions.values():
            for left, right in zip(indices, indices[1:]):
                if prefix[right] - prefix[left] > 0:
                    repeated_positive_segments += 1
    return {
        "signature_width": width,
        "distinct_signatures": len(drifts),
        "drift_collision_signatures": sum(len(values) > 1 for values in drifts.values()),
        "largest_observed_drift_spread": max(
            (max(values) - min(values) for values in drifts.values()), default=0
        ),
        "nondeterministic_successor_signatures": sum(
            len(values) > 1 for values in successors.values()
        ),
        "realized_repeated_signature_positive_segments": repeated_positive_segments,
    }


def main() -> None:
    exhaustive_rows = []
    first_counterexample = None
    for root in range(1, EXHAUSTIVE_MAX + 1, 2):
        row = audit_root(root)
        exhaustive_rows.append(row)
        if row.maximum_queue > root.bit_length() and first_counterexample is None:
            first_counterexample = {
                "root": root,
                "initial_width": root.bit_length(),
                "maximum_queue": row.maximum_queue,
            }

    rng = random.Random(RANDOM_SEED)
    random_roots = [
        odd_with_exact_width(rng, width)
        for width in RANDOM_WIDTHS
        for _ in range(RANDOM_PER_WIDTH)
    ]
    random_rows = [audit_root(root) for root in random_roots]
    for root, row in zip(random_roots, random_rows):
        if row.maximum_queue > root.bit_length() and first_counterexample is None:
            first_counterexample = {
                "root": root,
                "initial_width": root.bit_length(),
                "maximum_queue": row.maximum_queue,
            }

    # A representative deterministic subset is enough for collision diagnostics.
    trace_roots = list(range(1, 16_384, 2)) + random_roots
    traces = [block_trace(root) for root in trace_roots]
    sig_summaries = [signature_summary(traces, width) for width in SIGNATURE_WIDTHS]

    all_rows = exhaustive_rows + random_rows
    queue_record = max(all_rows, key=lambda row: (row.maximum_queue, -row.root))
    result = {
        "checkpoint": 317,
        "exhaustive_odd_roots": len(exhaustive_rows),
        "exhaustive_max": EXHAUSTIVE_MAX,
        "random_seed": RANDOM_SEED,
        "random_roots": len(random_roots),
        "random_widths": list(RANDOM_WIDTHS),
        "block_limit": BLOCK_LIMIT,
        "normal_form_trace_roots": len(trace_roots),
        "normal_form_assertions": "passed",
        "initial_width_candidate_first_counterexample": first_counterexample,
        "largest_observed_queue": queue_record.maximum_queue,
        "largest_observed_queue_root": queue_record.root,
        "largest_observed_queue_root_width": queue_record.root.bit_length(),
        "signature_summaries": sig_summaries,
    }

    output_dir = Path(__file__).with_name("results")
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "canonical_block_normal_form_audit_317.json"
    md_path = output_dir / "canonical_block_normal_form_audit_317.md"
    json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    counterexample_text = (
        "none observed" if first_counterexample is None else f"`{first_counterexample}`"
    )
    lines = [
        "# Canonical Block Normal-Form Audit (cp-317)",
        "",
        "This is finite computational evidence, not a Lean theorem.",
        "",
        "## Range",
        "",
        f"- exhaustive odd roots: `1..{EXHAUSTIVE_MAX}` ({len(exhaustive_rows)} roots)",
        f"- deterministic random roots: {len(random_roots)} over widths {RANDOM_WIDTHS}",
        f"- random seed: `{RANDOM_SEED}`",
        f"- per-root block limit: `{BLOCK_LIMIT}`",
        f"- exact normal-form trace roots: `{len(trace_roots)}`",
        "",
        "## Results",
        "",
        "- every audited block passed the exact normal-form transition assertions",
        f"- first `queue > initial bitWidth` counterexample: {counterexample_text}",
        f"- largest observed queue: `{queue_record.maximum_queue}` at root `{queue_record.root}` "
        f"(initial width `{queue_record.root.bit_length()}`)",
        "",
        "## Finite Signature Diagnostics",
        "",
        "| w | signatures | drift collisions | max drift spread | nondeterministic successors | realized positive repeated segments |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    lines.extend(
        f"| {item['signature_width']} | {item['distinct_signatures']} | "
        f"{item['drift_collision_signatures']} | {item['largest_observed_drift_spread']} | "
        f"{item['nondeterministic_successor_signatures']} | "
        f"{item['realized_repeated_signature_positive_segments']} |"
        for item in sig_summaries
    )
    lines.extend(
        [
            "",
            "The candidate signatures use capped length, capped terminal valuation, capped claim count,",
            "the low `w` core bits, and the high `w` start-state bits.  A collision or nondeterministic",
            "successor is evidence that this projection is not an exact automaton state.  Absence of an",
            "observed collision would still not establish projection soundness.",
        ]
    )
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
