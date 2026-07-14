#!/usr/bin/env python3
"""cp-318 finite audit of consecutive saturated canonical blocks.

This script tests the rigid exception isolated by Lean:

    L = v + 1, claims = L, drift = 1.

It records successor data and repayment behavior over the same exhaustive and
deterministic random root families as the cp-317 normal-form audit.  Results
are computational evidence only; they do not establish a universal successor
grammar.
"""

from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path

from canonical_block_normal_form_audit import (
    EXHAUSTIVE_MAX,
    RANDOM_PER_WIDTH,
    RANDOM_SEED,
    RANDOM_WIDTHS,
    block_trace,
    odd_with_exact_width,
)


def saturated(block: dict[str, int]) -> bool:
    return (
        block["length"] == block["terminal_valuation"] + 1
        and block["claims"] == block["length"]
        and block["drift"] == 1
    )


def audit_traces(traces: list[list[dict[str, int]]]) -> dict[str, object]:
    saturated_count = 0
    maximum_run = 0
    transition_counter: Counter[tuple[int, ...]] = Counter()
    successor_positive = 0
    successor_nonpositive = 0
    consecutive_pairs = 0
    runs_without_later_nonpositive = 0
    maximum_blocks_to_nonpositive = 0
    first_two_consecutive = None
    saturated_lengths: Counter[int] = Counter()
    saturated_core_mod_8: Counter[int] = Counter()

    for blocks in traces:
        i = 0
        while i < len(blocks):
            if not saturated(blocks[i]):
                i += 1
                continue
            start = i
            while i < len(blocks) and saturated(blocks[i]):
                saturated_count += 1
                saturated_lengths[blocks[i]["length"]] += 1
                saturated_core_mod_8[blocks[i]["core"] % 8] += 1
                if i + 1 < len(blocks):
                    nxt = blocks[i + 1]
                    transition_counter[
                        (
                            blocks[i]["length"],
                            blocks[i]["core"] % 256,
                            nxt["length"],
                            nxt["terminal_valuation"],
                            nxt["drift"],
                        )
                    ] += 1
                    if nxt["drift"] <= 0:
                        successor_nonpositive += 1
                    else:
                        successor_positive += 1
                    if saturated(nxt):
                        consecutive_pairs += 1
                        if first_two_consecutive is None:
                            first_two_consecutive = {
                                "root_start_state": blocks[0]["start_state"],
                                "left_block": blocks[i],
                                "right_block": nxt,
                            }
                i += 1

            run_length = i - start
            maximum_run = max(maximum_run, run_length)
            repayment = next(
                (j for j in range(i, len(blocks)) if blocks[j]["drift"] <= 0),
                None,
            )
            if repayment is None:
                runs_without_later_nonpositive += 1
            else:
                maximum_blocks_to_nonpositive = max(
                    maximum_blocks_to_nonpositive, repayment - i + 1
                )

    most_common = [
        {
            "length": key[0],
            "core_mod_256": key[1],
            "next_length": key[2],
            "next_terminal_valuation": key[3],
            "next_drift": key[4],
            "count": count,
        }
        for key, count in transition_counter.most_common(40)
    ]
    return {
        "saturated_blocks": saturated_count,
        "maximum_consecutive_saturated_length": maximum_run,
        "consecutive_saturated_pairs": consecutive_pairs,
        "saturated_successor_nonpositive_drift": successor_nonpositive,
        "saturated_successor_positive_drift": successor_positive,
        "runs_without_observed_later_nonpositive_drift": runs_without_later_nonpositive,
        "maximum_blocks_to_first_nonpositive_drift_after_run": maximum_blocks_to_nonpositive,
        "first_two_consecutive_saturated": first_two_consecutive,
        "saturated_length_counts": dict(sorted(saturated_lengths.items())),
        "saturated_core_mod_8_counts": dict(sorted(saturated_core_mod_8.items())),
        "most_common_transitions": most_common,
    }


def main() -> None:
    exhaustive_roots = list(range(1, EXHAUSTIVE_MAX + 1, 2))
    rng = random.Random(RANDOM_SEED)
    random_roots = [
        odd_with_exact_width(rng, width)
        for width in RANDOM_WIDTHS
        for _ in range(RANDOM_PER_WIDTH)
    ]
    traces = [block_trace(root) for root in exhaustive_roots + random_roots]
    result = {
        "checkpoint": 318,
        "exhaustive_odd_roots": len(exhaustive_roots),
        "exhaustive_max": EXHAUSTIVE_MAX,
        "random_seed": RANDOM_SEED,
        "random_roots": len(random_roots),
        "random_widths": list(RANDOM_WIDTHS),
        **audit_traces(traces),
    }

    output_dir = Path(__file__).with_name("results")
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "saturated_block_audit_318.json"
    md_path = output_dir / "saturated_block_audit_318.md"
    json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    lines = [
        "# Saturated Canonical Block Audit (cp-318)",
        "",
        "Finite computational evidence only; no universal successor theorem is inferred.",
        "",
        "## Range",
        "",
        f"- exhaustive odd roots: `{len(exhaustive_roots)}` through `{EXHAUSTIVE_MAX}`",
        f"- deterministic random roots: `{len(random_roots)}` over `{RANDOM_WIDTHS}`",
        f"- random seed: `{RANDOM_SEED}`",
        "",
        "## Saturated runs",
        "",
        f"- saturated blocks: `{result['saturated_blocks']}`",
        f"- maximum consecutive saturated length: `{result['maximum_consecutive_saturated_length']}`",
        f"- consecutive saturated pairs: `{result['consecutive_saturated_pairs']}`",
        f"- saturated length counts: `{result['saturated_length_counts']}`",
        f"- saturated odd-core residues mod 8: `{result['saturated_core_mod_8_counts']}`",
        f"- immediate successor drift nonpositive: `{result['saturated_successor_nonpositive_drift']}`",
        f"- immediate successor drift positive: `{result['saturated_successor_positive_drift']}`",
        f"- runs without a later observed nonpositive drift: `{result['runs_without_observed_later_nonpositive_drift']}`",
        f"- maximum blocks to first later nonpositive drift: `{result['maximum_blocks_to_first_nonpositive_drift_after_run']}`",
        "",
        "A positive successor or a consecutive saturated pair refutes the simplest",
        "`saturated -> next drift <= 0` candidate.  Even a clean finite row would",
        "remain evidence rather than a Lean theorem.",
    ]
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
