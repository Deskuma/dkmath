#!/usr/bin/env python3
"""Evaluate repair-height preservation on exact flip-sector chambers."""

from __future__ import annotations

import argparse
import json
import os
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import repair_depth_search as rds


def one_height_job(job: dict) -> dict:
    payload = json.loads(Path(job["witness"]).read_text(encoding="utf-8"))
    tri = rds.triangulation_from_witness(payload)
    tri.apply_flip(tuple(int(x) for x in job["move"]))
    colored = {int(k): int(v) for k, v in job["colored_state"].items()}
    remaining = {int(v) for v in job["remaining"]}
    profile = rds.repair_maze_from_explicit_state(
        tri,
        colored=colored,
        remaining=remaining,
        current=int(job["node"]),
        max_depth=int(job["max_depth"]),
        node_limit=int(job["node_limit"]),
        intermediate_policy=str(job["intermediate_policy"]),
    )
    return {
        "neighbor_index": int(job["neighbor_index"]),
        "state_index": int(job["state_index"]),
        "profile": profile,
    }


def projection_key(projection: dict, mutable: list[int]) -> tuple[int, ...]:
    return tuple(int(projection[str(v)]) for v in mutable)


def parse_indices(raw: str | None) -> set[int] | None:
    if raw is None:
        return None
    return {
        int(piece.strip())
        for piece in raw.split(",")
        if piece.strip()
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness")
    parser.add_argument("--source-component-summary", required=True)
    parser.add_argument("--flip-census-summary", required=True)
    parser.add_argument("--indices")
    parser.add_argument("--step", type=int, default=16)
    parser.add_argument("--prefix-depth", type=int, default=10)
    parser.add_argument("--max-depth", type=int, default=11)
    parser.add_argument("--node-limit", type=int, default=6_000_000)
    parser.add_argument("--state-limit", type=int, default=512)
    parser.add_argument(
        "--workers", type=int, default=max(1, (os.cpu_count() or 2) - 1)
    )
    parser.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    parser.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/sector-height-census",
    )
    args = parser.parse_args()

    source = Path(args.witness)
    payload = json.loads(source.read_text(encoding="utf-8"))
    parent = json.loads(
        Path(args.source_component_summary).read_text(encoding="utf-8")
    )
    census = json.loads(
        Path(args.flip_census_summary).read_text(encoding="utf-8")
    )

    requested = parse_indices(args.indices)
    selected = [
        row
        for row in census["neighbors"]
        if row.get("comparison_available")
        and row.get("child_matches_child_admissible_sector")
        and (requested is None or int(row["index"]) in requested)
    ]
    if requested is not None:
        found = {int(row["index"]) for row in selected}
        missing = sorted(requested - found)
        if missing:
            raise SystemExit(
                "requested indices are not exact child-admissible sectors: "
                + ",".join(str(x) for x in missing)
            )

    parent_mutable = [int(v) for v in parent["mutable_vertices"]]
    parent_by_key = {
        projection_key(row["projection"], parent_mutable): row
        for row in parent["states"]
    }

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    jobs: list[dict] = []
    metadata: dict[int, dict] = {}

    for row in selected:
        neighbor_index = int(row["index"])
        tri = rds.triangulation_from_witness(payload)
        move = tuple(int(x) for x in row["move"])
        tri.apply_flip(move)
        prefix = rds.restore_state_before_step(
            tri,
            args.step,
            max_repair_depth=args.prefix_depth,
            node_limit=args.node_limit,
            intermediate_policy=args.intermediate_policy,
        )
        component = rds.enumerate_admissible_component_static(
            tri,
            prefix,
            state_limit=args.state_limit,
        )
        child_mutable = [int(v) for v in component["mutable_vertices"]]
        if child_mutable != parent_mutable:
            raise SystemExit(
                f"neighbor {neighbor_index} mutable coordinates differ"
            )

        base_state = {
            int(k): int(v)
            for k, v in component["baseline_colored_state"].items()
        }
        state_parent_map: dict[int, int] = {}

        for child_state in component["states"]:
            key = projection_key(child_state["projection"], parent_mutable)
            parent_state = parent_by_key.get(key)
            if parent_state is None:
                raise SystemExit(
                    f"neighbor {neighbor_index} child state "
                    f"{child_state['index']} not found in parent component"
                )
            child_index = int(child_state["index"])
            parent_index = int(parent_state["index"])
            state_parent_map[child_index] = parent_index

            colored = dict(base_state)
            for v in child_mutable:
                colored[v] = int(child_state["projection"][str(v)])

            jobs.append(
                {
                    "neighbor_index": neighbor_index,
                    "state_index": child_index,
                    "witness": str(source),
                    "move": list(move),
                    "colored_state": {
                        str(v): int(c)
                        for v, c in sorted(colored.items())
                    },
                    "remaining": component["remaining"],
                    "node": component["node"],
                    "max_depth": args.max_depth,
                    "node_limit": args.node_limit,
                    "intermediate_policy": args.intermediate_policy,
                }
            )

        metadata[neighbor_index] = {
            "row": row,
            "component": component,
            "state_parent_map": state_parent_map,
        }

    started = time.time()
    print(
        f"neighbors={len(selected)} states={len(jobs)} workers={args.workers}",
        flush=True,
    )

    results: dict[tuple[int, int], dict] = {}
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {
            pool.submit(one_height_job, job): (
                job["neighbor_index"],
                job["state_index"],
            )
            for job in jobs
        }
        for future in as_completed(futures):
            result = future.result()
            key = (
                int(result["neighbor_index"]),
                int(result["state_index"]),
            )
            results[key] = result["profile"]
            print(
                "HEIGHT",
                f"neighbor={key[0]}",
                f"state={key[1]}",
                f"depth={result['profile'].get('first_exit_depth')}",
                flush=True,
            )

    neighbor_summaries = []
    total_states = 0
    total_height_matches = 0

    parent_rows = {
        int(row["index"]): row for row in parent["states"]
    }

    for neighbor_index in sorted(metadata):
        meta = metadata[neighbor_index]
        row = meta["row"]
        component = meta["component"]
        state_parent_map = meta["state_parent_map"]

        state_rows = []
        depth_counts: dict[str, int] = {}
        for child_state in component["states"]:
            child_index = int(child_state["index"])
            parent_index = state_parent_map[child_index]
            parent_depth = parent_rows[parent_index]["first_exit_depth"]
            profile = results[(neighbor_index, child_index)]
            child_depth = profile.get("first_exit_depth")
            depth_key = (
                str(child_depth) if child_depth is not None else "unresolved"
            )
            depth_counts[depth_key] = depth_counts.get(depth_key, 0) + 1
            equal = child_depth == parent_depth
            total_height_matches += int(equal)
            total_states += 1
            state_rows.append(
                {
                    "child_index": child_index,
                    "parent_index": parent_index,
                    "parent_depth": parent_depth,
                    "child_depth": child_depth,
                    "height_equal": equal,
                    "expanded_unique_states": profile.get(
                        "expanded_unique_states", 0
                    ),
                    "exit_counts": profile.get("exit_counts", {}),
                }
            )

        by_child = {
            row["child_index"]: row for row in state_rows
        }
        edge_rows = []
        max_abs_delta = 0
        all_edges_resolved = True
        for a, b in component["edges"]:
            da = by_child[int(a)]["child_depth"]
            db = by_child[int(b)]["child_depth"]
            delta = None if da is None or db is None else db - da
            if delta is None:
                all_edges_resolved = False
            else:
                max_abs_delta = max(max_abs_delta, abs(delta))
            edge_rows.append(
                {
                    "a": int(a),
                    "b": int(b),
                    "depth_a": da,
                    "depth_b": db,
                    "delta": delta,
                }
            )

        report = {
            "neighbor_index": neighbor_index,
            "move": row["move"],
            "child_states": component["admissible_states"],
            "child_edges": component["graph_edges"],
            "depth_counts": depth_counts,
            "states": state_rows,
            "edge_depth_deltas": edge_rows,
            "all_height_labels_preserved": all(
                item["height_equal"] for item in state_rows
            ),
            "all_edges_resolved": all_edges_resolved,
            "max_edge_absolute_depth_delta": (
                max_abs_delta if all_edges_resolved else None
            ),
            "unit_slope": (
                all_edges_resolved and max_abs_delta <= 1
            ),
            "depth11_found": any(
                item["child_depth"] == 11 for item in state_rows
            ),
            "expanded_unique_state_min": min(
                (
                    item["expanded_unique_states"]
                    for item in state_rows
                ),
                default=0,
            ),
            "expanded_unique_state_max": max(
                (
                    item["expanded_unique_states"]
                    for item in state_rows
                ),
                default=0,
            ),
        }
        rds.atomic_json(
            out / f"neighbor-{neighbor_index:02d}-height.json",
            report,
        )
        neighbor_summaries.append(report)

    summary = {
        "witness": str(source),
        "source_component_summary": args.source_component_summary,
        "flip_census_summary": args.flip_census_summary,
        "selected_neighbor_indices": [
            int(row["index"]) for row in selected
        ],
        "neighbors_evaluated": len(neighbor_summaries),
        "states_evaluated": total_states,
        "height_labels_equal_states": total_height_matches,
        "all_height_labels_preserved_neighbors": [
            row["neighbor_index"]
            for row in neighbor_summaries
            if row["all_height_labels_preserved"]
        ],
        "unit_slope_neighbors": [
            row["neighbor_index"]
            for row in neighbor_summaries
            if row["unit_slope"]
        ],
        "depth11_neighbors": [
            row["neighbor_index"]
            for row in neighbor_summaries
            if row["depth11_found"]
        ],
        "neighbors": [
            {
                key: row[key]
                for key in (
                    "neighbor_index",
                    "move",
                    "child_states",
                    "child_edges",
                    "depth_counts",
                    "all_height_labels_preserved",
                    "max_edge_absolute_depth_delta",
                    "unit_slope",
                    "depth11_found",
                    "expanded_unique_state_min",
                    "expanded_unique_state_max",
                )
            }
            for row in neighbor_summaries
        ],
        "elapsed_seconds": time.time() - started,
    }
    rds.atomic_json(out / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
