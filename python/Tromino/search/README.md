# Repair-depth long-run search

This directory contains the long-running search harness for the Tromino Missing-Color / maze-depth experiment.

The current goal is narrower than four-coloring itself: starting from a known tetrahedral / four-state solution and adding solution-preserving combinatorial walls, how large can the local repair depth become before the solver can continue its lift?

The search keeps a planted proper four-coloring as a hidden witness of solvability. The solver is not given that coloring.

## Generator

The base structure has an implicit outer sea of color 0, a fixed outer triangle colored 1,2,3, and one initial interior vertex of color 0.

An internal triangular face is refined by inserting one vertex. Because the three face vertices have three distinct colors, the inserted vertex receives the unique missing fourth color in the planted solution. Pure face refinement therefore increases resolution while retaining an explicit solution lineage.

Complexity is then added with legal diagonal edge flips. A flip is accepted by the generator only when the new diagonal also respects the planted coloring.

    resolution growth   = face subdivision
    maze-wall insertion = solution-preserving edge flip
    solver difficulty   = required local repair depth

## Solver

The solver restores vertices in refinement birth order. For each not-yet-restored vertex v it tracks P(v), the colors already visible on the restored boundary of v, and attempts to maintain the Missing-Color Invariant |P(v)| <= 3.

If a direct color keeps the invariant, no exchange is performed. If every direct color would violate the invariant, the solver searches two-color Kempe-component exchanges as the current diagnostic proxy for GapSwap. The outer frame is locked.

Two repair policies are available. strict requires every intermediate exchange state to preserve the invariant. endpoint allows intermediate exchange states to violate it, but a repaired endpoint must restore the invariant before the current vertex is colored. The proxy exchange must not be confused with the eventual DkMath Tromino GapSwap definition.

## Quick smoke test

From the repository root:

    python3 python/Tromino/search/repair_depth_search.py search \\
      --vertices 12 \\
      --jobs 8 \\
      --steps 100 \\
      --workers 2 \\
      --max-depth 4 \\
      --target-depth 3 \\
      --output /tmp/tromino-depth-smoke

## Suggested first long run

    mkdir -p python/Tromino/results/repair-depth/d5-v24

    python3 python/Tromino/search/repair_depth_search.py search \\
      --vertices 24 \\
      --jobs 2000 \\
      --steps 2000 \\
      --warmup-flips 48 \\
      --workers "$(nproc)" \\
      --max-depth 6 \\
      --target-depth 5 \\
      --node-limit 500000 \\
      --base-seed 6000000 \\
      --intermediate-policy strict \\
      --output python/Tromino/results/repair-depth/d5-v24

The process checkpoints after each completed independent job, so an interrupted run can be resumed by running the same command again. Seeds already present in runs.jsonl are skipped.

If this run spends excessive time in repair BFS, reduce --workers before reducing the node limit. Each worker maintains its own repair frontier and can therefore consume substantial memory.

## Output

A run directory contains:

    config.json
    runs.jsonl
    summary.json
    best_witness.json

runs.jsonl is crash-safe raw job output and can become large. best_witness.json contains the final triangular faces, planted colors, refinement birth order, complete flip history, solver classification, and trace metadata required to reconstruct the hard instance.

## Replay a witness

    python3 python/Tromino/search/repair_depth_search.py replay \\
      python/Tromino/results/repair-depth/d5-v24/best_witness.json \\
      --min-depth 0 \\
      --max-depth 10 \\
      --node-limit 2000000 \\
      --intermediate-policy strict \\
      --trace \\
      --stop-on-success \\
      --output python/Tromino/results/repair-depth/d5-v24/replay-strict.json

If strict replay remains unresolved, also replay with --intermediate-policy endpoint. This comparison helps distinguish a genuinely deeper maze from a route that exists only when the strict intermediate Missing-Color condition is relaxed.

## Result return policy

For chat-side analysis, the smallest useful return is summary.json plus best_witness.json, and replay-strict.json when relevant. These files can be attached directly in chat.

For repository-side preservation, commit the small result files into a named result directory. Raw runs.jsonl is ignored by default because long runs can be large; add it explicitly only when the complete raw record is useful.

## Current target

The immediate target is a verified depth-5 witness. More importantly, classify the first hard examples as one of three cases: genuinely solved only after depth 5 or greater, merely depth-limited by the configured ceiling, or blocked by the strict Missing-Color invariant even though the planted coloring proves that a global proper coloring exists.

The third case is especially valuable because it means the present invariant or proxy move set is too restrictive rather than merely revealing a deeper maze.
