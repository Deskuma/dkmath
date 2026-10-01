# TRM-030 — Unlabeled Strong Combinatorial Map / Genus-Zero Input

## Implemented

Added `DkMath/Tromino/PortCombinatorialMap.lean` with a label-free strong
`PortCombinatorialMap` over `PortNetwork` and `PortCrossing`:

- crossing, rotation, nonempty-region, and structural connectedness fields;
- local rotation, vertex/edge/face/port observers, and arithmetic Euler
  characteristic;
- same-region vertex-rotation orbit and connected-region forwarding APIs;
- arithmetic `PortHasCombinatorialGenus`, uniqueness, genus 0/1
  characterizations, `χ ≤ 2`, and evenness; and
- `PortHasSphereCharacteristic` plus the `PortGenusZeroCombinatorialMap`
  wrapper and sphere consequence.

## Flow calibration and independence

Flow combinatorial maps erase to strong Port maps, and strong Port maps lift
through any `V4FlowAssignment`.  Exact observer equalities are proved for
vertex, edge, face, port, and Euler counts in both directions.  Genus and
sphere iff-calibrations, assignment independence of all observers, genus,
and sphere, and crossing/rotation round trips are included.

`DkMathTest/Tromino/PortCombinatorialMapAxiomAudit.lean` checks pure 2×2 and
2×3 fixtures, with values `(V,E,F,D,χ) = (2,2,2,4,2)` and
`(2,3,1,6,0)`, respectively.  It also checks genus-zero/sphere behavior, the
genus-zero wrapper, the disconnected TRM-029 nonexample, Flow erasure/lift
calibration, assignment independence, and round trips.

`DkMathTest/Tromino/PortCombinatorialMapGenusAxiomAudit.lean` checks the
arithmetic genus and sphere API independently, including both calibration
directions.

## Boundary and verification

This checkpoint stops at the label-free strong map and genus-zero input.  It
does not construct a topological realization, prove planarity or sphere
embedding, prove a universal V4 assignment, or establish Four-Color
existence.  The intended open architecture remains
`PortGenusZeroCombinatorialMap → existence gap → RegionPotential → Colorable4`.

The requested production/audit build completed successfully:

```text
DkMath.Tromino.PortCombinatorialMap                         1545 jobs
DkMathTest.Tromino.PortCombinatorialMapAxiomAudit           1557 jobs
DkMathTest.Tromino.PortCombinatorialMapGenusAxiomAudit      1558 jobs
```

The new production declarations were checked with `#print axioms`; no new
axiom, `sorry`, `admit`, `unsafe`, or `noncomputable` production declaration
was introduced.  Existing dependency audit output contains the repository's
previous `propext`/choice/quotient axioms and linter warnings.
