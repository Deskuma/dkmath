# TRM-026 — Unlabeled Port Network / V4 Flow-Assignment Split

## Implemented

Added `DkMath/Tromino/PortNetwork.lean` with the unlabeled structural carrier:

- `PortNetwork` stores `regionCount` and the arity of every region;
- `PortNetworkPort P` is the dependent Sigma of region ports;
- `PortCrossing P` stores an involutive crossing and the region-change law;
- `V4FlowAssignment C` stores nowhere-zero `TrominoState` labels and
  crossing label preservation.

The carrier and crossing contain no label or holonomy fields.  A crossing is
fixed-point-free as a consequence of `changesRegion`, and `crossEquiv` exposes
the involution as an equivalence.

## FlowNetwork reconstruction and erasure

For `A : V4FlowAssignment C`, `A.toFlowNetwork` keeps the same region count
and arities and constructs each `FlowSignature` from `A.label`.  The
corresponding `A.toFlowCrossing` uses the same crossing function, involution,
region-change proof, and crossing-label law.

For an existing `N : FlowNetwork` and `C : FlowCrossing N`,
`N.toPortNetwork`, `C.toPortCrossing`, and
`C.toV4FlowAssignment` erase the labels from the structural carrier while
retaining the original crossing and nonzero label data.

The production API includes pointwise theorems for region count, arity,
labels, crossing functions, and re-extracted assignment labels.  The audit
checks both directions of the round trip without changing the existing
FlowNetwork/FlowCrossing modules.

No separate `PortNetworkFlowBridge` was added: importing RegionWalk,
RegionPotential, or coloring APIs into this low-level structural module would
raise the dependency layer unnecessarily.  The existing flow theory remains
available through the reconstructed FlowNetwork stack.

## Separation fixture

On the same 2-region × 2-port structural carrier and crossing, the audit
constructs two distinct assignments:

- every port labeled `deltaA`;
- every port labeled `deltaB`.

Both are nowhere-zero and crossing-preserving, but they are unequal.  Thus the
combinatorial carrier does not determine the V4 labels.

## Boundary

This checkpoint only factors structural port data from supplied V4 labels.  It
does not migrate rotation, Euler, or genus modules, and it does not prove
planarity, topological realization, arbitrary sphere-map flow existence,
zero-holonomy flow existence, or the Four-Color theorem.

## Verification

The requested production and audit builds completed successfully.  Regression
builds for `CombinatorialMap`, its audit, `RegionPotential`, and the coloring
bridge also completed successfully.  The key declarations were checked with
`#print axioms`; no new axiom, `sorry`, `admit`, `unsafe`, or `noncomputable`
production declaration was introduced.
