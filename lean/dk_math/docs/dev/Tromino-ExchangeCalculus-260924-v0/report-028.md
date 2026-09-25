# TRM-029 — Port Region Walk / Structural Connectivity Migration

## Implemented

Added `DkMath/Tromino/PortRegionWalk.lean` with a label-free walk layer on
`PortNetwork` and `PortCrossing`:

- `PortRegionWalk.Valid` and `PortRegionWalk` preserve only port lists and
  structural crossing validity;
- extensionality, nil, length, singleton, append, append associativity, and
  reverse algebra are implemented as computable definitions/theorems; and
- `PortRegionReachable`, `PortRootedRegionConnected`, and
  `PortRegionConnected` provide structural reachability and connectedness.

The connectedness API includes reflexivity, symmetry, transitivity, global to
rooted conversion, and rooted-to-global conversion.

## Flow erasure and assignment lift

Existing `FlowRegionWalk` values erase to `PortRegionWalk` with the exact same
edge list.  Conversely, a `PortRegionWalk` lifts through any
`V4FlowAssignment` to a `FlowRegionWalk`, again preserving the edge list.

Nil, singleton, append, and reverse commute with both adapters.  The
round-trip edge-list/structure theorems are included.

The central calibration theorem is the exact equivalence
`PortRegionReachable C r s ↔ RegionReachable A.toFlowCrossing r s`.
Consequently, Flow reachability is independent of the chosen assignment;
rooted and global connectedness have corresponding lift and independence
theorems as well.

## Structural fixtures and audit

`DkMathTest/Tromino/PortRegionWalkAxiomAudit.lean` checks:

- nil/singleton validity and append/reverse laws;
- 2×2 and 2×3 connectedness;
- a four-region, one-port-per-region crossing with components `0↔1` and
  `2↔3`, including positive and negative reachability and non-connectedness;
- Flow-to-Port erasure and Port-to-Flow lifting;
- reachability equivalence and assignment independence; and
- connected Flow calibration plus round-trip edge-list preservation.

## Boundary and verification

The Port core has no label, holonomy, potential, planarity, topological
realization, genus, strong PortCombinatorialMap, universal V4-flow, or
Four-Color claim.  Existing FlowRegionWalk APIs remain unchanged.

The requested production/audit build and regression targets completed
successfully.  The new declarations were checked with `#print axioms`; no
new axiom, `sorry`, `admit`, `unsafe`, or `noncomputable` production
declaration was introduced.
