# TRM-025 — Connected Combinatorial-Map Certificate / Arithmetic Genus

## Implemented

Added `DkMath/Tromino/CombinatorialMap.lean` with the strong wrapper
`FlowCombinatorialMap N`.  Its fields are:

- a fixed-point-free `FlowCrossing N`;
- a `FlowRotationSystem N`, hence one cyclic rotation orbit per region;
- `0 < N.regionCount`; and
- `RegionReachable crossing r s` for every pair of regions.

The wrapper exposes `localRotation`, `vertexCount`, `edgeCount`, `faceCount`,
`portCount`, and `eulerCharacteristic`, forwarding to the TRM-024 finite
counting layer.  The generic `EulerCount` API is unchanged.

For ports in the same region, the audit checks the theorem-level consequence
of `FlowRotationSystem.cyclic`: every such port is reachable from every other
by an iterate of the local rotation.  This is packaged as
`SameVertexRotationOrbit`.  The weak `FlowLocalRotation` interface has no such
alignment guarantee.

## Arithmetic characteristic layer

`HasCombinatorialGenus M g` is defined by the relation

```text
M.eulerCharacteristic = 2 - 2 * g
```

The production module proves genus uniqueness, the genus-zero and genus-one
characterizations, the bound `chi ≤ 2` for a witnessed genus, and evenness of
`chi` for a witnessed genus.  `HasSphereCharacteristic M` is the purely
combinatorial predicate `M.eulerCharacteristic = 2`, with an equivalence to
`HasCombinatorialGenus M 0`.

No existence theorem for a genus witness is asserted.

## Kernel-checked fixtures

`DkMathTest/Tromino/CombinatorialMapAxiomAudit.lean` adds and checks:

- a connected 2-region × 2-port cyclic rotation system.  Its face step has
  two 2-cycles, giving `V = 2`, `E = 2`, `F = 2`, `D = 4`, and `chi = 2`;
- the connected 2-region × 3-port cyclic fixture from TRM-022.  It gives
  `V = 2`, `E = 3`, `F = 1`, `D = 6`, and `chi = 0`, and is packaged with
  arithmetic genus `1`; and
- the existing 2-region × 4-port identity rotation as a negative calibration:
  one region has at least two distinct ports but its identity rotation is not
  `RegionRotationCyclic`.

The 2×4 identity fixture is therefore not packaged as a strong map or used as
a sphere/genus-zero calibration.

## Boundary and remaining gap

The connected rotation-system data are standard combinatorial data associated
with an orientable cellular-embedding picture, and `chi = 2 - 2g` is recorded
only as an arithmetic relation here.  This checkpoint does not formalize a
topological realization theorem, planarity, sphere embedding, genus of a
surface, or a planar-map extraction.

The Four-Color-side implication from a sphere/planar combinatorial map to a
nonzero `V4` edge flow with zero holonomy, then to `RegionPotential` and a
Mathlib 4-coloring, remains a separate open gap.  No zero-holonomy existence
assumption was added to `FlowCombinatorialMap`.

## Verification

The focused production and audit builds completed successfully.  The key
declarations were checked with `#print axioms`; the reports contain only the
existing logical dependencies (`propext`, `Quot.sound`, and where inherited
by finite/arithmetic infrastructure, `Classical.choice`).  No new axiom,
`sorry`, `admit`, `unsafe`, or `noncomputable` production declaration was
introduced.
