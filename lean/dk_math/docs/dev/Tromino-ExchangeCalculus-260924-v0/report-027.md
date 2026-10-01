# TRM-028 — Port Face Orbit / Euler Count Migration

## Implemented

Added `DkMath/Tromino/PortFaceOrbit.lean` with the label-free analogue of
the existing Flow face-orbit API:

- `portFaceOrbit` and its membership, iterate, distinctness, and card
  theorems;
- reverse membership, subset/equality, equal-or-disjoint, coverage, and
  first-return invariance;
- `SamePortFaceOrbit` and `portFaceOrbitSetoid`; and
- finite first-return and orbit calibration back to `faceOrbit`.

The module also proves that Flow face orbits obtained from any lifted
`V4FlowAssignment` equal the same structural `portFaceOrbit`.  Thus orbit
data is independent of the chosen assignment.

Added `DkMath/Tromino/PortEulerCount.lean` with the label-free edge-pair,
edge-orbit, face-family, and Euler-count layer:

- port edge-pair cardinality, partition, coverage, and `D = 2E`;
- port face-family cardinality, partition, and total-cardinality sum;
- `portRegionVertexCount`, `portCrossingEdgeCount`, `portFaceCount`, and
  `portCombinatorialEulerCharacteristic`; and
- exact calibration of port counts and Euler characteristic to the existing
  Flow definitions, including assignment-independent lifted Euler
  characteristic.

## Pure structural fixtures and audits

`DkMathTest/Tromino/PortFaceOrbitAxiomAudit.lean` checks the 2×2 two-face
decomposition, the 2×3 six-step face orbit, setoid/orbit laws, Flow erasure,
and assignment-independent orbit lifting.

`DkMathTest/Tromino/PortEulerCountAxiomAudit.lean` checks the pure fixtures:

- 2×2: `V = 2`, `E = 2`, `F = 2`, `χ = 2`;
- 2×3: `V = 2`, `E = 3`, `F = 1`, `χ = 0`;
- edge and face partition sums; and
- Flow calibration and assignment-independent Euler characteristic.

## Boundary and verification

The existing Flow APIs remain unchanged.  Strong Port combinatorial-map,
genus, planarity, topological realization, and Four-Color migration remain
outside this checkpoint.

The requested production/audit build and the `FaceOrbit`, `EulerCount`, and
`CombinatorialMap` regressions completed successfully.  The new declarations
were checked with `#print axioms`; production files contain no `sorry`,
`admit`, `unsafe`, new axiom, or `noncomputable` declaration.
