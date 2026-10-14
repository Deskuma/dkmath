# TRM-024 — Combinatorial Euler Counting Layer

## Implemented

Added `DkMath/Tromino/EulerCount.lean`, importing the completed face-orbit layer.
The module defines the finite combinatorial counts

- `regionVertexCount N := N.regionCount`;
- `crossingEdgePair C p := {p, C.cross p}`;
- `crossingEdgeOrbits := Finset.univ.image (crossingEdgePair C)` and
  `crossingEdgeCount`;
- `faceOrbits := Finset.univ.image (faceOrbit R C)` and `faceCount`; and
- `combinatorialEulerCharacteristic R C :=
  (regionVertexCount R).toInt - crossingEdgeCount C + faceCount R C`.

For every crossing port, `crossingEdgePair` is a two-element `Finset`, is
invariant under `C.cross`, and two such pairs are equal or disjoint.  The
image family therefore has pairwise disjoint members covering all crossing
ports.  The module proves the cardinality sum and the finite identity

```text
2 * crossingEdgeCount C = R.totalPortCount
```

The face image family is likewise proved pairwise disjoint and covering all
ports.  Its cardinality sum is exactly `R.totalPortCount`, so the two finite
sum identities give the intended combinatorial `D = 2E` and `D = Σ face.length`
relations without enumerating quotient representatives.

## Fixtures

The audit fixture in `DkMathTest/Tromino/EulerCountAxiomAudit.lean` checks:

- the 2×3 two-region fixture: `V = 2`, `E = 3`, `F = 1`, `D = 6`, and
  `χ = 0`;
- the 2×4 two-region fixture: `V = 2`, `E = 4`, `F = 4`, `D = 8`, and
  `χ = 2`; and
- the two Euler characteristics are different, so the implementation does
  not assert that the finite characteristic is always `2`.

## Verification

The following focused regression build completed successfully:

```text
lake build DkMath.Tromino.FaceOrbit DkMath.Tromino.EulerCount \
  DkMathTest.Tromino.EulerCountAxiomAudit \
  DkMathTest.Tromino.FaceOrbitAxiomAudit \
  DkMathTest.Tromino.RotationSystemAxiomAudit \
  DkMathTest.Tromino.GraphColoringBridgeAxiomAudit
```

The production and audit files contain no `sorry`, `admit`, `unsafe`,
`noncomputable`, or new `axiom` declarations.  The key declarations were
checked with `#print axioms`; their reported dependencies are the existing
logical infrastructure (`propext`, `Quot.sound`, and `Classical.choice`).

This checkpoint is purely a finite combinatorial counting layer.  It does not
claim planarity, a surface interpretation, genus, a sphere, or a topological
Euler formula.
