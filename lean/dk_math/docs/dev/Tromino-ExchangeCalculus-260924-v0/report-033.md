# TRM-034 report — F2 chain scaffold

## Implemented

- Added `DkMath.Tromino.PortF2Chains` with `PortF2 := ZMod 2`.
- Defined multigraph-safe port edge and face cells, finite chain spaces, and their `finrank` calibrations.
- Added edge/vertex incidence, `portBoundary1`, the walk coefficient chain, endpoint identity, and the closed-walk cycle theorem.
- Added face incidence, face-boundary chains, representative face-boundary walks, and the face-boundary cycle theorem.
- Proved `portBoundary1 ∘ portBoundary2 = 0`, and proved the face-boundary space is contained in the cycle space.
- Added `DkMathTest.Tromino.PortF2ChainsAxiomAudit` with 18 finite/API checks and axiom prints for the new boundary results.

## Verification

The following builds succeeded from `lean/dk_math` with Lean 4.34:

```text
lake build DkMath.Tromino.PortF2Chains
lake build DkMathTest.Tromino.PortF2ChainsAxiomAudit
lake build DkMath.Tromino.PortF2Chains DkMathTest.Tromino.PortF2ChainsAxiomAudit \
  DkMath.Tromino.PortDualityKernel DkMathTest.Tromino.PortDualityKernelAxiomAudit \
  DkMath.Tromino.PortKirchhoffFlow DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit \
  DkMath.Tromino.PortCombinatorialMap DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
```

The production-file forbidden-construct scan for `sorry`, `admit`, `unsafe`,
`axiom`, and `noncomputable` returned no matches.

## Boundary

This checkpoint supplies the finite F2 chain scaffold only. It does not claim
genus-zero exactness, a universal dual constructor, a V4 functional, or a
global four-coloring theorem.
