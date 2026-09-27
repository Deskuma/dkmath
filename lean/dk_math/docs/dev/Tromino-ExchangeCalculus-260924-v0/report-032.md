# TRM-033 — Face-boundary duality kernel / triangle dual calibration

## Implemented

- Added `DkMath.Tromino.PortDualityKernel`.
- Defined the raw permutation convention
  `alpha := crossing`, `rho := local rotation`, and
  `phi := rho ∘ alpha`.
- Defined `dualRotationEquiv := portFaceEquiv` and proved the raw identity
  `dualFaceStepRaw R C p = R.rotate p`, including its iterate form.
- Identified dual vertices with primal face orbits and dual faces with primal
  region/vertex rotation orbits.
- Added the dual/primal count swap and Euler-characteristic preservation.
- Added the computable primitive face-boundary walk, its closure/length,
  orbit-membership, exact Finset support, and label-sum/XOR identity.
- Proved primal zero-holonomy V4 tension implies orbit-level dual face
  Kirchhoff conservation.
- Added `IsDualLoopPort`, `DualLoopFree`, crossing invariance, and the
  characteristic-two crossing-pair label cancellation theorem.
- Proved the TRM-032 triangle fixture is dual-loop-free.
- Added the fixture-specific two-region, arity-three triangle dual map and
  kernel-checked values `V*=2`, `E*=3`, `F*=3`, `D*=6`, `chi*=2`.
- Audited the old `portThreeMap`: it has the same 2-region/3-edge
  multiplicities but `F=1`, `chi=0`; its permutation data differ from the
  triangle dual, so the multigraph shape does not determine the embedding.
- Transported the explicit triangle coloring labels to a concrete dual
  assignment and proved dual Kirchhoff balance from
  `deltaA + deltaB + deltaC = 0`.
- Proved the raw double-dual permutation identity.

## Boundary

No general dual `PortNetwork` constructor was introduced. The converse from
dual face conservation to primal tension remains open and is recorded as the
genus-zero face-boundary-generation gap. No loop-capable carrier, universal
flow-existence theorem, topological realization, or Four Color theorem claim
was added.

## Validation

- `lake build DkMath.Tromino.PortDualityKernel`
- `lake build DkMathTest.Tromino.PortDualityKernelAxiomAudit`
- Regression build:
  `PortKirchhoffFlow`, its audit, `PortTensionColoring`, its audit,
  `PortCombinatorialMap`, and its audit.
- `git diff --check` and forbidden-construct scan completed.
- `#print axioms` audit completed for the new kernel-facing results.
