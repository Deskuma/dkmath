/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.GEisensteinBridge
import DkMath.FLT.Kummer
import DkMath.FLT.Main
import DkMath.FLT.PrimeProvider
import DkMath.FLT.Samples
import DkMath.FLT.Five
import DkMath.FLT.Seven
import DkMath.FLT.QuadraticEssence
import DkMath.FLT.Frey
import DkMath.FLT.FreyTwo
import DkMath.FLT.FreyPrimeProfile
import DkMath.FLT.FreyCounterexample
import DkMath.FLT.FreyResidualRepresentation
import DkMath.FLT.FreyResidualIrreducibility
import DkMath.FLT.FreyResidualFiniteLevel
import DkMath.FLT.FreyResidualGeometry
import DkMath.FLT.FreyResidualDimensionBound
import DkMath.FLT.FreyResidualNontrivial
import DkMath.FLT.FreyResidualDimensionCriteria
import DkMath.FLT.FreyResidualRankTwo
import DkMath.FLT.FreyResidualGL2
import DkMath.FLT.FreyResidualCyclotomic
import DkMath.FLT.FreyTorsionAllCard
import DkMath.FLT.FreyTorsionPrimePower
import DkMath.FLT.FreyWeilGeometry
import DkMath.FLT.FreyWeilFunction
import DkMath.FLT.FreyWeilValuation
import DkMath.FLT.FreyWeilTransport
import DkMath.FLT.FreyWeilCharacter
import DkMath.FLT.FreyWeilBicharacter
import DkMath.FLT.PrimeDepthBridge
import DkMath.FLT.FreyWeilGalois
import DkMath.FLT.FreyGeometricWeilPairing
import DkMath.FLT.FreyStableLine
import DkMath.FLT.FreyRationalTorsionValuation
import DkMath.FLT.FreyRationalTorsionIntegral
import DkMath.FLT.FreyRationalTorsionPositive
import DkMath.FLT.FreyRationalTorsionBounds
import DkMath.FLT.FreyRationalTorsionIdentities
import DkMath.FLT.FreyRationalTorsion
import DkMath.FLT.FreyRationalTorsionBridge

import DkMath.FLT.FreyInertiaTransport
import DkMath.FLT.FreyValuationArithmetic
import DkMath.FLT.FreyGoodReductionInertia
import DkMath.FLT.FreySmoothReductionInertia
import DkMath.FLT.FreyCriticalCentre
import DkMath.FLT.FreyNodalReduction
import DkMath.FLT.FreyShallowSlope
import DkMath.FLT.FreyBranchComparison
import DkMath.FLT.FreyDoublingDepth
import DkMath.FLT.FreyUnramifiedAway
import DkMath.FLT.FreyDyadicInertia
import DkMath.FLT.FreyIntegralTorsionWitness
import DkMath.FLT.FreyPrimeGoodFiltration
import DkMath.FLT.FreyPrimeFiltration
import DkMath.FLT.FreyStableLineLocalGlobal
import DkMath.FLT.FreyCofixedBranchSwap
import DkMath.FLT.FreyDyadicNontrivial
import DkMath.FLT.FreyDyadicGeometry
import DkMath.FLT.FreyDyadicZeroComponent

#print "file: DkMath.FLT"

set_option linter.style.longLine false

/-!
# DkMath FLT historical broad aggregator

`DkMath.FLT` is a broad compatibility/research aggregator that predates the
independent completed exponent-three public surface.  It still imports legacy
`Main`, Kummer/provider research, FLT5, FLT7 research, and related bridge
modules, so it is intentionally **not** the canonical discovery import for the
current standalone FLT3 proof.

For completed exponent-specific public results, prefer explicit imports:

```lean
import DkMath.FLT.Three
import DkMath.FLT.Five
```

with endpoints:

- `DkMath.FLT.Three.fermatThree_no_positive_solution`
- `DkMath.FLT.Five.fermatFive_no_positive_solution`

For the current odd-prime generalization architecture, see `DkMath.FLT.Prime.*`
and `docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`.

For neutral reusable mathematics extracted from FLT and other research owners,
prefer `DkMath.Lib` where an appropriate promoted API exists.

No import semantics are changed by this documentation note: in particular,
`DkMath.FLT.Three` remains an explicit independent import rather than being
silently added to this historical aggregator.
-/
