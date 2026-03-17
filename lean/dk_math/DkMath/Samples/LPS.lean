/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

/-
LPS module: Lander, Parkin, and Selfridge conjecture research

NOTE: Original LPS files have been refactored into 3 main families:
  - CosmicFormula.Residual*  (formerly BigFamily.lean / BigFamilyInt.lean)
  - PowerSwap.*              (formerly PowerSwap.lean / Exchange.lean / PowerSwapBranch.lean / GapContours.lean)
  - NumberTheory.PowerSums.* (formerly GapFillRank.lean / BigFamilyExamples.lean)

This file provides backward-compatible imports for the refactored structure.
-/

-- Re-export new modules as backward-compatible bridges
import DkMath.CosmicFormula.ResidualNat
import DkMath.CosmicFormula.ResidualInt
import DkMath.PowerSwap
import DkMath.NumberTheory.PowerSums
