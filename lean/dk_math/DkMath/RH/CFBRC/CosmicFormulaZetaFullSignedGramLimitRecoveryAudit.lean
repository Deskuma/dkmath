/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedMellinGramBridgeAudit
import DkMath.Analysis.MellinQuadraticGramLimit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedGramLimitRecoveryAudit"

/-!
# CFZP-006G: full signed Gram zero-width limit recovery

This module applies the generic finite Mellin Gram zero-width limit to the
full canonical signed family from CFZP-006F.  The resulting target is the
fixed finite source mass, and then the already-proved CFZP-006D full pair sum.

Only one-sided finite limits are recorded.  No completion remainder,
rectangle remainder, off-diagonal sign, infinite limit, or RH consequence is
introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Fixed source recovery at zero width -/

theorem cfzpCanonicalSignedLogCoefficientNodeSum_eq_source
    (X : ℕ) (s : ℂ) :
    ∑ j : Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X)),
      cfzpCanonicalSignedLogCoefficientFinFamily X s j *
        cfzpCanonicalSignedLogNodeFinFamily X j =
      cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s := by
  simpa [cfzpCanonicalSignedLogFinFeatureSum] using
    (cfzpCanonicalSignedLogFinFeatureSum_zeroShift X s)

/-! ## B. Full signed Gram energy -/

theorem tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_totalSourceMass
    (X : ℕ) (s : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s)
      (𝓝[>] 0)
      (𝓝 (cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s)) := by
  have hgeneric :=
    tendsto_mellinQuadraticBoxGramEnergy_zeroWidth
      (cfzpCanonicalSignedLogNodeFinFamily X)
      (cfzpCanonicalSignedLogCoefficientFinFamily X s)
  simpa [cfzpCanonicalFunctionalReflectionFullSignedGramEnergy,
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo,
    cfzpCanonicalSignedLogCoefficientNodeSum_eq_source X s] using hgeneric

theorem tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_totalSourceMass
    (X : ℕ) (s : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm ε X s)
      (𝓝[>] 0)
      (𝓝 ((cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s : ℝ) : ℂ)) := by
  have hgeneric :=
    tendsto_mellinQuadraticBoxGramQuadraticForm_zeroWidth
      (cfzpCanonicalSignedLogNodeFinFamily X)
      (cfzpCanonicalSignedLogCoefficientFinFamily X s)
  simpa [cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm,
    cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo,
    cfzpCanonicalSignedLogCoefficientNodeSum_eq_source X s] using hgeneric

/-! ## C. Exact 006D pair-sum target -/

theorem tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_fullPairSum
    (X : ℕ) (s : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s)
      (𝓝[>] 0)
      (𝓝 (cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s)) := by
  rw [cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass]
  exact tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_totalSourceMass
    X s

end DkMath.RH.CFBRCProjection
