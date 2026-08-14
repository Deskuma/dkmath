/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaFunctionalEquationReflection
import Mathlib.Tactic

/-!
# Gate 4A: prime-side mirror/conjugation source audit

This module records the mirror identities available for the full centered-Xi
source and keeps their scope separate from the finite prime cutoff.  The
functional-equation reflection pairs the full decomposed right-edge source;
it does not provide a termwise conjugate/adjoint identity for the finite
von-Mangoldt cutoff.  Consequently this module supplies no prime-side energy,
nonnegativity theorem, defect sign, limit exchange, or RH consequence.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## Gate 4A.1: available full-source reflection -/

/-- The canonical Mellin quadratic weight is even in the centered coordinate.
This is the symmetry input available for the full fixed-Xi reflection. -/
theorem pascalCenteredXiPrimeSideGate4A_weight_even
    {ε : ℝ} (hε : 0 < ε) :
    PascalCenteredEvenWeight
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0) :=
  pascalCenteredXiMellinSecondDifferenceWeight_even hε

/-- The full decomposed ordinary-coordinate source has the functional-equation
reflection at the paired points `s` and `1 - s`, under the exact finite-factor
nonvanishing hypotheses. -/
theorem pascalCenteredXiPrimeSideGate4A_decomposed_source_reflection
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0)
    (h1s0 : 1 - s ≠ 0) (h1s1 : 1 - s ≠ 1)
    (h1szeta : riemannZeta (1 - s) ≠ 0)
    (h1sGamma : Complex.Gammaℝ (1 - s) ≠ 0) :
    pascalXiDecomposedNegLogDeriv (1 - s) =
      -pascalXiDecomposedNegLogDeriv s :=
  pascalXiDecomposedNegLogDeriv_one_sub_eq_neg
    hs0 hs1 hzeta hGamma h1s0 h1s1 h1szeta h1sGamma

/-! ## Gate 4A.2: finite vertical pairing scope -/

/-- The full fixed-Xi vertical pair is doubled by the even Mellin weight.
This is a reality/symmetry identity, not a positive-semidefinite pairing. -/
theorem pascalCenteredXiPrimeSideGate4A_full_vertical_pair
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiLeftVerticalContribution
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.toContourTransportWindow +
        pascalCenteredXiRightVerticalContribution
          (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
          W.toContourTransportWindow =
      2 * pascalCenteredXiRightVerticalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow :=
  pascalCenteredXiVerticalPair_eq_two_right
    (pascalCenteredXiPrimeSideGate4A_weight_even hε)
    W.toContourTransportWindow

/-- The full right-edge source is decomposed only after the fixed-Xi source
has been formed.  This theorem intentionally does not split the reflection
law into prime, archimedean, and elementary cutoff-level conjugation laws. -/
theorem pascalCenteredXiPrimeSideGate4A_right_source_decomposed
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRightVerticalContribution
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
        W.toContourTransportWindow =
      ∫ t in (-W.rectangle.T)..W.rectangle.T,
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          pascalXiDecomposedNegLogDeriv
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
          Complex.I := by
  exact pascalCenteredXiRightVerticalContribution_eq_decomposed
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
    W.toContourTransportWindow

/-! Gate 4A closeout: these theorems provide full-source reflection and
finite vertical symmetry only.  No finite-cutoff conjugate partner or Gram
bridge has been derived, so the independent prime-side provider remains open.
-/

end DkMath.RH.CFBRCProjection
