/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABCEpsilonIdentity
import DkMath.ABC.GNJointPressureOddPrime

#print "file: DkMath.ABC.ABCEpsilonJointPressureBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Intrinsic ABC epsilon and odd-prime joint-pressure bridge

This module composes the odd-prime GN joint-pressure route with the intrinsic
ABC epsilon coordinate and the ordinary ABC quality coordinate.
-/

namespace DkMath.ABC

/--
A fixed odd-prime joint-pressure budget along a large-radical family forces
ordinary ABC quality eventually below every strict threshold `1 + δ` above the
external exponent `1 + ε`.
-/
theorem eventually_quality_lt_one_add_of_oddPrime_jointPressure
    {ι : Type*} {l : Filter ι}
    (T : ι → Triple)
    {p : ℕ} (ε ρ C δ : ℝ)
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : ∀ᶠ i in l, 0 < (T i).a)
    (hb : ∀ᶠ i in l, 0 < (T i).b)
    (hmargin :
      ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε))
    (hjoint :
      ∀ᶠ i in l,
        GNOddPrimeJointPressureBudgetAffine (T i) p ρ C)
    (hrad : Filter.Tendsto (fun i => (T i).radLog) l Filter.atTop)
    (hεδ : ε < δ) :
    ∀ᶠ i in l, quality (T i) < 1 + δ := by
  have hK : 0 < GNABCConstant p C 0 :=
    lt_of_lt_of_le zero_lt_one (one_le_GNABCConstant p C 0)
  have hbound :
      ∀ᶠ i in l,
        ((T i).c : ℝ) ≤
          GNABCConstant p C 0 *
            (rad ((T i).a * (T i).b * (T i).c) : ℝ) ^ (1 + ε) := by
    filter_upwards [ha, hb, hjoint] with i hai hbi hjointi
    exact (T i).abc_bound_of_oddPrime_jointPressure
      hp hpOdd hai hbi hmargin hjointi
  exact eventually_quality_lt_one_add_of_abc_bound
    T ε (GNABCConstant p C 0) δ ha hb hK hbound hrad hεδ

end DkMath.ABC
