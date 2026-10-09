/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PadicValNat

#print "file: DkMath.Lib.NumberTheory.SevenUnitAllocation"

/-! Neutral allocation in a product with one residual seven-adic layer. -/

namespace DkMath.Lib.NumberTheory

/-- Unit ordinary factors leave twice the quadratic valuation in the carrier. -/
theorem padicValNat_seven_unit_product {g T A B C Q : ℕ}
    (hg : g ≠ 0) (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hprod : g * T = 7 * A * B * C * Q ^ 2)
    (hval : padicValNat 7 T = 1)
    (huA : ¬ 7 ∣ A) (huB : ¬ 7 ∣ B) (huC : ¬ 7 ∣ C) :
    padicValNat 7 g = 2 * padicValNat 7 Q := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7A : 7 * A ≠ 0 := mul_ne_zero (by decide) hA
  have h7AB : 7 * A * B ≠ 0 := mul_ne_zero h7A hB
  have h7ABC : 7 * A * B * C ≠ 0 := mul_ne_zero h7AB hC
  have hv := congrArg (padicValNat 7) hprod
  rw [padicValNat.mul hg hT, hval,
    padicValNat.mul h7ABC (pow_ne_zero _ hQ), padicValNat.mul h7AB hC,
    padicValNat.mul h7A hB, padicValNat.mul (by decide : 7 ≠ 0) hA,
    padicValNat.pow, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd huA, padicValNat.eq_zero_of_not_dvd huB,
    padicValNat.eq_zero_of_not_dvd huC] at hv
  omega

/-- An even positive seven-adic carrier valuation forces a second layer. -/
theorem fortyNine_dvd_of_seven_dvd_of_valuation_double {g Q : ℕ}
    (hg : g ≠ 0) (hgap : 7 ∣ g)
    (hval : padicValNat 7 g = 2 * padicValNat 7 Q) :
    49 ∣ g := by
  have hp : Nat.Prime 7 := by decide
  have hge := (Vp_ge_one_iff hp hg).mpr hgap
  have htwo : 2 ≤ padicValNat 7 g := by omega
  simpa using (padicValNat_le_iff_dvd hp hg 2).mp htwo

end DkMath.Lib.NumberTheory
