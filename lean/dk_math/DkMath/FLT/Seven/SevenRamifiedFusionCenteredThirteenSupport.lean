/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport"

namespace DkMath.FLT.Seven

/-- The actual sextic never vanishes mod13 at a unit gap. -/
theorem centeredSevenSextic_not_dvd_thirteen {D q : ℕ} (hD : ¬ 13 ∣ D) :
    ¬ 13 ∣ centeredSevenSextic D q := by
  have hf : ∀ d x : ZMod 13, d ≠ 0 →
      7*x^6 + 35*d^2*x^4 + 21*d^4*x^2 + d^6 ≠ 0 := by decide
  have hd : (D : ZMod 13) ≠ 0 := by
    intro h
    exact hD ((ZMod.natCast_eq_zero_iff D 13).mp h)
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (centeredSevenSextic D q) 13).mpr h
  apply hf (D : ZMod 13) (q : ZMod 13) hd
  simpa only [centeredSevenSextic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hz

/-- Complementary13 support cannot occur in the image at a13-unit divisor. -/
theorem centeredSevenSextic_no_image_of_thirteen_support {r s : ℕ}
    (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ s) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49 := by
  have hp : Nat.Prime 13 := by decide
  have hD : ¬ 13 ∣ 7 ^ 27 * r ^ 49 := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact (by decide : ¬ 13 ∣ 7) (hp.dvd_of_dvd_pow h)
    · exact hr13 (hp.dvd_of_dvd_pow h)
  rintro ⟨q, heq⟩
  apply centeredSevenSextic_not_dvd_thirteen (q := q) hD
  rw [heq]
  exact dvd_mul_of_dvd_right (dvd_pow hs13 (by decide : 49 ≠ 0)) _

/-- Exclude the same chosen receiver using its necessary centered scalar equation. -/
theorem nestedAllocation_excluded_of_thirteen_support {M r : ℕ}
    (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ M / r) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) := by
  intro h
  rcases (nestedAllocation_iff_centered M r).mp h with ⟨q, hq⟩
  apply centeredSevenSextic_no_image_of_thirteen_support hr13 hs13
  refine ⟨q, ?_⟩
  simpa only [← mul_assoc, show (64 : ℕ)*7 = 448 by decide] using hq.2.1

end DkMath.FLT.Seven
