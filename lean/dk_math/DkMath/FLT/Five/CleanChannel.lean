/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GN5

#print "file: DkMath.FLT.Five.CleanChannel"

namespace DkMath.FLT.Five

/-!
# Local valuation-one obstructions

A `CleanGN5Channel g y q` is a prime divisor of the cyclotomic factor which does not
divide the gap and occurs only to its first power.  Hence `q` divides
`g * GN5 g y`, while `q^2` does not.  This is incompatible with a fifth power.

The module gives the direct square-divisibility contradiction.  `Valuation.lean`
repackages the same obstruction as the incompatible bounds `v_q >= 5` and `v_q <= 1`.
-/

/-- A prime occurring with local valuation exactly one in the residual and valuation
zero in the gap.  The fields are intentionally explicit so providers can be audited. -/
structure CleanGN5Channel (g y q : ℕ) : Prop where
  prime : Nat.Prime q
  dvd_GN5 : q ∣ GN5 g y
  not_dvd_gap : ¬ q ∣ g
  noLift : ¬ q ^ 2 ∣ GN5 g y

namespace CleanGN5Channel

/-- A clean GN5 channel divides the fifth-power body. -/
theorem dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    q ∣ g * GN5 g y := by
  exact dvd_mul_of_dvd_right h.dvd_GN5 g

/-- A clean channel prevents the square of its prime from entering the full body. -/
theorem not_sq_dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ q ^ 2 ∣ g * GN5 g y := by
  intro hqSqBody
  apply h.noLift
  have hqCoprimeGap : Nat.Coprime q g :=
    (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_gap
  have hqSqCoprimeGap : Nat.Coprime (q ^ 2) g :=
    hqCoprimeGap.pow_left 2
  exact Nat.Coprime.dvd_of_dvd_mul_left hqSqCoprimeGap hqSqBody

end CleanGN5Channel

/-- A local no-lift prime channel prevents `GN5 g y` from being a fifth power. -/
theorem not_fifth_power_GN5_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    simpa [hx] using h.dvd_GN5
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.noLift
  rw [hx]
  use q ^ 3 * k ^ 5
  ring

/-- A clean channel prevents the full body `g * GN5 g y` from being a fifth power. -/
theorem not_fifth_power_body_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, g * GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hx]
    exact h.dvd_body
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.not_sq_dvd_body
  rw [hx]
  use q ^ 3 * k ^ 5
  ring

/-- The finite-prime escape example gives a concrete clean channel at `31`. -/
theorem cleanGN5Channel_one_one_31 : CleanGN5Channel 1 1 31 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · norm_num [GN5]
  · norm_num
  · norm_num [GN5]

/-- The concrete GN5 target is not a perfect fifth power. -/
theorem GN5_one_one_not_fifth_power :
    ¬ ∃ x : ℕ, GN5 1 1 = x ^ 5 := by
  exact not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31

end DkMath.FLT.Five
