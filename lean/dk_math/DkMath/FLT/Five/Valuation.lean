/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchB

#print "file: DkMath.FLT.Five.Valuation"

namespace DkMath.FLT.Five

/-!
# Exponent-five valuation checkpoint

This module carries an independent `padicValNat` proof of the clean-channel
obstruction:

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

No research-only valuation theorem is imported here.
-/

/-- A prime divisor of a positive base contributes valuation at least five to its fifth power. -/
theorem padicValNat_lower_bound_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hvalX : 1 ≤ padicValNat q x := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp (by simpa using hqx)
  have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by
    simpa using (padicValNat.pow (p := q) (a := x) 5 hx.ne')
  rw [hpow]
  omega

/-- A clean channel bounds the valuation of the full fifth-power body by one. -/
theorem padicValNat_clean_body_upper_bound
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) ≤ 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  by_contra hnot
  have htwo : 2 ≤ padicValNat q (g * GN5 g y) := by
    omega
  have hsq : q ^ 2 ∣ g * GN5 g y :=
    (@padicValNat_dvd_iff_le q (Fact.mk h.prime) (g * GN5 g y) 2 hBodyNe).mpr htwo
  exact h.not_sq_dvd_body hsq

/-- The clean-channel contradiction, proved independently through `padicValNat`. -/
theorem counterexample_false_of_clean_GN5Channel_by_padicValNat
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z := Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  have hBodyEq : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hBodyEq]
    exact hClean.dvd_body
  have hqDivX : q ∣ x := hClean.prime.dvd_of_dvd_pow hqDivPow
  have hlower : 5 ≤ padicValNat q (x ^ 5) :=
    padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
  have hupper : padicValNat q (Body5 (z - y) y) ≤ 1 := by
    simpa [Body5] using padicValNat_clean_body_upper_bound hClean
  rw [hBodyEq] at hupper
  omega

end DkMath.FLT.Five
