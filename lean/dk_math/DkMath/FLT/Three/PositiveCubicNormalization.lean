/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.PrimitiveCubicClosure

#print "file: DkMath.FLT.Three.PositiveCubicNormalization"

namespace DkMath.FLT.Three

/-!
# Positive-natural normalization for the cubic endpoint

This module reduces an arbitrary positive cubic solution by `gcd a b` and
feeds the resulting primitive packet to the independent Three tower closure.
It does not modify the legacy `DkMath.FLT.Main` surface.
-/

/-- Normalize a positive cubic solution to a positive primitive cubic pack. -/
theorem exists_primitiveCubicPack_of_positive_solution
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ a' b' c' : ℕ, PrimitiveCubicPack a' b' c' := by
  let d := Nat.gcd a b
  let a' := a / d
  let b' := b / d
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have hd3c3 : d ^ 3 ∣ c ^ 3 := by
    have hd3a3 : d ^ 3 ∣ a ^ 3 := pow_dvd_pow_of_dvd hda 3
    have hd3b3 : d ^ 3 ∣ b ^ 3 := pow_dvd_pow_of_dvd hdb 3
    rw [← hEq]
    exact dvd_add hd3a3 hd3b3
  have hdc : d ∣ c := by
    have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd (a := d ^ 3) (b := c)
      (by decide : 3 ≠ 0)).mp hd3c3
    simpa using hroot
  let c' := c / d
  have haEq : d * a' = a := Nat.mul_div_cancel' hda
  have hbEq : d * b' = b := Nat.mul_div_cancel' hdb
  have hcEq : d * c' = c := Nat.mul_div_cancel' hdc
  have haPos : 0 < a' := Nat.div_pos (Nat.le_of_dvd ha hda) hdPos
  have hbPos : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb hdb) hdPos
  have hcPos : 0 < c' := Nat.div_pos (Nat.le_of_dvd hc hdc) hdPos
  have hcop : Nat.Coprime a' b' := by
    exact Nat.coprime_div_gcd_div_gcd hdPos
  have hEq' : a' ^ 3 + b' ^ 3 = c' ^ 3 := by
    have hscaled : d ^ 3 * (a' ^ 3 + b' ^ 3) = d ^ 3 * c' ^ 3 := by
      calc
        d ^ 3 * (a' ^ 3 + b' ^ 3) = (d * a') ^ 3 + (d * b') ^ 3 := by
          ring
        _ = a ^ 3 + b ^ 3 := by rw [haEq, hbEq]
        _ = c ^ 3 := hEq
        _ = (d * c') ^ 3 := by rw [hcEq]
        _ = d ^ 3 * c' ^ 3 := by ring
    exact Nat.mul_left_cancel (pow_pos hdPos 3) hscaled
  exact ⟨a', b', c', {
    hx := haPos
    hy := hbPos
    hz := hcPos
    coprime_xy := hcop
    equation := hEq' }⟩

/-- No positive natural numbers solve the cubic Fermat equation. -/
theorem fermatThree_no_positive_solution
    (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hEq
  rcases exists_primitiveCubicPack_of_positive_solution ha hb hc hEq with
    ⟨a', b', c', p⟩
  exact primitiveCubicPack_false p

end DkMath.FLT.Three
