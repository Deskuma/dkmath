/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenAdicPowerSplit

#print "file: DkMath.FLT.Seven.SevenAdicNestedPowerSplit"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

/-- A second use of the existing coprime power extraction. The extra four
factors of seven turn the exceptional allocation into a pure seventh power;
the prime-free residual factor receives no seven. -/
theorem exists_nested_seventh_allocation {M a b : ℕ}
    (haPos : 0 < a) (hbPos : 0 < b) (habCoprime : Nat.Coprime a b)
    (hb7 : ¬ 7 ∣ b) (hdist : 7 ^ 4 * M ^ 7 = 7 * a * b) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      a = 7 ^ 3 * r ^ 7 ∧ b = s ^ 7 ∧ M = r * s := by
  have hcop : Nat.Coprime (7 ^ 4 * a) b :=
    (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
      hb7).pow_left 4).mul_left habCoprime
  have hab : (7 ^ 4 * a) * b = (7 * M) ^ 7 := by
    have h := hdist
    have hcancel : a * b = 7 ^ 3 * M ^ 7 := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7)
      nlinarith [h]
    rw [mul_assoc, hcancel, mul_pow]
    ring
  rcases seventh_power_factor_split hcop hab with ⟨⟨R, hR⟩, ⟨s, hs⟩⟩
  have h7R : 7 ∣ R := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow
    (by rw [← hR]; exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 7 ^ 4) _)
  rcases h7R with ⟨r, hr⟩
  have ha : a = 7 ^ 3 * r ^ 7 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7 ^ 4)
    rw [hR, hr, mul_pow]
    ring
  have hM : M = r * s := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7 ^ 4)
    have h := hdist
    rw [ha, hs] at h
    simpa only [mul_pow] using (show 7 ^ 4 * M ^ 7 = 7 ^ 4 * (r * s) ^ 7 by
      calc
        _ = 7 * (7 ^ 3 * r ^ 7) * s ^ 7 := h
        _ = _ := by ring)
  have hrpos : 0 < r := by
    by_contra hz
    have : r = 0 := Nat.eq_zero_of_not_pos hz
    have hapos := haPos
    rw [ha, this] at hapos
    norm_num at hapos
  have hspos : 0 < s := by
    by_contra hz
    have : s = 0 := Nat.eq_zero_of_not_pos hz
    have hb := hbPos
    rw [hs, this] at hb
    norm_num at hb
  have hrs : Nat.Coprime r s := habCoprime.of_dvd
    (by rw [ha]; exact dvd_mul_of_dvd_right (dvd_pow_self r (by decide)) _)
    (by rw [hs]; exact dvd_pow_self s (by decide))
  exact ⟨r, s, hrpos, hspos, hrs, ha, hs, hM⟩

/-- The existing GN packet uses the common arithmetic allocation unchanged.
The same helper also applies to the prescribed-carrier alternating split. -/
theorem SevenAdicPowerSplit.exists_nested_seventh_roots {M u v : ℕ}
    (split : SevenAdicPowerSplit (7 ^ 4 * M ^ 7) u v) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      split.a = 7 ^ 3 * r ^ 7 ∧ split.b = s ^ 7 ∧ M = r * s :=
  exists_nested_seventh_allocation split.a_pos split.b_pos
    split.coprime_a_b split.seven_not_dvd_b split.distinguished_eq

/-- The nested split makes the gap a seventh power of a seventh power,
with all twenty-seven factors of seven displayed. -/
theorem SevenAdicPowerSplit.nested_gap_residual {M u v r s : ℕ}
    (split : SevenAdicPowerSplit (7 ^ 4 * M ^ 7) u v)
    (ha : split.a = 7 ^ 3 * r ^ 7) (hb : split.b = s ^ 7) :
    v - u = 7 ^ 27 * r ^ 49 ∧ GN 7 (v - u) u = 7 * s ^ 49 := by
  constructor
  · rw [split.gap_eq, ha, mul_pow, ← pow_mul, ← pow_mul]
    ring
  · rw [split.residual_eq, hb, ← pow_mul]

/-- A division-safe normalization of the existing explicit GN expansion. -/
theorem GN_seven_div_seven_eq_head_add (d u : ℕ) (h7 : 7 ∣ d) :
    GN 7 d u / 7 = u ^ 6 + (d / 7) *
      (d ^ 5 + 7 * d ^ 4 * u + 21 * d ^ 3 * u ^ 2 +
        35 * d ^ 2 * u ^ 3 + 35 * d * u ^ 4 + 21 * u ^ 5) := by
  have hd : d = 7 * (d / 7) := (Nat.mul_div_cancel' h7).symm
  have hGN : 7 ∣ GN 7 d u := by
    rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
    exact dvd_add (dvd_mul_of_dvd_left h7 _) (dvd_mul_right 7 _)
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7)
  rw [Nat.mul_div_cancel' hGN, GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  conv_lhs => lhs; lhs; rw [hd]
  ring

/-- Removing the unique factor seven retains the full modulus `d/7`, not
only a small fixed seven-power shadow. -/
theorem GN_seven_div_seven_modEq_head (d u : ℕ) (h7 : 7 ∣ d) :
    Nat.ModEq (d / 7) (GN 7 d u / 7) (u ^ 6) := by
  rw [GN_seven_div_seven_eq_head_add d u h7]
  unfold Nat.ModEq
  simp [Nat.add_mod]

/-- For a fixed gap the GN residual is strictly increasing in the positive
endpoint coordinate, including when the gap is zero. -/
theorem GN_seven_unit_strictMono (d : ℕ) : StrictMono (fun u : ℕ => GN 7 d u) := by
  intro u v huv
  change GN 7 d u < GN 7 d v
  rw [GN_seven_eq_gap_mul_add_seven_mul_y_pow_six,
    GN_seven_eq_gap_mul_add_seven_mul_y_pow_six]
  have hp : u ^ 6 < v ^ 6 :=
    (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mpr huv
  have ht :
      d * (d ^ 5 + 7 * d ^ 4 * u + 21 * d ^ 3 * u ^ 2 +
        35 * d ^ 2 * u ^ 3 + 35 * d * u ^ 4 + 21 * u ^ 5) ≤
      d * (d ^ 5 + 7 * d ^ 4 * v + 21 * d ^ 3 * v ^ 2 +
        35 * d ^ 2 * v ^ 3 + 35 * d * v ^ 4 + 21 * v ^ 5) := by
    gcongr
  omega

/-- Each factor allocation has at most one endpoint solving the residual
equation. This is uniqueness, without existence or enumeration. -/
theorem nestedResidual_unit_unique {r s u v : ℕ}
    (hu : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49)
    (hv : GN 7 (7 ^ 27 * r ^ 49) v = 7 * s ^ 49) : u = v :=
  (GN_seven_unit_strictMono _).injective (hu.trans hv.symm)

/-- At exponent seven every coefficient in the higher polynomial is itself
divisible by seven when the gap is. The normalized congruence therefore
retains even the full gap modulus. -/
theorem GN_seven_div_seven_modEq_gap (d u : ℕ) (h7 : 7 ∣ d) :
    Nat.ModEq d (GN 7 d u / 7) (u ^ 6) := by
  let P := d ^ 5 + 7 * d ^ 4 * u + 21 * d ^ 3 * u ^ 2 +
    35 * d ^ 2 * u ^ 3 + 35 * d * u ^ 4 + 21 * u ^ 5
  have hP : 7 ∣ P := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hm := Nat.dvd_iff_mod_eq_zero.mp h7
    dsimp [P]
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hm]
  have hd : d = 7 * (d / 7) := (Nat.mul_div_cancel' h7).symm
  have heq : (d / 7) * P = d * (P / 7) := by
    calc
      _ = (d / 7) * (7 * (P / 7)) := by rw [Nat.mul_div_cancel' hP]
      _ = _ := by
        conv_rhs => lhs; rw [hd]
        ring
  rw [GN_seven_div_seven_eq_head_add d u h7]
  change Nat.ModEq d (u ^ 6 + (d / 7) * P) (u ^ 6)
  rw [heq]
  unfold Nat.ModEq
  simp [Nat.add_mod]

end DkMath.FLT.Seven
