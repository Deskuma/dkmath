/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gcd.Basic
import DkMath.NumberTheory.GcdNext

/-!
# DkMath.NumberTheory.Gcd.GN

`GN` / shifted-difference へ specialized した gcd 系 API の集約入口。

現時点では、既存の `GcdNext.lean` にある specialized 補題を再 export する。
今後 `GcdGN.lean` 系の wrapper や naming 整理をここへ集約していく。
-/

namespace DkMath.NumberTheory.Gcd

open DkMath.NumberTheory.GcdNext

/-- `a := x + u`, `b := u` に specialze した整数 gcd 版。 -/
theorem gcd_boundary_sd_divides_exp_int
    (x u : ℤ) (d : ℕ) (hd : 1 ≤ d) (hcop : Int.gcd (x + u) u = 1) :
    Int.gcd x (Sd (x + u) u d) ∣ d := by
  simpa using DkMath.NumberTheory.GcdNext.gcd_specialized_divides_d x u d hd hcop

/-- `gap = z - y` と置くと、整数環の `GN` は差の冪和 `Sd z y p` と一致する。 -/
theorem gn_sub_eq_sd_int
    {p z y : ℕ} (hp : 0 < p) (hyz : y < z) :
    DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ) =
      DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p := by
  have hGN_nat : z ^ p - y ^ p = (z - y) * DkMath.CosmicFormulaBinom.GN p (z - y) y := by
    simpa using DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N hp hyz
  have hyz_pow : y ^ p ≤ z ^ p := by
    exact Nat.pow_le_pow_left (Nat.le_of_lt hyz) p
  have hGN_int :
      (z : ℤ) ^ p - (y : ℤ) ^ p =
        (((z - y : ℕ) : ℤ) * DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    calc
      (z : ℤ) ^ p - (y : ℤ) ^ p = (↑(z ^ p) : ℤ) - ↑(y ^ p) := by
        simp [Nat.cast_pow]
      _ = ((z ^ p - y ^ p : ℕ) : ℤ) := by
        rw [← Nat.cast_sub hyz_pow]
      _ = (((z - y) * DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℤ) := by
        rw [hGN_nat]
      _ = (((z - y : ℕ) : ℤ) *
            DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
        simp [DkMath.CosmicFormulaBinom.GN]
  have hSd :
      (z : ℤ) ^ p - (y : ℤ) ^ p =
        (((z - y : ℕ) : ℤ) * DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) := by
    simpa [Int.ofNat_sub (Nat.le_of_lt hyz)] using
      (DkMath.Algebra.DiffPow.pow_sub_pow_factor (a := (z : ℤ)) (b := (y : ℤ)) (d := p))
  have hgap_ne0 : (((z - y : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hyz))
  have hmul :
      (((z - y : ℕ) : ℤ) * DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) =
        (((z - y : ℕ) : ℤ) * DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) := by
    rw [← hGN_int, hSd]
  exact Int.eq_of_mul_eq_mul_left hgap_ne0 hmul

/-- `z` と `y` が互いに素なら、`gcd(z - y, GN p (z - y) y)` は `p` を割る。 -/
theorem gcd_gap_GN_dvd_exp_int
    {p z y : ℕ} (hp1 : 1 ≤ p) (hyz : y < z) (hcop : Nat.Coprime z y) :
    Int.gcd (((z - y : ℕ) : ℤ))
      (DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
  have hgcd_zy : Nat.gcd z y = 1 := (Nat.coprime_iff_gcd_eq_one).1 hcop
  have hab : Int.gcd (z : ℤ) (y : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simp [hgcd_zy]
  have hSd :
      Int.gcd (((z - y : ℕ) : ℤ)) (DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) ∣ p := by
    simpa [Int.ofNat_sub (Nat.le_of_lt hyz)] using
      (DkMath.NumberTheory.GcdDiffPow.gcd_divides_d (a := (z : ℤ)) (b := (y : ℤ)) (d := p) hp1 hab)
  rw [gn_sub_eq_sd_int hp1 hyz]
  exact hSd

/-- `z` と `y` が互いに素で `p` が gap を割らなければ、`gap` と `GN` は互いに素。 -/
theorem coprime_gap_GN_of_not_dvd_exp_prime
    {p z y : ℕ} (hp : Nat.Prime p) (hyz : y < z) (hcop : Nat.Coprime z y)
    (hp_gap : ¬ p ∣ (z - y)) :
    Nat.Coprime (z - y) (DkMath.CosmicFormulaBinom.GN p (z - y) y) := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd (z - y) (DkMath.CosmicFormulaBinom.GN p (z - y) y) ≠ 1 := by
    simpa using hg1
  rcases Nat.exists_prime_and_dvd hg_ne1 with ⟨r, hrP, hr_gcd⟩
  have hr_gap : r ∣ (z - y) := by
    exact dvd_trans hr_gcd (Nat.gcd_dvd_left (z - y) (DkMath.CosmicFormulaBinom.GN p (z - y) y))
  have hr_GN : r ∣ DkMath.CosmicFormulaBinom.GN p (z - y) y := by
    exact dvd_trans hr_gcd (Nat.gcd_dvd_right (z - y) (DkMath.CosmicFormulaBinom.GN p (z - y) y))
  have hr_gap_int : (r : ℤ) ∣ (((z - y : ℕ) : ℤ)) := by
    exact_mod_cast hr_gap
  have hr_GN_cast : (r : ℤ) ∣ ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℤ) := by
    exact_mod_cast hr_GN
  have hr_GN_int :
      (r : ℤ) ∣ DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ) := by
    simpa [DkMath.CosmicFormulaBinom.GN] using hr_GN_cast
  have hr_gcd_int :
      r ∣ Int.gcd (((z - y : ℕ) : ℤ))
        (DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    exact Int.dvd_gcd hr_gap_int hr_GN_int
  have hgapgcd_dvd_p :
      Int.gcd (((z - y : ℕ) : ℤ))
        (DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
    exact gcd_gap_GN_dvd_exp_int (hp1 := Nat.succ_le_of_lt hp.pos) (hyz := hyz) (hcop := hcop)
  have hr_dvd_p : r ∣ p := dvd_trans hr_gcd_int hgapgcd_dvd_p
  have hr_eq_p : r = p := (Nat.prime_dvd_prime_iff_eq hrP hp).1 hr_dvd_p
  exact hp_gap (by simpa [hr_eq_p] using hr_gap)

/-- `d = 3` では `gcd(x, GN 3 x u)` は `gcd(x, 3)` に等しい。 -/
theorem gcd_boundary_GN_three_eq_gcd_boundary_three
    {x u : ℕ} (hcop : Nat.Coprime x u) :
    Nat.gcd x (DkMath.CosmicFormulaBinom.GN 3 x u) = Nat.gcd x 3 := by
  rw [GN_three_explicit]
  have hstep : Nat.gcd x (x ^ 2 + 3 * x * u + 3 * u ^ 2) = Nat.gcd x (3 * u ^ 2) := by
    have hx : x ^ 2 + 3 * x * u + 3 * u ^ 2 = 3 * u ^ 2 + (x + 3 * u) * x := by
      ring
    rw [hx, Nat.gcd_add_mul_right_right]
  rw [hstep]
  have hpow : Nat.Coprime x (u ^ 2) := Nat.Coprime.pow_right 2 hcop
  rw [Nat.gcd_comm, hpow.symm.gcd_mul_right_cancel, Nat.gcd_comm]

/-- `d = 3` では `gcd(x, GN 3 x u)` は 3 を割る。 -/
theorem gcd_boundary_GN_three_dvd_three
    {x u : ℕ} (hcop : Nat.Coprime x u) :
    Nat.gcd x (DkMath.CosmicFormulaBinom.GN 3 x u) ∣ 3 := by
  rw [gcd_boundary_GN_three_eq_gcd_boundary_three hcop]
  exact Nat.gcd_dvd_right x 3

/-- `x` と `u` が互いに素で `3 ∤ x` なら、`x` と `GN 3 x u` は互いに素。 -/
theorem coprime_boundary_GN_three_of_coprime_of_not_dvd_three
    {x u : ℕ} (hcop : Nat.Coprime x u) (h3x : ¬ 3 ∣ x) :
    Nat.Coprime x (DkMath.CosmicFormulaBinom.GN 3 x u) := by
  apply (Nat.coprime_iff_gcd_eq_one).2
  have hg : Nat.gcd x (DkMath.CosmicFormulaBinom.GN 3 x u) = Nat.gcd x 3 :=
    gcd_boundary_GN_three_eq_gcd_boundary_three hcop
  have hcases : Nat.gcd x 3 = 1 ∨ Nat.gcd x 3 = 3 := by
    exact (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right x 3)
  rcases hcases with h1 | h3
  · rw [hg]
    exact h1
  · exfalso
    have h3g : 3 ∣ Nat.gcd x 3 := by
      simp [h3]
    have hx3 : 3 ∣ x := dvd_trans h3g (Nat.gcd_dvd_left x 3)
    exact h3x hx3

end DkMath.NumberTheory.Gcd
