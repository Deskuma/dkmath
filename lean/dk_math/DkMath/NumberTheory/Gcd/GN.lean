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
