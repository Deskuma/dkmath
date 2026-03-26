/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gcd.Basic
import DkMath.NumberTheory.GcdNext
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree

#print "file: DkMath.NumberTheory.Gcd.GN"

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

/-- `GN` は自然数から整数へのキャストと可換。 -/
theorem gn_natCast_int
    {d x u : ℕ} :
    DkMath.CosmicFormulaBinom.GN d (x : ℤ) (u : ℤ) =
      (DkMath.CosmicFormulaBinom.GN d x u : ℤ) := by
  simp [DkMath.CosmicFormulaBinom.GN]

/-- 自然数入力を整数へ持ち上げた `GN` の `natAbs` は自然数版 `GN` に戻る。 -/
theorem natAbs_gn_natCast_int
    {d x u : ℕ} :
    (DkMath.CosmicFormulaBinom.GN d (x : ℤ) (u : ℤ)).natAbs =
      DkMath.CosmicFormulaBinom.GN d x u := by
  simpa [DkMath.CosmicFormulaBinom.GN] using
    (Int.natAbs_natCast (DkMath.CosmicFormulaBinom.GN d x u))

/-- `gap = z - y` の specialized `natAbs` 版。 -/
theorem natAbs_gn_gap_natCast_int
    {p z y : ℕ} :
    (DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)).natAbs =
      DkMath.CosmicFormulaBinom.GN p (z - y) y := by
  exact natAbs_gn_natCast_int (d := p) (x := z - y) (u := y)

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

/-- `gcd(z - y, GN p (z - y) y)` の自然数版は `p` を割る。 -/
theorem gcd_gap_GN_dvd_exp
    {p z y : ℕ} (hp1 : 1 ≤ p) (hyz : y < z) (hcop : Nat.Coprime z y) :
    Nat.gcd (z - y) (DkMath.CosmicFormulaBinom.GN p (z - y) y) ∣ p := by
  have hgcd_int :
      Int.gcd (((z - y : ℕ) : ℤ))
        (DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
    exact gcd_gap_GN_dvd_exp_int (hp1 := hp1) (hyz := hyz) (hcop := hcop)
  rw [Int.gcd_eq_natAbs] at hgcd_int
  rw [natAbs_gn_gap_natCast_int] at hgcd_int
  exact hgcd_int

/--
If `gcd(x + u, u) = 1` and the boundary `x` is coprime to the exponent `d`,
then the boundary and `GN d x u` are coprime.

This is the direct `gcd(x,GN) ∣ d` wrapper in the natural `Body` coordinates
`(x + u, u)`.
-/
theorem coprime_boundary_GN_of_coprime_add_of_coprime_exp
    {d x u : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x)
    (hcop_add : Nat.Coprime (x + u) u)
    (hcop_xd : Nat.Coprime x d) :
    Nat.Coprime x (DkMath.CosmicFormulaBinom.GN d x u) := by
  have hyz : u < x + u := by omega
  have hgcd_dvd_d :
      Nat.gcd x (DkMath.CosmicFormulaBinom.GN d x u) ∣ d := by
    simpa [Nat.add_sub_cancel_left] using
      (gcd_gap_GN_dvd_exp (p := d) (z := x + u) (y := u) hd1 hyz hcop_add)
  have hgcd_dvd_x :
      Nat.gcd x (DkMath.CosmicFormulaBinom.GN d x u) ∣ x := by
    exact Nat.gcd_dvd_left x (DkMath.CosmicFormulaBinom.GN d x u)
  have hgcd_dvd_one :
      Nat.gcd x (DkMath.CosmicFormulaBinom.GN d x u) ∣ 1 := by
    rw [← hcop_xd.gcd_eq_one]
    exact Nat.dvd_gcd hgcd_dvd_x hgcd_dvd_d
  exact (Nat.coprime_iff_gcd_eq_one).2 (Nat.eq_one_of_dvd_one hgcd_dvd_one)

/--
Wrapper from coprime `Body` coordinates to the squarefree-`GN` obstruction
theorem on the `CosmicFormula` side.

This is an FLT-shaped local refuter in `Body` coordinates:
once the squarefree `GN` hypothesis is available, it directly rules out
`(x + u)^d - u^d = t^d`.
-/
theorem body_not_perfect_pow_of_squarefree_GN_of_coprime_add
    {d x u : ℕ}
    (hd : 1 < d) (hx : 0 < x)
    (hcop_add : Nat.Coprime (x + u) u)
    (hcop_xd : Nat.Coprime x d)
    (hGN_gt : 1 < DkMath.CosmicFormulaBinom.GN d x u)
    (hSq : Squarefree (DkMath.CosmicFormulaBinom.GN d x u)) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x + u) ^ d - u ^ d = t ^ d := by
  exact DkMath.CosmicFormulaBinom.body_not_perfect_pow_of_squarefree_GN
    hd hGN_gt
    (coprime_boundary_GN_of_coprime_add_of_coprime_exp
      (hd1 := Nat.le_of_lt hd) (hx := hx)
      (hcop_add := hcop_add) (hcop_xd := hcop_xd))
    hSq

/--
Primitive-prime obstruction wrapper in `Body` coordinates.

This is the `a := x + u`, `b := u` specialization of the pure diff-side
primitive-prime obstruction.

Again this is already FLT-shaped: it is not the global FLT theorem, but it
directly kills one local branch with conclusion
`¬ ∃ t, 0 < t ∧ (x + u)^d - u^d = t^d`.
-/
theorem body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop_add : Nat.Coprime (x + u) u)
    (hnd : ¬ d ∣ x) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x + u) ^ d - u ^ d = t ^ d := by
  have hlt : u < x + u := by omega
  simpa [Nat.add_sub_cancel_left] using
    (DkMath.NumberTheory.PrimitiveBeam.primitive_prime_factor_forbids_perfect_pow_diff
      (a := x + u) (b := u) (d := d)
      hd_prime hd_ge hlt hu hcop_add (by simpa [Nat.add_sub_cancel_left] using hnd))

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

/-- `q ∤ gap` なら、差の冪の `q`-進付値は `GN` 側の `q`-進付値と一致する。 -/
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
    {p z y q : ℕ} (hp2 : 2 ≤ p) (hyz : y < z) (hy : 0 < y)
    (hqP : Nat.Prime q) (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    padicValNat q (z ^ p - y ^ p) =
      padicValNat q (DkMath.CosmicFormulaBinom.GN p (z - y) y) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp2
  have hdiff_ne0 : z ^ p - y ^ p ≠ 0 := by
    have hyz_pow_lt : y ^ p < z ^ p := by
      exact Nat.pow_lt_pow_left hyz (Nat.ne_of_gt hp_pos)
    exact Nat.sub_ne_zero_of_lt hyz_pow_lt
  have hfactor :
      z ^ p - y ^ p = (z - y) * DkMath.CosmicFormulaBinom.GN p (z - y) y := by
    simpa using DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
      hp_pos hyz
  have hGN_ne : DkMath.CosmicFormulaBinom.GN p (z - y) y ≠ 0 := by
    exact DkMath.CosmicFormulaBinom.GN_ne_zero_nat_of_two_le
      (d := p) (x := z - y) (u := y) hp2 (Nat.sub_pos_of_lt hyz) hy
  have hpadic :=
    DkMath.NumberTheory.GcdNext.padicValNat_factorization
      hp_pos hyz hqP hfactor hGN_ne
  have hzero : padicValNat q (z - y) = 0 := by
    exact padicValNat.eq_zero_of_not_dvd hq_not_dvd_gap
  simpa [hzero] using hpadic

/-- Squarefree な非零自然数は、任意の素数 `q` に対して 2 段 lift を持たない。 -/
theorem not_sq_dvd_of_squarefree {q X : ℕ}
    (hqP : Nat.Prime q) (hX_ne : X ≠ 0) (hSq : Squarefree X) :
    ¬ q ^ 2 ∣ X := by
  intro hq2_dvd
  have hVal : padicValNat q X ≤ 1 :=
    DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree hqP hX_ne hSq
  have h2_le : 2 ≤ padicValNat q X := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hqP) X 2 hX_ne).1 hq2_dvd
  exact (not_le_of_gt h2_le) hVal

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
