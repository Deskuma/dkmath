/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic

set_option linter.style.emptyLine false
set_option linter.style.longLine false

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.GcdNext

namespace DkMath.NumberTheory.PrimitiveBeam

/--
`q` is a primitive prime factor of the difference power `a^d - b^d`.
-/
def PrimitivePrimeFactorOfDiffPow (q a b d : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ a ^ d - b ^ d ∧
  ∀ {k : ℕ}, 0 < k → k < d → ¬ q ∣ a ^ k - b ^ k

/--
Bundle the existing Zsigmondy existence result and the primitive-condition upgrade
into a single proposition-valued API.
-/
lemma exists_primitive_prime_factor_as_prop
    {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b) :
    ∃ q : ℕ, PrimitivePrimeFactorOfDiffPow q a b d := by
  rcases exists_primitive_prime_factor_basic hd_prime hd_ge hab_lt hb hab hpnd with
    ⟨q, hq_prime, hq_div, hq_ndiv⟩
  refine ⟨q, hq_prime, hq_div, ?_⟩
  intro k hk_pos hk_lt
  exact prime_exp_not_dvd_diff_imp_primitive
    hd_prime (Nat.Prime.one_lt hd_prime) hq_prime hab hab_lt hb hq_div hq_ndiv hk_pos hk_lt

/-- A primitive prime factor cannot divide the boundary `a - b`. -/
lemma primitive_prime_not_dvd_boundary
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd1 : 1 < d) :
    ¬ q ∣ a - b := by
  have hnot : ¬ q ∣ a ^ 1 - b ^ 1 := hq.2.2 (show 0 < (1 : ℕ) by decide) hd1
  simpa using hnot

/--
Primitive prime factors move from the difference-power body to the `GN` / Beam side.
-/
lemma primitive_prime_dvd_GN
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    q ∣ GN d (a - b) b := by
  have hq_ndiv : ¬ q ∣ a - b := primitive_prime_not_dvd_boundary hq hd1
  have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
    simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
  have hq_div : q ∣ (a - b) * GN d (a - b) b := by
    rw [← hfactor]
    exact hq.2.1
  rcases (Nat.Prime.dvd_mul hq.1).mp hq_div with hq_ab | hq_GN
  · exact False.elim (hq_ndiv hq_ab)
  · exact hq_GN

/--
For a primitive prime factor, the `q`-adic valuation of `a^d - b^d` is exactly the
valuation of the `GN` factor.
-/
lemma primitive_prime_padic_eq_GN
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a) :
    padicValNat q (a ^ d - b ^ d) = padicValNat q (GN d (a - b) b) := by
  have hq_ndiv : ¬ q ∣ a - b := primitive_prime_not_dvd_boundary hq hd1
  have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
    simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
  have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
    have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
    exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab_lt hd_ne)
  have hGN_ne : GN d (a - b) b ≠ 0 := by
    intro hGN0
    have : a ^ d - b ^ d = (a - b) * GN d (a - b) b := hfactor
    rw [hGN0, mul_zero] at this
    exact hdiff_ne this
  have hpadic :
      padicValNat q (a ^ d - b ^ d) =
        padicValNat q (a - b) + padicValNat q (GN d (a - b) b) := by
    exact
      padicValNat_factorization
        (a := a) (b := b) (d := d) (q := q) (N := GN d (a - b) b)
        hd hab_lt hq.1 hfactor hGN_ne
  have hzero : padicValNat q (a - b) = 0 := padicValNat.eq_zero_of_not_dvd hq_ndiv
  simpa [hzero] using hpadic

/-- Specialized `Body = x * GN d x u` form of `primitive_prime_dvd_GN`. -/
lemma primitive_prime_dvd_GN_body
    {q x u d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d) (hd1 : 1 < d) :
    q ∣ GN d x u := by
  have hx_ne : x ≠ 0 := by
    intro hx0
    have : q ∣ (x + u) - u := by simp [hx0]
    exact primitive_prime_not_dvd_boundary hq hd1 this
  have hx_pos : 0 < x := Nat.pos_of_ne_zero hx_ne
  have hab_lt : u < x + u := by
    simpa [Nat.add_comm] using Nat.lt_add_of_pos_right (n := u) hx_pos
  simpa [Nat.add_sub_cancel] using
    primitive_prime_dvd_GN (a := x + u) (b := u) (d := d) (q := q) hq hd hd1 hab_lt

/-- Specialized `u = 1` bridge for Mersenne / ABC-style examples. -/
lemma primitive_prime_in_beam_for_body_one
    {q x d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + 1) 1 d)
    (hd : 0 < d) (hd1 : 1 < d) :
    q ∣ GN d x 1 := by
  simpa using primitive_prime_dvd_GN_body (q := q) (x := x) (u := 1) (d := d) hq hd hd1

end DkMath.NumberTheory.PrimitiveBeam
