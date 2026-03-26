/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.ABC.Square
import DkMath.ABC.PadicValNat

#print "file: DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

namespace DkMath.NumberTheory.GcdNext

/--
True generic helper: a nonzero squarefree natural number has `q`-adic valuation at most `1`
at every prime `q`.
-/
lemma padicValNat_le_one_of_squarefree {q n : ℕ}
    (hq_prime : Nat.Prime q) (hn : n ≠ 0) (hsq : Squarefree n) :
    padicValNat q n ≤ 1 := by
  by_contra h_not_le
  have htwo_le : 2 ≤ padicValNat q n := by
    omega
  have hq2_dvd : q ^ 2 ∣ n := by
    exact (ABC.padicValNat_le_iff_dvd hq_prime hn 2).mp htwo_le
  have hfac_le : n.factorization q ≤ 1 := by
    exact (Nat.squarefree_iff_factorization_le_one hn).mp hsq q
  have hfac_ge : 2 ≤ n.factorization q := by
    exact (hq_prime.pow_dvd_iff_le_factorization hn).mp hq2_dvd
  exact (Nat.not_succ_le_self 1) (le_trans hfac_ge hfac_le)

/--
Usable primitive-prime valuation bound under an explicit squarefree hypothesis on the cyclotomic
factor `GN d (a - b) b`.

This is the honest replacement direction for phase-15: rather than claiming a false global
statement, we isolate the precise extra assumption currently needed by the squarefree route.
-/
lemma padicValNat_primitive_prime_factor_le_one_of_squarefree_G {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (hq_ndiv : ¬ q ∣ a - b)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  have _hd_prime := hd_prime
  have _hd_ge := hd_ge
  have _hb := hb
  have _hab := hab
  have _hpnd := hpnd
  have _hq_div := hq_div
  have hd_pos : 0 < d := by
    omega
  let N := GN d (a - b) b
  have hfactor : a ^ d - b ^ d = (a - b) * N := by
    simpa [N] using pow_sub_pow_factor_cosmic_N hd_pos hab_lt
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
  have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
    have hlt : b ^ d < a ^ d := Nat.pow_lt_pow_left hab_lt hd_ne
    exact Nat.sub_ne_zero_of_lt hlt
  have hN_ne : N ≠ 0 := by
    intro hN0
    have htmp : a ^ d - b ^ d = (a - b) * N := hfactor
    rw [hN0] at htmp
    simp only [mul_zero] at htmp
    exact hdiff_ne htmp
  have hpadic_eq : padicValNat q (a ^ d - b ^ d) = padicValNat q N := by
    have hpadic := padicValNat_factorization hd_pos hab_lt hq_prime hfactor hN_ne
    have hzero : padicValNat q (a - b) = 0 := padicValNat.eq_zero_of_not_dvd hq_ndiv
    rw [hzero, zero_add] at hpadic
    exact hpadic
  have hN_le : padicValNat q N ≤ 1 := by
    exact padicValNat_le_one_of_squarefree hq_prime hN_ne (by simpa [N] using hG_sq)
  calc
    padicValNat q (a ^ d - b ^ d) = padicValNat q N := hpadic_eq
    _ ≤ 1 := hN_le

end DkMath.NumberTheory.GcdNext
