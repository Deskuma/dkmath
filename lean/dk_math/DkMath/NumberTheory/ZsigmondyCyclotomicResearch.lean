/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.ABC.Square
import DkMath.ABC.PadicValNat

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

namespace DkMath.NumberTheory.GcdNext


namespace DkMath.NumberTheory.GcdNext

-- -------------- --
-- ※反例を明示化 --
-- -------------- --

/-- 反例: d=3, a=5, b=3, q=7 で `padicValNat q (a^d - b^d) ≤ 1` は成り立たない。 -/
lemma counterexample_padicValNat_diff_le_one :
    ¬ (padicValNat 7 (5 ^ 3 - 3 ^ 3) ≤ 1) := by
  have hdiff_ne0 : (5 ^ 3 - 3 ^ 3 : ℕ) ≠ 0 := by
    decide
  have hq2_dvd : (7 : ℕ) ^ 2 ∣ (5 ^ 3 - 3 ^ 3) := by
    -- 5^3 - 3^3 = 98 = 2 * 7^2
    decide
  have h2_le : 2 ≤ padicValNat 7 (5 ^ 3 - 3 ^ 3) := by
    exact
      (@padicValNat_dvd_iff_le 7 (Fact.mk (by decide : Nat.Prime 7))
          (5 ^ 3 - 3 ^ 3) 2 hdiff_ne0).1 hq2_dvd
  intro hle
  have : (2 : ℕ) ≤ 1 := le_trans h2_le hle
  exact (by decide : ¬ ((2 : ℕ) ≤ 1)) this

/-- よって `squarefree_implies_padic_val_le_one` の現 statement は一般には偽。 -/
lemma squarefree_implies_padic_val_le_one_is_false :
    ¬ (∀ d a b q : ℕ,
        Nat.Prime d → 0 < b → Nat.Coprime a b →
        Nat.Prime q → q ∣ a ^ d - b ^ d →
        padicValNat q (a ^ d - b ^ d) ≤ 1) := by
  intro h
  have h' :
      padicValNat 7 (5 ^ 3 - 3 ^ 3) ≤ 1 := by
    have hd : Nat.Prime 3 := by decide
    have hb : 0 < (3 : ℕ) := by decide
    have hab : Nat.Coprime 5 3 := by decide
    have hq : Nat.Prime 7 := by decide
    have hdiv : (7 : ℕ) ∣ 5 ^ 3 - 3 ^ 3 := by decide
    exact h 3 5 3 7 hd hb hab hq hdiv
  exact counterexample_padicValNat_diff_le_one h'

end DkMath.NumberTheory.GcdNext

/--
Research placeholder.

This statement is currently known to be too strong as written: there are counterexamples to
the naive global implication "squarefree-like input implies `padicValNat ≤ 1`" in this level of
generality. It is intentionally kept as a single research stub so phase-15 callers can point to
one place while the final statement is repaired (typically by strengthening hypotheses or by
replacing this with a more precise primitive-prime valuation theorem).
-/
lemma squarefree_implies_padic_val_le_one (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  have hd_two_le : 2 ≤ d := hd_prime.two_le
  have hq_ne_one : q ≠ 1 := hq_prime.ne_one
  have hq_pos : 0 < q := hq_prime.pos
  have hq_dvd : q ∣ a ^ d - b ^ d := hq_div
  clear hb hab hq_div
  -- [TODO] この命題は現状の一般形では強すぎ、反例がある。
  --        ここでやるべきことは「証明を埋める」ことではなく、必要な仮定を足すか、
  --        primitive-prime valuation のより精密な定理へ置き換えて statement を修正すること。
  sorry

/--
True generic helper: a nonzero squarefree natural number has `q`-adic valuation at most `1`
at every prime `q`.

This is the exact squarefree-to-valuation bridge that the old global placeholder was trying to
approximate, but without the false overreach.
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
statement, we isolate the precise extra assumption currently needed by the research spine.
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

/--
Thin wrapper used by phase-15 bridge code.

This currently delegates to `squarefree_implies_padic_val_le_one`, so the real unresolved work is
statement repair in that theorem rather than local bridge construction.

For a true statement with an explicit additional hypothesis, see
`padicValNat_primitive_prime_factor_le_one_of_squarefree_G`.
-/
lemma padicValNat_primitive_prime_factor_le_one {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (_hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (_hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (_hq_ndiv : ¬ q ∣ a - b) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  have _hd_pos : 0 < d := Nat.zero_lt_of_lt (by omega : 2 < d)
  exact squarefree_implies_padic_val_le_one d a b q hd_prime hb hab hq_prime hq_div

end DkMath.NumberTheory.GcdNext
