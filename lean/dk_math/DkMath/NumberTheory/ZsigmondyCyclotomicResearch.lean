/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree

#print "file: DkMath.NumberTheory.ZsigmondyCyclotomicResearch"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open DkMath.CosmicFormulaBinom

namespace DkMath.NumberTheory.GcdNext


namespace DkMath.NumberTheory.GcdNext

-- Research の残骸名を「真」に修正（squarefree 仮定を追加）
lemma squarefree_implies_padic_val_le_one (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (hq_ndiv : ¬ q ∣ a - b)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  exact
    padicValNat_primitive_prime_factor_le_one_of_squarefree_G
      (a := a) (b := b) (d := d) (q := q)
      hd_prime hd_ge hab_lt hb hab hpnd hq_prime hq_div hq_ndiv hG_sq

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
