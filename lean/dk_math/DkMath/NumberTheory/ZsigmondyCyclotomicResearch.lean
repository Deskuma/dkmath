/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

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
