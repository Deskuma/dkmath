/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed"

/-!
# 有限体上の Frobenius 固定元を同じ有限体へ降ろす

`x^#F=x` を満たす拡大体の元は `F` の像に入る。
有限体の全元に加えてもう一つ根があると `X^#F-X` の次数を越える。
拡大体の有限性・代数閉性は要求しない。
-/

namespace DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed

open Polynomial

/-- 実際の有限体埋込みの像は `#F` 乗で固定される元の全体。 -/
theorem exists_preimage_of_pow_card_eq (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K]
    (x : K) (hx : x ^ Fintype.card F = x) : ∃ a : F, algebraMap F K a = x := by
  classical
  by_contra he
  push Not at he
  let f : Option F → K := fun z => z.elim x (algebraMap F K)
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (he b hab.symm).elim
    | some a =>
      cases b with
      | none => exact (he a hab).elim
      | some b => exact congrArg some ((algebraMap F K).injective hab)
  let P : K[X] := X ^ Fintype.card F - X
  have hroot (z : Option F) : P.eval (f z) = 0 := by
    cases z with
    | none => simpa only [P, f, Option.elim_none, eval_sub, eval_pow, eval_X, sub_eq_zero] using hx
    | some a =>
      simp only [P, f, Option.elim_some, eval_sub, eval_pow, eval_X]
      rw [← map_pow, FiniteField.pow_card, sub_self]
  have hd : P.natDegree < Fintype.card (Option F) := by
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card, Fintype.card_option]
    omega
  exact (FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card)
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hf hroot hd)

end DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed
