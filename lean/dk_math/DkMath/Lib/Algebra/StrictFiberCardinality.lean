/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset

#print "file: DkMath.Lib.Algebra.StrictFiberCardinality"

/-!
# 一つの小さいファイバーから、総数の厳密不等式を得る

[DkMath.Lib] 全ファイバーがn点以下で、その一つがn点未満なら、
元の有限集合の個数は像の候補数×nより真に小さい。
楕円曲線ではx座標のファイバーは高々2点、反転固定点のファイバーは1点となる。
-/
namespace DkMath.Lib.Algebra.StrictFiberCardinality
open scoped BigOperators

/-- [DkMath.Lib] ファイバーごとの上界と一つの厳密上界を、全体の厳密上界へ足し合わせる。 -/
theorem card_lt_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (n : ℕ)
    (hmap : ∀ a ∈ s, f a ∈ t)
    (hbound : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ n)
    (b : β) (hb : b ∈ t) (hstrict : (s.filter (fun a => f a = b)).card < n) :
    s.card < n * t.card := by
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have h := Finset.sum_lt_sum hbound ⟨b, hb, hstrict⟩
  simpa only [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm] using h

end DkMath.Lib.Algebra.StrictFiberCardinality
