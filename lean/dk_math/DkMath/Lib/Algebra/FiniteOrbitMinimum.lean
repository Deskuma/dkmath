/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Finset.Max
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.Algebra.FiniteOrbitMinimum"

/-!
# 有限軌道では、負の値をさらに下げ続けられない

群の倍点や付値を使う前に、有限集合上の最小値の議論を独立させる。
有限集合Sを保存する写像stepが、値が負の時にその値を厳密に下げるなら、
S上の値は全て非負である。最小値を持つこと以外に、単射性や全射性は不要。

後半はnQ=0という有限周期へ適用する。周期nの剰余で代表を選ぶため、
stepが倍点である場合にも軌道から外れない。これは楕円曲線を使わない群の原理である。
-/
namespace DkMath.Lib.Algebra.FiniteOrbitMinimum

/-- 有限集合を保つ写像が負の値をさらに下げるなら、その集合上に負の値はない。 -/
theorem nonnegative_of_strict_drop {α : Type*} (S : Finset α) (step : α → α)
    (f : α → ℤ) (hstep : ∀ a ∈ S, step a ∈ S)
    (hdrop : ∀ a ∈ S, f a < 0 → f (step a) < f a) :
    ∀ a ∈ S, 0 ≤ f a := by
  intro a ha
  obtain ⟨b, hb, hmin⟩ := S.exists_min_image f ⟨a, ha⟩
  by_contra h
  have hneg : f b < 0 := lt_of_le_of_lt (hmin a ha) (lt_of_not_ge h)
  exact (not_lt_of_ge (hmin (step b) (hstep b hb))) (hdrop b hb hneg)

/-- nQ=0の有限軌道上で、負の値を倍点が下げるなら全ての倍点の値は非負。
正の周期nを保持し、無限軌道に有限性を仮定したことにはしない。 -/
theorem nsmul_nonnegative_of_double_drop {G : Type*} [AddCommGroup G]
    (Q : G) (n : ℕ) (hn : 0 < n) (hQ : n • Q = 0) (f : G → ℤ)
    (hdrop : ∀ k : ℕ, f (k • Q) < 0 → f (2 • (k • Q)) < f (k • Q)) (k : ℕ) :
    0 ≤ f (k • Q) := by
  have hmod (j : ℕ) : (j % n) • Q = j • Q := by
    conv_rhs => rw [← Nat.mod_add_div j n]
    rw [add_nsmul, mul_nsmul, hQ, nsmul_zero, add_zero]
  have h := nonnegative_of_strict_drop (Finset.range n) (fun j => (2 * j) % n)
    (fun j => f (j • Q)) (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hn)) (by
      intro j _ hj
      rw [hmod, mul_comm 2 j, mul_nsmul]
      exact hdrop j hj)
  have hk := h (k % n) (Finset.mem_range.mpr (Nat.mod_lt _ hn))
  rwa [hmod] at hk

end DkMath.Lib.Algebra.FiniteOrbitMinimum
