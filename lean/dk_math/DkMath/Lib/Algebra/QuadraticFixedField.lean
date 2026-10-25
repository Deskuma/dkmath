/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

#print "file: DkMath.Lib.Algebra.QuadraticFixedField"

/-!
# 二次拡大の明暗: 動く元と固定される元

[DkMath.Lib] N/Aの次数が2なら、Aを固定しNのある元を動かす自己同型の
N内の固定元はちょうどAに属する。周囲の体の自己同型を使うので、
Nへの制限自己同型を新しいデータとして選ぶ必要はない。
-/
namespace DkMath.Lib.Algebra.QuadraticFixedField
open IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- [DkMath.Lib] 同じ周囲の体内の二次中間拡大で、非自明な反射の固定元は基礎体に戻る。
次数2と動く元は証明に使い、任意の自己同型の固定元へ無条件には拡張しない。 -/
theorem mem_of_fixed (A N : IntermediateField k F) (hAN : A ≤ N)
    (hdeg : A.relfinrank N = 2) (ι : F ≃ₐ[k] F)
    (hfix : ∀ a ∈ A, ι a = a) (y : F) (hy : y ∈ N) (hmove : ι y ≠ y)
    {z : F} (hz : z ∈ N) (hzfix : ι z = z) : z ∈ A := by
  let M : IntermediateField k F :=
    { carrier := {x | ι x = x}
      zero_mem' := map_zero ι
      one_mem' := map_one ι
      add_mem' := by intro a b ha hb; change ι (a + b) = a + b; rw [map_add, ha, hb]
      mul_mem' := by intro a b ha hb; change ι (a * b) = a * b; rw [map_mul, ha, hb]
      inv_mem' := by intro a ha; change ι a⁻¹ = a⁻¹; rw [map_inv₀, ha]
      algebraMap_mem' := ι.commutes }
  let J := N ⊓ M
  have hAJ : A ≤ J := le_inf hAN hfix
  have ht := relfinrank_mul_relfinrank hAJ (show J ≤ N from inf_le_left)
  rw [hdeg] at ht
  have hd : J.relfinrank N ∣ 2 := ⟨A.relfinrank J, by rw [mul_comm]; exact ht.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · have hNJ := relfinrank_eq_one_iff.mp h1
    exact (hmove (hNJ hy).2).elim
  · rw [h2] at ht
    have h1 : A.relfinrank J = 1 := by omega
    exact (relfinrank_eq_one_iff.mp h1) ⟨hz, hzfix⟩

end DkMath.Lib.Algebra.QuadraticFixedField
