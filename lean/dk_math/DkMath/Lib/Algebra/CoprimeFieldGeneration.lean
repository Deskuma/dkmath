/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Relrank

#print "file: DkMath.Lib.Algebra.CoprimeFieldGeneration"

/-!
# NOTE-032-005C₂c₁: 互いに素な相対次数による同じ中間体の生成

[DkMath.Lib] A,B⊆Nで[N:A],[N:B]が互いに素なら、AとBはNを生成する。
共通の中間体A∨Bの指数が両次数を割ることから得る。
周囲の体Lの次数を使う場合は、共通因子[L:N]が非零であることを保持して消去する。
次数2d,3dをまだ供給できていない利用側で、この条件を隠してはならない。
-/
namespace DkMath.Lib.Algebra.CoprimeFieldGeneration
open IntermediateField
variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- [DkMath.Lib] 二つの包含した中間体の相対次数が互いに素なら、その上限は同じNとなる。 -/
theorem sup_eq_of_coprime (A B N : IntermediateField k L) (hA : A ≤ N) (hB : B ≤ N)
    (hc : Nat.Coprime (A.relfinrank N) (B.relfinrank N)) : A ⊔ B = N := by
  have hdA : (A ⊔ B).relfinrank N ∣ A.relfinrank N := relfinrank_dvd_of_le_left N le_sup_left
  have hdB : (A ⊔ B).relfinrank N ∣ B.relfinrank N := relfinrank_dvd_of_le_left N le_sup_right
  have h1 : (A ⊔ B).relfinrank N = 1 :=
    Nat.dvd_one.mp (hc.gcd_eq_one ▸ Nat.dvd_gcd hdA hdB)
  exact le_antisymm (sup_le hA hB) (relfinrank_eq_one_iff.mp h1)

/-- [DkMath.Lib] 周囲の同じ体での次数mdとdから、相対次数mを計算する。
d=0という無限拡大時のfinrankの便宜値を、消去に使わない。 -/
theorem relfinrank_eq_of_ambient_degrees (A N : IntermediateField k L) (hA : A ≤ N)
    (m d : ℕ) (hd : d ≠ 0) (hN : Module.finrank N L = d)
    (hdeg : Module.finrank A L = m * d) : A.relfinrank N = m := by
  have ht := relfinrank_mul_finrank_top hA
  rw [hN, hdeg] at ht
  exact mul_right_cancel₀ hd ht

/-- [DkMath.Lib] 同じ共通因子dを持つ互いに素な次数md,ndから、中間体Nの生成を得る。
両方の次数と共通因子の非零性は数学的な入力として保持する。 -/
theorem sup_eq_of_ambient_degrees (A B N : IntermediateField k L) (hA : A ≤ N) (hB : B ≤ N)
    (m n d : ℕ) (hc : Nat.Coprime m n) (hd : d ≠ 0) (hN : Module.finrank N L = d)
    (hdegA : Module.finrank A L = m * d) (hdegB : Module.finrank B L = n * d) : A ⊔ B = N := by
  apply sup_eq_of_coprime A B N hA hB
  rw [relfinrank_eq_of_ambient_degrees A N hA m d hd hN hdegA,
    relfinrank_eq_of_ambient_degrees B N hB n d hd hN hdegB]
  exact hc

end DkMath.Lib.Algebra.CoprimeFieldGeneration
