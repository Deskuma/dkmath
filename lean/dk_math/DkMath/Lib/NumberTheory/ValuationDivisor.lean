/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

#print "file: DkMath.Lib.NumberTheory.ValuationDivisor"

/-!
# 離散付値の族で定義する、有限支持因子と主因子

[DkMath.Lib] 因子Dは点に整数を割り当てる有限支持関数である。
主因子であるとは、非零の実際の関数fが存在し、全ての点でD(P)=−log(v_P(f))となること。
有限支持性はDの型に保持する。任意の関数の位数の支持が有限であるという追加定理や、
因子の次数が0であることは、この一般の付値族では主張しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationDivisor
open WithZero
variable {A F : Type*} [Field F] (v : A → Valuation F ℤᵐ⁰)

/-- [DkMath.Lib] 有限支持因子の主性。実際の非零関数による全点位数の実現を要求する。 -/
def IsPrincipal (D : A →₀ ℤ) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ P, D P = -log (v P f)

/-- [DkMath.Lib] 零因子は関数1の主因子である。 -/
theorem isPrincipal_zero : IsPrincipal v 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro P
  simp

/-- [DkMath.Lib] 主因子の和は、同じ関数の積で実現する。 -/
theorem IsPrincipal.add {D C : A →₀ ℤ} (hD : IsPrincipal v D) (hC : IsPrincipal v C) :
    IsPrincipal v (D + C) := by
  obtain ⟨f, hf, hD⟩ := hD
  obtain ⟨g, hg, hC⟩ := hC
  refine ⟨f * g, mul_ne_zero hf hg, fun P => ?_⟩
  rw [Finsupp.add_apply, hD, hC, map_mul,
    log_mul ((v P).ne_zero_iff.mpr hf) ((v P).ne_zero_iff.mpr hg)]
  omega

/-- [DkMath.Lib] 主因子の負は、同じ関数の逆数で実現する。 -/
theorem IsPrincipal.neg {D : A →₀ ℤ} (hD : IsPrincipal v D) : IsPrincipal v (-D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨f⁻¹, inv_ne_zero hf, fun P => ?_⟩
  rw [Finsupp.neg_apply, hD, map_inv₀, log_inv]

/-- [DkMath.Lib] 有限支持の主因子全体は、実際の因子群の加法部分群となる。 -/
def principalSubgroup : AddSubgroup (A →₀ ℤ) where
  carrier := {D | IsPrincipal v D}
  zero_mem' := isPrincipal_zero v
  add_mem' := fun hD hC => hD.add v hC
  neg_mem' := fun hD => hD.neg v

end DkMath.Lib.NumberTheory.ValuationDivisor
