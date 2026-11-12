/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Reconstructed from the three-root argument in
S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero.lean,
blob f66586eb1bb501437c601e7af2bd9a79c0f77a48.
Modified: arbitrary Weierstrass model and actual three affine solutions;
no cyclic-kernel definitions, macros or external proof imports.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic.LinearCombination

#print "file: DkMath.Lib.NumberTheory.WeierstrassTwoTorsionSeparation"

/-!
# 三つの相異なる反転固定点から、標的の判別式非零へ

[DkMath.Lib] 方程式上の点がy=negY(x,y)を満たすと、そのxは2捩れ三次式の根となる。
相異なる三根があれば三次式の判別式は非零であり、曲線のΔも非零となる。
非特異性を結論する前なので、入力はPointやtorsionByでなくEquationと反転固定条件で記述する。
三根の分離を実際の有限核から供給する仕事は、この一般判定の入力とは区別する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassTwoTorsionSeparation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- [DkMath.Lib] 方程式上の反転固定点のx座標は、2捩れ三次式の根である。
標的の楕円性や2の可逆性は、この恒等式には不要。 -/
theorem root_of_equation_of_neg_fixed {x y : k} (he : W.toAffine.Equation x y)
    (hn : y = -y - W.a₁ * x - W.a₃) : W.twoTorsionPolynomial.toPoly.eval x = 0 := by
  have h := (equation_iff _ _).mp he
  have hz : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hn
  simp only [twoTorsionPolynomial, Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    b₂, b₄, b₆]
  linear_combination -4 * h + (2 * y + W.a₁ * x + W.a₃) * hz

/-- [DkMath.Lib] 2が非零の体で、2捩れ三次式に相異なる三根があればΔ≠0。
根の存在・分離を省略せず、重根を持つ特異三次曲線を排除する。 -/
theorem discriminant_ne_zero_of_three_roots (h2 : (2 : k) ≠ 0) (r₁ r₂ r₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) : W.Δ ≠ 0 := by
  classical
  have h4 : (4 : k) ≠ 0 := by simpa only [show (2 : k) ^ 2 = 4 by norm_num] using pow_ne_zero 2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hp : W.twoTorsionPolynomial.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have hd : W.twoTorsionPolynomial.toPoly.natDegree = 3 := Cubic.natDegree_of_a_ne_zero ha
  have hnodup : ({r₁, r₂, r₃} : Multiset k).Nodup := by
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, not_or, Multiset.nodup_singleton]
    exact ⟨⟨h₁₂, h₁₃⟩, h₂₃, True.intro⟩
  have hsub : ({r₁, r₂, r₃} : Multiset k) ≤ W.twoTorsionPolynomial.toPoly.roots := by
    apply (Multiset.le_iff_subset hnodup).mpr
    intro r hr
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact (mem_roots hp).mpr h₁
    · exact (mem_roots hp).mpr h₂
    · exact (mem_roots hp).mpr h₃
  have hr : W.twoTorsionPolynomial.toPoly.roots = {r₁, r₂, r₃} := by
    apply (Multiset.eq_of_le_of_card_le hsub ?_).symm
    simpa only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, hd]
      using Polynomial.card_roots' W.twoTorsionPolynomial.toPoly
  have hc : (Cubic.map (RingHom.id k) W.twoTorsionPolynomial).roots = {r₁, r₂, r₃} := by
    simpa only [Cubic.map_roots, Polynomial.map_id] using hr
  have hn := (Cubic.discr_ne_zero_iff_roots_ne ha hc).mpr ⟨h₁₂, h₁₃, h₂₃⟩
  intro hΔ
  exact hn (by rw [twoTorsionPolynomial_discr, hΔ, mul_zero])

/-- [DkMath.Lib] 同じモデルの三つの実際の方程式解と反転固定条件を、非特異性の判定へ接続する。 -/
theorem discriminant_ne_zero_of_three_fixed_solutions (h2 : (2 : k) ≠ 0)
    (x y : Fin 3 → k) (he : ∀ i, W.toAffine.Equation (x i) (y i))
    (hn : ∀ i, y i = -y i - W.a₁ * x i - W.a₃) (hx : Function.Injective x) : W.Δ ≠ 0 :=
  discriminant_ne_zero_of_three_roots W h2 (x 0) (x 1) (x 2)
    (root_of_equation_of_neg_fixed W (he 0) (hn 0))
    (root_of_equation_of_neg_fixed W (he 1) (hn 1))
    (root_of_equation_of_neg_fixed W (he 2) (hn 2))
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hx h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hx h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hx h))

end DkMath.Lib.NumberTheory.WeierstrassTwoTorsionSeparation
