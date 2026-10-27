/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
The three-root argument is adapted from WeierstrassTwoTorsionSeparation.lean.
-/
import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionSeparation
import DkMath.Lib.NumberTheory.WeierstrassVeluPair

#print "file: DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots"

/-!
# 2捩れ三根による判別式と接線分母の展開

[DkMath.Lib] 2捩れ三次式の三つの相異なる根を指定すると、その根は重複込みで
すべての根である。したがって三次式、判別式、および曲線上の点の接線式を
同じ根の差で記述できる。核の存在や商写像については仮定しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- [DkMath.Lib] 相異なる三根は三次式の根の多重集合を尽くす。 -/
theorem roots_eq_three (h2 : (2 : k) ≠ 0) (r₁ r₂ r₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    (Cubic.map (RingHom.id k) W.twoTorsionPolynomial).roots = {r₁, r₂, r₃} := by
  classical
  have h4 : (4 : k) ≠ 0 := by
    simpa only [show (2 : k) ^ 2 = 4 by norm_num] using pow_ne_zero 2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hp := Cubic.ne_zero_of_a_ne_zero ha
  have hd := Cubic.natDegree_of_a_ne_zero ha
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
  simpa only [Cubic.map_roots, Polynomial.map_id] using hr

/-- [DkMath.Lib] 2捩れ三次式は首係数4と三つの一次因子に分解する。 -/
theorem polynomial_eval_factor (h2 : (2 : k) ≠ 0) (r₁ r₂ r₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) (x : k) :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * (x - r₁) * (x - r₂) * (x - r₃) := by
  have h4 : (4 : k) ≠ 0 := by
    simpa only [show (2 : k) ^ 2 = 4 by norm_num] using pow_ne_zero 2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hf := Cubic.eq_prod_three_roots ha (roots_eq_three W h2 r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃)
  have he := congrArg (fun p : k[X] => p.eval x) hf
  simpa only [Cubic.map_toPoly, Polynomial.map_id, RingHom.id_apply, twoTorsionPolynomial,
    eval_mul, eval_C, eval_sub, eval_X] using he

/-- [DkMath.Lib] 判別式は三根間の差の積の平方の16倍である。
これは楕円性を仮定する定理ではなく、三根の存在と分離から得られる恒等式。 -/
theorem discriminant_eq_root_differences (h2 : (2 : k) ≠ 0) (r₁ r₂ r₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    W.Δ = 16 * ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 := by
  have h4 : (4 : k) ≠ 0 := by
    simpa only [show (2 : k) ^ 2 = 4 by norm_num] using pow_ne_zero 2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hi := Cubic.discr_eq_prod_three_roots ha
    (roots_eq_three W h2 r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃)
  change W.twoTorsionPolynomial.discr = (4 * 4 * (r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 at hi
  rw [twoTorsionPolynomial_discr] at hi
  have h16 : (16 : k) ≠ 0 := by
    simpa only [show (4 : k) ^ 2 = 16 by norm_num] using pow_ne_zero 2 h4
  apply mul_left_cancel₀ h16
  linear_combination hi

/-- [DkMath.Lib] 曲線上の接線式の平方は、2捩れ三根への距離の積である。
Vélu の分母の積を根の差へ移す際の基本恒等式。 -/
theorem tangent_square_eq_root_product (h2 : (2 : k) ≠ 0) (r₁ r₂ r₃ : k)
    (h₁ : W.twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : W.twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : W.twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (x y : k) (he : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * (x - r₁) * (x - r₂) * (x - r₃) := by
  have hf := polynomial_eval_factor W h2 r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ x
  have hh := (equation_iff _ _).mp he
  simp only [twoTorsionPolynomial, Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    b₂, b₄, b₆] at hf
  linear_combination hf + 4 * hh

end DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
