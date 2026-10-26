/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPair
import DkMath.Lib.Algebra.ValuationVeluExpansion

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelVeluEquation"

/-!
# 同じX_H,Y_HのVélu係数方程式

[DkMath.Lib] 反転対和の二段有限展開から、候補方程式の残差はOで厳密に消える。
残差は同じHで不変、Hの外で正則なので全点で正則。従って定数であり、Oでの消滅から零。
巡回核、形式級数、微分、明示的な全核の分母積を用いない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation WeierstrassVeluPair WeierstrassVeluPolynomial
open DkMath.Lib.Algebra.ValuationVeluExpansion
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelVeluEquation {α : Type*} :
    DecidableEq α := Classical.decEq _

omit [CharZero K] in
/-- [DkMath.Lib] 同じ核で不変かつ核外正則な関数は、Oで厳密に消えれば零。
既存の全点正則関数の定数判定を、同じ核の対称性と接続する。 -/
theorem eq_zero_of_kernel_regular_lt_one (H : AddSubgroup (Points E))
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (hi : f ∈ kernelFixedField E H)
    (ho : ∀ P : Points E, P ∉ H → pointValuation E P f ≤ 1)
    (h0 : pointValuation E (0 : Points E) f < 1) : f = 0 := by
  obtain ⟨c, he⟩ := eq_const_of_pointValuation_le_one E f (fun P => by
    by_cases hP : P ∈ H
    · rw [pointValuation_kernel_eq_zero E H hi ⟨P, hP⟩]
      exact h0.le
    · exact ho P hP)
  have hc : c = 0 := by
    by_contra hn
    have hv := pointValuation_const_eq_one E (0 : Points E) hn
    rw [he, hv] at h0
    exact lt_irrefl _ h0
  rw [he, hc, map_zero]

omit [CharZero K] in
/-- [DkMath.Lib] 同じ半核の二モーメントと整な剰余による、同じ座標の正確な有限展開。 -/
theorem velu_half_expansion (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H)) :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let V := (pointValuation E (0 : Points E)).valuationSubring
    let W := E.map (algebraMap K F)
    let x := genericX E (AlgebraicClosure K)
    let z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
    let c := algebraMap (AlgebraicClosure K) F
    let T := ∑ Q ∈ halfKernel E H, momentT W (c Q.val.xc)
    let U := ∑ Q ∈ halfKernel E H, momentW W (c Q.val.xc) (c Q.val.yc)
    ∃ A B : F, A ∈ V ∧ B ∈ V ∧
      veluX E H = x + x⁻¹ * (T + x⁻¹ * (U + x⁻¹ * A)) ∧
      2 * veluY E H + W.a₁ * veluX E H + W.a₃ =
        z * (1 + (x⁻¹) ^ 2 * (-T + x⁻¹ * (-2 * U + x⁻¹ * B))) := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let v := pointValuation E (0 : Points E)
  let V := v.valuationSubring.toSubring
  let W := E.map (algebraMap K F)
  let c := algebraMap (AlgebraicClosure K) F
  let x := genericX E (AlgebraicClosure K)
  let h := x⁻¹
  let a : H → F := fun Q => c Q.val.xc
  let t : H → F := fun Q => momentT W (a Q)
  let u : H → F := fun Q => (2 * c Q.val.yc + W.a₁ * a Q + W.a₃) ^ 2
  let w : H → F := fun Q => u Q + a Q * t Q
  let s := halfKernel E H
  have hc (k : AlgebraicClosure K) : c k ∈ V := pointValuation_const_le_one E (0 : Points E) k
  have hcoeff : CoefficientsIn V W := by
    have hm : (E.map (algebraMap K (AlgebraicClosure K))).map c = W := by
      ext <;> exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F _).symm
    rw [← hm]
    exact ⟨hc _, hc _, hc _, hc _, hc _⟩
  have hb₂ : W.b₂ ∈ V := V.add_mem (V.pow_mem hcoeff.1 2) (V.mul_mem (natCast_mem V 4) hcoeff.2.1)
  have hb₄ : W.b₄ ∈ V := V.add_mem (V.mul_mem (natCast_mem V 2) hcoeff.2.2.2.1)
    (V.mul_mem hcoeff.1 hcoeff.2.2.1)
  have ht (Q : H) : t Q ∈ V := V.add_mem
    (V.add_mem (V.mul_mem (natCast_mem V 6) (V.pow_mem (hc _) 2)) (V.mul_mem hb₂ (hc _))) hb₄
  have hu (Q : H) : u Q ∈ V := V.pow_mem
    (V.add_mem (V.add_mem (V.mul_mem (natCast_mem V 2) (hc _)) (V.mul_mem hcoeff.1 (hc _))) hcoeff.2.2.1) 2
  have hx : x ≠ 0 := by simpa only [map_zero] using genericX_ne_const E (0 : AlgebraicClosure K)
  have hxh : x * h = 1 := mul_inv_cancel₀ hx
  have hh : v h < 1 := by
    change pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) x⁻¹ < 1
    rw [map_inv₀, pointValuation_zero_genericX]
    change exp (-2 : ℤ) < exp (0 : ℤ)
    exact exp_lt_exp.mpr (by decide)
  have hd (Q : H) : 1 - a Q * h ≠ 0 := by
    have hv : v (1 - a Q * h) = 1 := v.map_one_sub_of_lt (by
      rw [map_mul]; exact (mul_le_of_le_one_left' (hc Q.val.xc)).trans_lt hh)
    intro he
    rw [he, map_zero] at hv
    exact zero_ne_one hv
  let A := ∑ Q ∈ s, remainderX (a Q) (t Q) (u Q) h
  let B := ∑ Q ∈ s, remainderZ (a Q) (t Q) (u Q) h
  refine ⟨A, B, V.sum_mem (fun Q _ => (remainders_mem v _ _ _ _ (hc _) (ht Q) (hu Q) hh).1),
    V.sum_mem (fun Q _ => (remainders_mem v _ _ _ _ (hc _) (ht Q) (hu Q) hh).2), ?_, ?_⟩
  · rw [veluX_half E H ho]
    change x + ∑ Q ∈ s, (t Q / (x - a Q) + u Q / (x - a Q) ^ 2) =
      x + h * ((∑ Q ∈ s, t Q) + h * ((∑ Q ∈ s, w Q) + h * A))
    congr 1
    simp_rw [(pair_expansion x h _ _ _ hxh (hd _)).1]
    dsimp only [A, w]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring
  · rw [veluZ_half E H ho]
    congr 2
    change (∑ Q ∈ s, (-t Q / (x - a Q) ^ 2 - 2 * u Q / (x - a Q) ^ 3)) =
      h ^ 2 * (-(∑ Q ∈ s, t Q) + h * (-2 * (∑ Q ∈ s, w Q) + h * B))
    simp_rw [(pair_expansion x h _ _ _ hxh (hd _)).2]
    dsimp only [B, w]
    simp only [mul_add, mul_neg, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring

/-- [DkMath.Lib] 同じ半核候補方程式の平方完成残差。関数は既存X_H,Y_Hのままである。 -/
noncomputable def halfKernelPolynomialDefect (H : AddSubgroup (Points E)) [Fintype H] :
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  let J := (halfKernelPolynomialModel E H).map
    (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
  (2 * veluY E H + J.a₁ * veluX E H + J.a₃) ^ 2 - cubic J.b₂ J.b₄ J.b₆ (veluX E H)

/-- [DkMath.Lib] 候補残差はOで厳密に消える。有限の有理式展開で三次式の全非消滅項を相殺する。 -/
theorem halfKernelPolynomialDefect_lt_one (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) : pointValuation E (0 : Points E) (halfKernelPolynomialDefect E H) < 1 := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let c := algebraMap (AlgebraicClosure K) F
  let W := E.map (algebraMap K F)
  let v := pointValuation E (0 : Points E)
  let V := v.valuationSubring.toSubring
  let x := genericX E (AlgebraicClosure K)
  let y := genericY E (AlgebraicClosure K)
  let T := ∑ Q ∈ halfKernel E H, momentT W (c Q.val.xc)
  let U := ∑ Q ∈ halfKernel E H, momentW W (c Q.val.xc) (c Q.val.yc)
  have hc (a : AlgebraicClosure K) : c a ∈ V := pointValuation_const_le_one E (0 : Points E) a
  have hW : (E.map (algebraMap K (AlgebraicClosure K))).map c = W := by
    ext <;> exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F _).symm
  have hm : (halfKernelPolynomialModel E H).map c = polynomialModel W (halfKernel E H)
      (fun Q => c Q.val.xc) (fun Q => c Q.val.yc) := by
    unfold halfKernelPolynomialModel
    rw [polynomialModel_map, hW]
    rfl
  have hT : T ∈ V := by
    apply V.sum_mem
    intro Q _
    rw [← hW, (moments_map c (E.map (algebraMap K (AlgebraicClosure K))) Q.val.xc Q.val.yc).1]
    exact hc _
  have hU : U ∈ V := by
    apply V.sum_mem
    intro Q _
    rw [← hW, (moments_map c (E.map (algebraMap K (AlgebraicClosure K))) Q.val.xc Q.val.yc).2]
    exact hc _
  have hb₂ : W.b₂ ∈ V := by rw [← hW, map_b₂]; exact hc _
  have hb₄ : W.b₄ ∈ V := by rw [← hW, map_b₄]; exact hc _
  have hb₆ : W.b₆ ∈ V := by rw [← hW, map_b₆]; exact hc _
  have hx : x ≠ 0 := by simpa only [map_zero] using genericX_ne_const E (0 : AlgebraicClosure K)
  have hh : v x⁻¹ < 1 := by
    change pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) x⁻¹ < 1
    rw [map_inv₀, pointValuation_zero_genericX]
    change exp (-2 : ℤ) < exp (0 : ℤ)
    exact exp_lt_exp.mpr (by decide)
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure K) F).injective
  have hz := (equation_iff_completedSquare W x y).mp (generic_equation E _)
  obtain ⟨A, B, hA, hB, hX, hZ⟩ := velu_half_expansion E H ho
  have he := defect_lt_one v x (2 * y + W.a₁ * x + W.a₃) (veluX E H)
    (2 * veluY E H + W.a₁ * veluX E H + W.a₃) x⁻¹ T U A B W.b₂ W.b₄ W.b₆
    (mul_inv_cancel₀ hx) hh hT hU hA hB hb₂ hb₄ hb₆ hz hX hZ
  unfold halfKernelPolynomialDefect
  change v _ < 1
  rw [hm]
  dsimp only
  have hb := polynomialModel_b_invariants W (halfKernel E H)
    (fun Q => c Q.val.xc) (fun Q => c Q.val.yc)
  rw [hb.1, hb.2.1, hb.2.2]
  exact he

omit [CharZero K] in
/-- [DkMath.Lib] 同じ候補残差はH不変かつ核外で正則。係数は同じ定数体にある。 -/
theorem halfKernelPolynomialDefect_regular (H : AddSubgroup (Points E)) [Fintype H] :
    halfKernelPolynomialDefect E H ∈ kernelFixedField E H ∧
      ∀ P : Points E, P ∉ H → pointValuation E P (halfKernelPolynomialDefect E H) ≤ 1 := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let c := algebraMap (AlgebraicClosure K) F
  let J := halfKernelPolynomialModel E H
  have hm (A : Subring F) (hc : ∀ a : AlgebraicClosure K, c a ∈ A)
      (hx : veluX E H ∈ A) (hy : veluY E H ∈ A) : halfKernelPolynomialDefect E H ∈ A := by
    have he : halfKernelPolynomialDefect E H =
        (2 * veluY E H + c J.a₁ * veluX E H + c J.a₃) ^ 2 -
          cubic (c J.b₂) (c J.b₄) (c J.b₆) (veluX E H) := by
      simp only [halfKernelPolynomialDefect, map_b₂, map_b₄, map_b₆, map_a₁, map_a₃]
      rfl
    rw [he]
    exact squareDefect_mem A _ _ _ _ _ _ _ hx hy (hc _) (hc _) (hc _) (hc _) (hc _)
  constructor
  · exact hm (kernelFixedField E H).toSubring (fun a => (kernelFixedField E H).algebraMap_mem a)
      (velu_coordinates_mem E H).1 (velu_coordinates_mem E H).2
  · intro P hP
    exact hm (pointValuation E P).valuationSubring.toSubring
      (fun a => pointValuation_const_le_one E P a)
      (veluX_regular_outside E H P hP) (veluY_regular_outside E H P hP)

/-- [DkMath.Lib] 同じX_H,Y_Hは、半核から作る明示的なVélu型候補の方程式を満たす。
同じ関数体の不変性、核外正則性、Oでの厳密な消滅を全て内部供給する。 -/
theorem halfKernelPolynomialModel_equation (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    ((halfKernelPolynomialModel E H).toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation
      (veluX E H) (veluY E H) := by
  have hr := halfKernelPolynomialDefect_regular E H
  have hz := eq_zero_of_kernel_regular_lt_one E H _ hr.1 hr.2 (halfKernelPolynomialDefect_lt_one E H ho)
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure K) F).injective
  apply (equation_iff_completedSquare _ _ _).mpr
  exact sub_eq_zero.mp hz

/-- [DkMath.Lib] 奇数核では、多項式候補は既存の同じkernelModelに無条件で一致する。 -/
theorem halfKernelPolynomialModel_eq_kernelModel (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) : halfKernelPolynomialModel E H = kernelModel E H :=
  halfKernelPolynomialModel_eq_kernelModel_of_equation E H (halfKernelPolynomialModel_equation E H ho)

/-- [DkMath.Lib] 同じ既存標的のa₂,a₄,a₆を、元の係数と同じ半核のモーメント和で明示する。 -/
theorem kernelModel_coefficients (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H)) :
    let W := E.map (algebraMap K (AlgebraicClosure K))
    let T := ∑ Q ∈ halfKernel E H, momentT W Q.val.xc
    let U := ∑ Q ∈ halfKernel E H, momentW W Q.val.xc Q.val.yc
    (kernelModel E H).a₂ = W.a₂ ∧ (kernelModel E H).a₄ = W.a₄ - 5 * T ∧
      (kernelModel E H).a₆ = W.a₆ - W.b₂ * T - 7 * U := by
  rw [← halfKernelPolynomialModel_eq_kernelModel E H ho]
  exact ⟨rfl, rfl, rfl⟩

/-- [DkMath.Lib] 同じ奇数核と同じ整モデルから、既存kernelModel自体の係数整性を得る。
候補との一致は内部証明済みであり、方程式providerは不要である。 -/
theorem kernelModel_coefficientsIn (H : AddSubgroup (Points E)) [Fintype H] (ho : Odd (Nat.card H))
    (n : ℕ) (hkill : ∀ P : H, n • P.val = 0) (A : ValuationSubring (AlgebraicClosure K))
    (M : WeierstrassCurve A) (hM : M.map A.subtype = E.map (algebraMap K (AlgebraicClosure K)))
    (hn : A.valuation (n : AlgebraicClosure K) = 1) : CoefficientsIn A.toSubring (kernelModel E H) := by
  rw [← halfKernelPolynomialModel_eq_kernelModel E H ho]
  exact halfKernelPolynomialModel_coefficientsIn E H n hkill A M hM hn

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
