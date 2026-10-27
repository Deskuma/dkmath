/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticPointEvaluation
import DkMath.Lib.NumberTheory.WeierstrassTwoTorsionSeparation
import DkMath.Lib.NumberTheory.EllipticFiniteKernelModelDescent

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization"

/-!
# 同じ商モデルの座標を実点へ特殊化する

[DkMath.Lib] 核Hの外ではX_H,Y_Hが正則なので、一意な有限値を持つ。
同じ二値は標的モデルの方程式を満たし、Hの平行移動で変化しない。
標的楕円性が供給された場合は、HをOへ送る実際の全点写像も構成できる。
この最後の仮定は型に残す。点写像の加法性・isogenyはここでは結論しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open scoped BigOperators
variable {K : Type*} [Field K] [NeZero (2 : K)] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] Hの外の実点における、同じX_Hの一意な有限値。 -/
noncomputable def kernelXAt (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) : AlgebraicClosure K :=
  value E P (veluX E H) (veluX_regular_outside E H P hP)

/-- [DkMath.Lib] Hの外の同じ実点における、同じY_Hの一意な有限値。 -/
noncomputable def kernelYAt (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) : AlgebraicClosure K :=
  value E P (veluY E H) (veluY_regular_outside E H P hP)

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 二つの特殊化座標は、元の関数に同じ点で合同である。 -/
theorem kernelAt_congr (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    (pointValuation E P).Cong (veluX E H) (algebraMap _ _ (kernelXAt E H P hP)) ∧
    (pointValuation E P).Cong (veluY E H) (algebraMap _ _ (kernelYAt E H P hP)) :=
  ⟨value_spec E P _ _, value_spec E P _ _⟩

/-- [DkMath.Lib] 同じ実点の二つの有限値は、同じ標的モデルの方程式を満たす。 -/
theorem kernelAt_equation (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    (kernelModel E H).toAffine.Equation (kernelXAt E H P hP) (kernelYAt E H P hP) :=
  equation_value E P (kernelModel E H) _ _
    (veluX_regular_outside E H P hP) (veluY_regular_outside E H P hP) (kernelModel_equation E H)

omit [NeZero (2 : K)] [E.IsElliptic] in
/-- [DkMath.Lib] Hの元による移動は、Hの外という条件を保つ。 -/
theorem add_not_mem_kernel (H : AddSubgroup (Points E))
    (P : Points E) (hP : P ∉ H) (Q : H) : P + Q.val ∉ H := by
  intro hm
  exact hP (by simpa only [add_sub_cancel_right] using H.sub_mem hm Q.property)

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 同じ核の移動で、特殊化したx値も不変である。 -/
theorem kernelXAt_translation (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) :
    kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) = kernelXAt E H P hP := by
  have h := value_translation E P Q.val (veluX E H)
    (veluX_regular_outside E H _ (add_not_mem_kernel E H P hP Q))
  simpa only [veluX_translation, kernelXAt] using h.symm

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 同じ核の移動で、特殊化したy値も不変である。 -/
theorem kernelYAt_translation (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) :
    kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) = kernelYAt E H P hP := by
  have h := value_translation E P Q.val (veluY E H)
    (veluY_regular_outside E H _ (add_not_mem_kernel E H P hP Q))
  simpa only [veluY_translation, kernelYAt] using h.symm

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 点の座標へ合同な関数の正規化和を、同じ有限点の座標和へ特殊化する。
移動先P+Qは全て有限点なので、Oの便宜的座標を有限評価へ流用しない。 -/
theorem normalized_trace_congr (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (c : Points E → AlgebraicClosure K)
    (hf : ∀ R : Points E, R ≠ 0 → (pointValuation E R).Cong f (algebraMap _ _ (c R)))
    (P : Points E) (hP : P ∉ H) :
    (pointValuation E P).Cong
      (kernelTrace E H f - algebraMap _ _ (∑ Q : H, c Q.val))
      (algebraMap _ _ ((∑ Q : H, c (P + Q.val)) - ∑ Q : H, c Q.val)) := by
  classical
  have hi (Q : H) : (pointValuation E P).Cong
      (transEquiv E (AlgebraicClosure K) Q.val f) (algebraMap _ _ (c (P + Q.val))) := by
    have hR : P + Q.val ≠ 0 := fun hz => hP (by
      rw [eq_neg_of_add_eq_zero_left hz]; exact H.neg_mem Q.property)
    have h := hf (P + Q.val) hR
    have ht := pointValuation_transEquiv E P Q.val (f - algebraMap _ _ (c (P + Q.val)))
    rw [map_sub, AlgEquiv.commutes] at ht
    exact ht.trans_lt h
  have hs : ∀ t : Finset H, (pointValuation E P).Cong
      (∑ Q ∈ t, transEquiv E (AlgebraicClosure K) Q.val f)
      (∑ Q ∈ t, algebraMap _ _ (c (P + Q.val))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact Valuation.Cong.rfl
    | @insert Q t hQ ih =>
      rw [Finset.sum_insert hQ, Finset.sum_insert hQ]
      exact (hi Q).add ih
  have h := (hs Finset.univ).sub (Valuation.Cong.rfl
    (v := pointValuation E P) (a := algebraMap _ _ (∑ Q : H, c Q.val)))
  simpa only [kernelTrace, map_sub, map_sum] using h

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 特殊化x値は、実点の正規化座標和そのものである。 -/
theorem kernelXAt_eq_sum (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    kernelXAt E H P hP = (∑ Q : H, (P + Q.val).xc) - ∑ Q : H, Q.val.xc := by
  apply value_eq
  refine normalized_trace_congr E H _ _ ?_ P hP
  intro R hR
  have h := value_spec E R (genericX E (AlgebraicClosure K)) (pointValuation_genericX_le_one E R hR)
  rwa [value_genericX E R hR] at h

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 特殊化y値も、同じ実点の正規化座標和で計算できる。 -/
theorem kernelYAt_eq_sum (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    kernelYAt E H P hP = (∑ Q : H, (P + Q.val).yc) - ∑ Q : H, Q.val.yc := by
  apply value_eq
  refine normalized_trace_congr E H _ _ ?_ P hP
  intro R hR
  have h := value_spec E R (genericY E (AlgebraicClosure K)) (pointValuation_genericY_le_one E R hR)
  rwa [value_genericY E R hR] at h

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] Hの外の点を反転しても、同じ特殊化x値となる。 -/
theorem kernelXAt_neg (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    kernelXAt E H (-P) (fun hm => hP (H.neg_mem_iff.mp hm)) = kernelXAt E H P hP := by
  rw [kernelXAt_eq_sum, kernelXAt_eq_sum]
  congr 1
  calc (∑ Q : H, (-P + Q.val).xc) = ∑ Q : H, (-P + -Q.val).xc :=
      (sum_kernel_neg E H (fun R => (-P + R).xc)).symm
    _ = ∑ Q : H, (P + Q.val).xc := by
      apply Finset.sum_congr rfl
      intro Q _
      have he : -P + -Q.val = -(P + Q.val) := by abel
      rw [he]
      cases (P + Q.val : Points E) <;> rfl

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 特殊化y値の反転公式。Oの補正を含む同じa₃が残る。 -/
theorem kernelYAt_neg (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) :
    kernelYAt E H (-P) (fun hm => hP (H.neg_mem_iff.mp hm)) = -kernelYAt E H P hP -
      (E⁄(AlgebraicClosure K)).a₁ * kernelXAt E H P hP - (E⁄(AlgebraicClosure K)).a₃ := by
  have hi (Q : H) : (-P + -Q.val).yc = -(P + Q.val).yc -
      (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc - (E⁄(AlgebraicClosure K)).a₃ := by
    have hR : P + Q.val ≠ 0 := fun hz => hP (by
      rw [eq_neg_of_add_eq_zero_left hz]; exact H.neg_mem Q.property)
    have he : -P + -Q.val = -(P + Q.val) := by abel
    rw [he]
    generalize hpoint : (P + Q.val : Points E) = R at *
    cases R with
    | zero => exact (hR rfl).elim
    | some x y h => rfl
  have hs : (∑ Q : H, (-P + Q.val).yc) = -(∑ Q : H, (P + Q.val).yc) -
      (E⁄(AlgebraicClosure K)).a₁ * (∑ Q : H, (P + Q.val).xc) -
      (Fintype.card H : AlgebraicClosure K) * (E⁄(AlgebraicClosure K)).a₃ := by
    rw [← sum_kernel_neg E H (fun R => (-P + R).yc)]
    simp only [hi, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [kernelYAt_eq_sum, kernelYAt_eq_sum, kernelXAt_eq_sum, hs]
  linear_combination -(kernel_coordinate_correction E H)

/-- [DkMath.Lib] 元の反転固定点は、特殊化後の2捩れ三次式の根を与える。
標的楕円性は使わず、三根の分離だけを残す。 -/
theorem kernelAt_twoTorsion_root (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    (kernelModel E H).twoTorsionPolynomial.toPoly.eval (kernelXAt E H P hP) = 0 := by
  apply WeierstrassTwoTorsionSeparation.root_of_equation_of_neg_fixed
    (kernelModel E H) (kernelAt_equation E H P hP)
  have hy := kernelYAt_neg E H P hP
  simpa only [hneg, kernelModel_a₁, kernelModel_a₃] using hy

/-- [DkMath.Lib] 反転固定点のH軌道では、特殊化x値が不変であるため、
軌道上の全ての点が同じ標的2捩れ根へ着地する。

これは根の「存在」を軌道全体へ輸送する補題であり、根の多重度や
ファイバー全体の列挙までは主張しない。後者は別途、次数比較と
`fiberFactor` の可除性層から供給する。 -/
theorem kernelAt_twoTorsion_root_translation
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) :
    (kernelModel E H).twoTorsionPolynomial.toPoly.eval
      (kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q)) = 0 := by
  rw [kernelXAt_translation E H P hP Q]
  exact kernelAt_twoTorsion_root E H P hP hneg

/-- [DkMath.Lib] 元の三つの反転固定点の特殊化x値が分離すれば、同じ標的のΔは非零。
根への着地は内部供給済みで、残る入力は実際の三値の分離である。 -/
theorem kernelModel_discriminant_of_twoTorsion_separation
    (H : AddSubgroup (Points E)) [Fintype H] (P : Fin 3 → Points E) (hP : ∀ i, P i ∉ H)
    (hneg : ∀ i, -P i = P i)
    (hx : Function.Injective (fun i => kernelXAt E H (P i) (hP i))) :
    (kernelModel E H).Δ ≠ 0 :=
  WeierstrassTwoTorsionSeparation.discriminant_ne_zero_of_three_roots (kernelModel E H)
    (by simpa only [map_ofNat, map_zero] using
      (algebraMap K (AlgebraicClosure K)).injective.ne (NeZero.ne (2 : K))) _ _ _ (kernelAt_twoTorsion_root E H _ (hP 0) (hneg 0))
    (kernelAt_twoTorsion_root E H _ (hP 1) (hneg 1))
    (kernelAt_twoTorsion_root E H _ (hP 2) (hneg 2))
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hx h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hx h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hx h))


/-- [DkMath.Lib] 標的楕円性があれば、特殊化した同じ有限座標点は非特異となる。
このインスタンスは今回の構成から自動供給したものではない。 -/
theorem kernelAt_nonsingular (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] (P : Points E) (hP : P ∉ H) :
    (kernelModel E H).toAffine.Nonsingular (kernelXAt E H P hP) (kernelYAt E H P hP) :=
  equation_iff_nonsingular.mp (kernelAt_equation E H P hP)

/-- [DkMath.Lib] 標的楕円性を明示入力とする全点写像。H上はO、Hの外は同じ有限値を使う。
型は関数であり、加法群準同型ではない。 -/
noncomputable def kernelPointMap (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] : Points E → (kernelModel E H).toAffine.Point := by
  classical
  exact fun P => if hP : P ∈ H then 0 else .some _ _ (kernelAt_nonsingular E H P hP)

/-- [DkMath.Lib] 同じ全点写像は、核Hの元を実際にOへ送る。 -/
theorem kernelPointMap_of_mem (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] (P : Points E) (hP : P ∈ H) : kernelPointMap E H P = 0 := by
  simp only [kernelPointMap, dite_eq_left hP]

/-- [DkMath.Lib] Hの外では、全点写像は同じ二つの有限値を持つ点である。 -/
theorem kernelPointMap_of_not_mem (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] (P : Points E) (hP : P ∉ H) :
    kernelPointMap E H P = .some _ _ (kernelAt_nonsingular E H P hP) := by
  simp only [kernelPointMap, dite_eq_right hP]

/-- [DkMath.Lib] 条件付き全点写像の零ファイバーは正確に同じH。
加法性未証明なので、AddMonoidHom.kerという表記へはまだ置き換えない。 -/
theorem kernelPointMap_eq_zero_iff (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] (P : Points E) : kernelPointMap E H P = 0 ↔ P ∈ H := by
  by_cases hP : P ∈ H
  · simp only [kernelPointMap_of_mem E H P hP, hP]
  · rw [kernelPointMap_of_not_mem E H P hP]
    exact iff_of_false (Point.some_ne_zero _) hP

/-- [DkMath.Lib] 条件付き全点写像は、同じ核の各平行移動軌道で一定である。 -/
theorem kernelPointMap_translation (H : AddSubgroup (Points E)) [Fintype H]
    [(kernelModel E H).IsElliptic] (P : Points E) (Q : H) :
    kernelPointMap E H (P + Q.val) = kernelPointMap E H P := by
  by_cases hP : P ∈ H
  · rw [kernelPointMap_of_mem E H _ (H.add_mem hP Q.property), kernelPointMap_of_mem E H _ hP]
  · rw [kernelPointMap_of_not_mem E H _ (add_not_mem_kernel E H P hP Q),
      kernelPointMap_of_not_mem E H _ hP]
    congr 1
    · exact kernelXAt_translation E H P hP Q
    · exact kernelYAt_translation E H P hP Q

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
