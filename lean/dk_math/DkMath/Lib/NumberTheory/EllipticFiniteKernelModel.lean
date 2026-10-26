/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelReflection
import DkMath.Lib.NumberTheory.EllipticFiniteKernelPolynomial
import DkMath.Lib.Algebra.ValuationCubicModel

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelModel"

/-!
# 同じ二関数が満たすWeierstrass方程式

[DkMath.Lib] 関数体の反転・二次性・正則性から、同じX_H,Y_Hを満たす三次方程式を構成する。
明るい側は実際の方程式とその一意な係数、暗い側は判別式の非零性・全点写像の構成である。
方程式があることを楕円曲線性やisogenyの存在へ読み替えない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelModel :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 正規化和と元の関数との差はOで正則。補正定数は任意でよい。 -/
theorem normalized_trace_correction_regular (H : AddSubgroup (Points E)) [Fintype H]
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (c : AlgebraicClosure K)
    (hreg : ∀ P : Points E, P ≠ 0 → pointValuation E P f ≤ 1) :
    pointValuation E (0 : Points E)
      (kernelTrace E H f - algebraMap _ _ c - f) ≤ 1 := by
  classical
  let g : H → (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
    fun Q => transEquiv E (AlgebraicClosure K) Q.val f
  have h0 : g 0 = f := by
    change transEquiv E (AlgebraicClosure K) (0 : (E⁄(AlgebraicClosure K)).Point) f = f
    rw [transEquiv_zero]; rfl
  have hs : kernelTrace E H f - f = ∑ Q ∈ Finset.univ.erase (0 : H), g Q := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset H) g (Finset.mem_univ (0 : H))
    rw [h0] at hsum
    change (∑ Q : H, g Q) - f = _
    linear_combination -hsum
  have he : kernelTrace E H f - algebraMap _ _ c - f =
      (∑ Q ∈ Finset.univ.erase (0 : H), g Q) - algebraMap _ _ c := by rw [← hs]; ring
  rw [he]
  apply ((pointValuation E (0 : Points E)).map_sub _ _).trans (max_le ?_ ?_)
  · apply Valuation.map_sum_le
    intro Q hQ
    have hQ0 : Q.val ≠ 0 := fun h => (Finset.mem_erase.mp hQ).1 (Subtype.ext h)
    have hv : pointValuation E (0 : Points E) (g Q) = pointValuation E Q.val f := by
      have ht : pointValuation E (0 : Points E) (g Q) =
          pointValuation E ((0 : Points E) + Q.val) f := pointValuation_transEquiv E 0 Q.val f
      simpa only [zero_add] using ht
    rw [hv]
    exact hreg Q.val hQ0
  · exact pointValuation_const_le_one E (0 : Points E) c

/-- [DkMath.Lib] 同じ正規化座標は、Oで元のx,yに正則な補正を加えたものである。 -/
theorem velu_corrections_regular (H : AddSubgroup (Points E)) [Fintype H] :
    pointValuation E (0 : Points E) (veluX E H - genericX E (AlgebraicClosure K)) ≤ 1 ∧
    pointValuation E (0 : Points E) (veluY E H - genericY E (AlgebraicClosure K)) ≤ 1 :=
  ⟨normalized_trace_correction_regular E H _ _ (pointValuation_genericX_le_one E),
    normalized_trace_correction_regular E H _ _ (pointValuation_genericY_le_one E)⟩

/-- [DkMath.Lib] 同じ曲線の基礎体係数は、関数体の全点付値で正則である。 -/
theorem pointValuation_base_const_le_one (P : Points E) (c : K) :
    pointValuation E P (algebraMap K (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K)]
  exact pointValuation_const_le_one E P _

/-- [DkMath.Lib] 同じ二関数の三次最高項を除いた実際の残差。 -/
noncomputable def veluCubicResidual (H : AddSubgroup (Points E)) [Fintype H] :
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  veluY E H ^ 2 + (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ * veluX E H * veluY E H +
    (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ * veluY E H - veluX E H ^ 3

/-- [DkMath.Lib] 残差は同じ核の固定体に属する。 -/
theorem veluCubicResidual_mem_fixedField (H : AddSubgroup (Points E)) [Fintype H] :
    veluCubicResidual E H ∈ kernelFixedField E H := by
  let N := kernelFixedField E H
  have hx := (velu_coordinates_mem E H).1
  have hy := (velu_coordinates_mem E H).2
  have hc (c : K) : algebraMap K (E.toAffine⁄(AlgebraicClosure K)).FunctionField c ∈ N := by
    rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K)]
    exact N.algebraMap_mem _
  exact N.sub_mem (N.add_mem (N.add_mem (N.pow_mem hy 2)
    (N.mul_mem (N.mul_mem (hc E.a₁) hx) hy)) (N.mul_mem (hc E.a₃) hy)) (N.pow_mem hx 3)

/-- [DkMath.Lib] 残差もHの外で正則。係数と二関数の正則性を部分環で保持する。 -/
theorem veluCubicResidual_regular_outside (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) : pointValuation E P (veluCubicResidual E H) ≤ 1 := by
  let V := (pointValuation E P).valuationSubring
  have hx : veluX E H ∈ V := veluX_regular_outside E H P hP
  have hy : veluY E H ∈ V := veluY_regular_outside E H P hP
  have hc (c : K) : algebraMap K (E.toAffine⁄(AlgebraicClosure K)).FunctionField c ∈ V :=
    pointValuation_base_const_le_one E P c
  exact V.toSubring.sub_mem (V.toSubring.add_mem (V.toSubring.add_mem (V.toSubring.pow_mem hy 2)
    (V.toSubring.mul_mem (V.toSubring.mul_mem (hc E.a₁) hx) hy))
      (V.toSubring.mul_mem (hc E.a₃) hy)) (V.toSubring.pow_mem hx 3)

/-- [DkMath.Lib] 正則な補正と元の方程式から、残差のOでの極は高々4となる。 -/
theorem veluCubicResidual_pole_bound (H : AddSubgroup (Points E)) [Fintype H] :
    pointValuation E (0 : Points E) (veluCubicResidual E H) ≤ exp (4 : ℤ) := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  have heq := (equation_iff _ _).mp (generic_equation E (AlgebraicClosure K))
  apply ValuationCubicModel.residual_le (pointValuation E (0 : Points E))
    (genericX E (AlgebraicClosure K)) (genericY E (AlgebraicClosure K))
    (veluX E H) (veluY E H) (E⁄F).a₁ (E⁄F).a₂ (E⁄F).a₃ (E⁄F).a₄ (E⁄F).a₆
  · exact heq
  · exact pointValuation_zero_genericX E
  · exact pointValuation_zero_genericY E
  · exact veluX_valuation_zero E H
  · exact veluY_valuation_zero E H
  · exact (velu_corrections_regular E H).1
  · exact (velu_corrections_regular E H).2
  all_goals exact pointValuation_base_const_le_one E (0 : Points E) _

/-- [DkMath.Lib] 元の基礎体係数は反転で固定される。二段の係数埋め込みを揃える。 -/
theorem negEquiv_base_const (c : K) :
    negEquiv E (AlgebraicClosure K) (algebraMap K (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) =
      algebraMap K (E.toAffine⁄(AlgebraicClosure K)).FunctionField c := by
  rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K), AlgEquiv.commutes]

/-- [DkMath.Lib] 残差は反転でも固定される。正規化yの反転公式を二次式に代入する。 -/
theorem negEquiv_veluCubicResidual (H : AddSubgroup (Points E)) [Fintype H] :
    negEquiv E (AlgebraicClosure K) (veluCubicResidual E H) = veluCubicResidual E H := by
  have h₁ : negEquiv E (AlgebraicClosure K)
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ =
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ := negEquiv_base_const E E.a₁
  have h₃ : negEquiv E (AlgebraicClosure K)
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ =
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ := negEquiv_base_const E E.a₃
  simp only [veluCubicResidual, map_sub, map_add, map_mul, map_pow,
    negEquiv_veluX, negEquiv_veluY, h₁, h₃]
  ring

/-- [DkMath.Lib] 極位数3はmod 2で係数体の値と合わないので、同じY_Hはk(X_H)に入らない。 -/
theorem veluY_not_mem_simpleX (H : AddSubgroup (Points E)) [Fintype H] :
    veluY E H ∉ (AlgebraicClosure K)⟮veluX E H⟯ := by
  intro hmem
  obtain ⟨m, hm⟩ := ValuationPoleSpace.value_adjoin_simple (pointValuation E (0 : Points E))
    (fun c hc => pointValuation_const_eq_one E (0 : Points E) hc)
    (veluX E H) 2 (by decide) (veluX_valuation_zero E H)
    ⟨veluY E H, hmem⟩ (fun he => veluY_ne_zero E H (congrArg Subtype.val he))
  change pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point) (veluY E H) = exp ((2 : ℤ) * m) at hm
  rw [veluY_valuation_zero, exp_inj] at hm
  omega

variable [NeZero (2 : K)]

/-- [DkMath.Lib] 2が非零の体では、反転は同じY_Hを実際に動かす。
固定ならY_Hを2で割った一次式で表せてしまい、上の非所属に矛盾する。 -/
theorem negEquiv_veluY_ne (H : AddSubgroup (Points E)) [Fintype H] :
    negEquiv E (AlgebraicClosure K) (veluY E H) ≠ veluY E H := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let : NeZero (2 : F) := ⟨by
    simpa only [map_ofNat, map_zero] using (algebraMap K F).injective.ne (NeZero.ne (2 : K))⟩
  let A := (AlgebraicClosure K)⟮veluX E H⟯
  have hc (c : K) : algebraMap K F c ∈ A := by
    rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K)]
    exact A.algebraMap_mem _
  intro he
  have h := negEquiv_veluY E H
  rw [he] at h
  have heq : veluY E H = -((E⁄F).a₁ * veluX E H + (E⁄F).a₃) / 2 := by
    apply (eq_div_iff (two_ne_zero : (2 : F) ≠ 0)).mpr
    linear_combination h
  apply veluY_not_mem_simpleX E H
  rw [heq]
  exact A.div_mem (A.neg_mem (A.add_mem
    (A.mul_mem (hc E.a₁) (mem_adjoin_simple_self _ _)) (hc E.a₃))) (A.natCast_mem 2)

/-- [DkMath.Lib] 同じ残差の二次反射不変性により、残差はk(X_H)へ戻る。 -/
theorem veluCubicResidual_mem_simpleX (H : AddSubgroup (Points E)) [Fintype H] :
    veluCubicResidual E H ∈ (AlgebraicClosure K)⟮veluX E H⟯ := by
  apply QuadraticFixedField.mem_of_fixed
    ((AlgebraicClosure K)⟮veluX E H⟯) (kernelFixedField E H)
    (adjoin_simple_le_iff.mpr (velu_coordinates_mem E H).1)
    (velu_relative_degrees E H).1 (negEquiv E (AlgebraicClosure K)) ?_
    (veluY E H) (velu_coordinates_mem E H).2 (negEquiv_veluY_ne E H)
    (veluCubicResidual_mem_fixedField E H) (negEquiv_veluCubicResidual E H)
  intro a ha
  obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff (AlgebraicClosure K) a).mp ha
  rw [he, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, negEquiv_veluX]

/-- [DkMath.Lib] 同じ残差はX_Hの二次以下の多項式である。
分母除去と極上界4を実際に接続し、Weierstrass方程式の係数を取り出せる形にする。 -/
theorem exists_velu_residual_polynomial (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ p : (AlgebraicClosure K)[X], p.natDegree ≤ 2 ∧
      veluCubicResidual E H = aeval (veluX E H) p := by
  obtain ⟨p, hp⟩ := exists_polynomial_of_kernel_regular E H _
    (veluCubicResidual_mem_simpleX E H) (veluCubicResidual_regular_outside E H)
  refine ⟨p, ?_, hp⟩
  have hd := polynomial_natDegree_le_of_pole_bound E H p 4
    (hp ▸ veluCubicResidual_pole_bound E H)
  omega

/-- [DkMath.Lib] 同じX_H,Y_HのWeierstrass形の三次関係を、係数を持つ実際の式として構成する。
a₁,a₃は元の曲線と同じである。判別式の非零性はこの定理の結論に含めない。 -/
theorem exists_velu_weierstrass_equation (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ a₂ a₄ a₆ : AlgebraicClosure K,
      veluY E H ^ 2 + (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₁ * veluX E H * veluY E H +
        (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).a₃ * veluY E H =
      veluX E H ^ 3 + algebraMap _ _ a₂ * veluX E H ^ 2 +
        algebraMap _ _ a₄ * veluX E H + algebraMap _ _ a₆ := by
  obtain ⟨p, hpdeg, hp⟩ := exists_velu_residual_polynomial E H
  have hform := congrArg (aeval (veluX E H)) (p.as_sum_range_C_mul_X_pow' (n := 3) (by omega))
  simp only [map_add, map_mul, aeval_C, map_pow, aeval_X,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one] at hform
  refine ⟨p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
  unfold veluCubicResidual at hp
  linear_combination hp + hform

/-- [DkMath.Lib] 同じ二関数を座標とするWeierstrassモデルが実在する。
ここではa₁,a₃の一致と方程式を構成し、Δ≠0を証明済みとはしない。 -/
theorem exists_kernelModel (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ W : WeierstrassCurve (AlgebraicClosure K),
      W.a₁ = (E⁄(AlgebraicClosure K)).a₁ ∧ W.a₃ = (E⁄(AlgebraicClosure K)).a₃ ∧
      (W.toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation (veluX E H) (veluY E H) := by
  obtain ⟨a₂, a₄, a₆, he⟩ := exists_velu_weierstrass_equation E H
  refine ⟨⟨(E⁄(AlgebraicClosure K)).a₁, a₂, (E⁄(AlgebraicClosure K)).a₃, a₄, a₆⟩, rfl, rfl, ?_⟩
  rw [equation_iff]
  change veluY E H ^ 2 + algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₁) *
    veluX E H * veluY E H + algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₃) * veluY E H = _
  rw [← IsScalarTower.algebraMap_apply K (AlgebraicClosure K),
    ← IsScalarTower.algebraMap_apply K (AlgebraicClosure K)]
  exact he

/-- [DkMath.Lib] 構成した同じ三次モデル。型はWeierstrassCurveであり、IsEllipticは仮定に隠さない。 -/
noncomputable def kernelModel (H : AddSubgroup (Points E)) [Fintype H] :
    WeierstrassCurve (AlgebraicClosure K) := Classical.choose (exists_kernelModel E H)

/-- [DkMath.Lib] 標的モデルのa₁は元の曲線のa₁と一致する。 -/
theorem kernelModel_a₁ (H : AddSubgroup (Points E)) [Fintype H] :
    (kernelModel E H).a₁ = (E⁄(AlgebraicClosure K)).a₁ :=
  (Classical.choose_spec (exists_kernelModel E H)).1

/-- [DkMath.Lib] 標的モデルのa₃は元の曲線のa₃と一致する。 -/
theorem kernelModel_a₃ (H : AddSubgroup (Points E)) [Fintype H] :
    (kernelModel E H).a₃ = (E⁄(AlgebraicClosure K)).a₃ :=
  (Classical.choose_spec (exists_kernelModel E H)).2.1

/-- [DkMath.Lib] 同じ構成済みX_H,Y_Hは、選んだ同じモデルの方程式を実際に満たす。 -/
theorem kernelModel_equation (H : AddSubgroup (Points E)) [Fintype H] :
    ((kernelModel E H).toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Equation
      (veluX E H) (veluY E H) :=
  (Classical.choose_spec (exists_kernelModel E H)).2.2

/-- [DkMath.Lib] 同じモデルの関数体値の一般座標点は非特異である。
一般点の非特異性は、モデルの全点の非特異性やΔ≠0より弱いことに注意する。 -/
theorem kernelModel_generic_nonsingular (H : AddSubgroup (Points E)) [Fintype H] :
    ((kernelModel E H).toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Nonsingular
      (veluX E H) (veluY E H) := by
  rw [nonsingular_iff]
  refine ⟨kernelModel_equation E H, Or.inr ?_⟩
  intro he
  apply negEquiv_veluY_ne E H
  rw [negEquiv_veluY]
  change veluY E H = -veluY E H -
    algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₁ * veluX E H -
      algebraMap (AlgebraicClosure K) _ (kernelModel E H).a₃ at he
  rw [kernelModel_a₁, kernelModel_a₃] at he
  change veluY E H = -veluY E H -
    algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₁) * veluX E H -
      algebraMap (AlgebraicClosure K) _ (algebraMap K _ E.a₃) at he
  rw [← IsScalarTower.algebraMap_apply K (AlgebraicClosure K),
    ← IsScalarTower.algebraMap_apply K (AlgebraicClosure K)] at he
  exact he.symm

/-- [DkMath.Lib] 同じモデル上の実際の関数体値点。全ての実点の写像を定義したものではない。 -/
noncomputable def kernelModelGenericPoint (H : AddSubgroup (Points E)) [Fintype H] :
    ((kernelModel E H).toAffine⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).Point :=
  .some (veluX E H) (veluY E H) (kernelModel_generic_nonsingular E H)

/-- [DkMath.Lib] 構成した関数体値点はOではない。 -/
theorem kernelModelGenericPoint_ne_zero (H : AddSubgroup (Points E)) [Fintype H] :
    kernelModelGenericPoint E H ≠ 0 := Point.some_ne_zero _

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
