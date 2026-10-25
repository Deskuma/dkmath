/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticPoleDegree

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelGeneration"

/-!
# 同じ正規化二関数による固定体生成を閉じる

[DkMath.Lib] Oでの極位数2,3から固定体の相対次数を上下から計算する。
上界は整基底と極空間の成長、下界は付値指数のmod 2,mod 3の合同類である。
既存の有限平行移動群の次数|H|と掛け合わせ、周囲の次数2|H|,3|H|を内部供給する。
前回の条件付き生成定理を、その未供給仮定を残さず適用する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticTorsionRepresentation EllipticFunctionField
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelGeneration :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- [DkMath.Lib] 同じ固定体の、同じX_H,Y_Hに対する相対次数は正確に2,3。
有限性だけを仮定にする包装ではなく、核外正則性とOの極から数値を証明する。 -/
theorem velu_relative_degrees (H : AddSubgroup (Points E)) [Fintype H] :
    ((AlgebraicClosure K)⟮veluX E H⟯).relfinrank (kernelFixedField E H) = 2 ∧
    ((AlgebraicClosure K)⟮veluY E H⟯).relfinrank (kernelFixedField E H) = 3 := by
  have hx := (velu_coordinates_mem E H).1
  have hy := (velu_coordinates_mem E H).2
  constructor
  · apply Nat.le_antisymm
    · exact relfinrank_le_poleOrder E H _ hx (veluX_regular_outside E H) 2 (by decide)
        (veluX_valuation_zero E H)
    · apply le_relfinrank_of_pole_classes E H (veluX E H) (veluY E H) hx hy
        2 3 2 (by decide) (veluX_valuation_zero E H) (veluY_valuation_zero E H)
      intro i j r s he
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
  · apply Nat.le_antisymm
    · exact relfinrank_le_poleOrder E H _ hy (veluY_regular_outside E H) 3 (by decide)
        (veluY_valuation_zero E H)
    · apply le_relfinrank_of_pole_classes E H (veluY E H) (veluX E H) hy hx
        3 2 3 (by decide) (veluY_valuation_zero E H) (veluX_valuation_zero E H)
      intro i j r s he
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega

/-- [DkMath.Lib] 周囲の同じ楕円関数体での正確な次数2|H|,3|H|。
総極位数と同じ数になることを、相対次数と固定体の塔から証明する。 -/
theorem velu_ambient_degrees (H : AddSubgroup (Points E)) [Fintype H] :
    Module.finrank (AlgebraicClosure K)⟮veluX E H⟯
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField = 2 * Nat.card H ∧
    Module.finrank (AlgebraicClosure K)⟮veluY E H⟯
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField = 3 * Nat.card H := by
  have ht := velu_degree_towers E H
  rw [(velu_relative_degrees E H).1, (velu_relative_degrees E H).2] at ht
  exact ⟨ht.1.symm, ht.2.symm⟩

/-- [DkMath.Lib] 同じX_H,Y_Hは同じ有限核の平行移動固定体を生成する。
正確な次数や生成のproviderを外部に要求しない。標的曲線のモデルとは区別する。 -/
theorem veluCoordinateField_eq_fixedField (H : AddSubgroup (Points E)) [Fintype H] :
    veluCoordinateField E H = kernelFixedField E H :=
  veluCoordinateField_eq_fixedField_of_degrees E H
    (velu_ambient_degrees E H).1 (velu_ambient_degrees E H).2

/-- [DkMath.Lib] 二関数それぞれの総極位数は、実際の単純部分体上の関数体次数に等しい。
今回の有限核の正規化関数についての等式であり、任意の曲線の因子次数定理ではない。 -/
theorem velu_total_poles_eq_degrees (H : AddSubgroup (Points E)) [Fintype H] :
    (∑ P : H, -pointOrder E P.val (veluX E H) (veluX_ne_zero E H)) =
      (Module.finrank (AlgebraicClosure K)⟮veluX E H⟯
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField : ℤ) ∧
    (∑ P : H, -pointOrder E P.val (veluY E H) (veluY_ne_zero E H)) =
      (Module.finrank (AlgebraicClosure K)⟮veluY E H⟯
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField : ℤ) := by
  have ht := velu_total_pole_orders E H
  rw [(velu_ambient_degrees E H).1, (velu_ambient_degrees E H).2]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht

/-- [DkMath.Lib] 同じY_Hのk(X_H)上の最小多項式は正確に二次である。
生成体と固定体の一致を使い、無用な有限拡大の係数を導入しない。 -/
theorem natDegree_minpoly_veluY (H : AddSubgroup (Points E)) [Fintype H] :
    (minpoly (AlgebraicClosure K)⟮veluX E H⟯ (veluY E H)).natDegree = 2 := by
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let A := k⟮veluX E H⟯
  let B := A⟮veluY E H⟯
  let := (finiteDimensional_over_velu E H).1
  have hy : IsIntegral A (veluY E H) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hB : B.restrictScalars k = kernelFixedField E H := by
    rw [show B.restrictScalars k = veluCoordinateField E H from
      adjoin_simple_adjoin_simple k (veluX E H) (veluY E H)]
    exact veluCoordinateField_eq_fixedField E H
  have hBdeg : Module.finrank B F = Nat.card H := by
    change Module.finrank (B.restrictScalars k) F = _
    rw [hB]
    exact finrank_kernelFixedField E H
  have ht := Module.finrank_mul_finrank A B F
  rw [adjoin.finrank hy, hBdeg, (velu_ambient_degrees E H).1] at ht
  exact mul_right_cancel₀ (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩) ht

/-- [DkMath.Lib] 同じ二関数の実際のモニック二次関係を公開する。
係数はk(X_H)にあり、まだWeierstrass形やその係数のkへの降下を結論しない。 -/
theorem exists_velu_quadratic_relation (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ q : ((AlgebraicClosure K)⟮veluX E H⟯)[X],
      q.Monic ∧ q.natDegree = 2 ∧ aeval (veluY E H) q = 0 := by
  let := (finiteDimensional_over_velu E H).1
  have hy : IsIntegral (AlgebraicClosure K)⟮veluX E H⟯ (veluY E H) :=
    (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  exact ⟨minpoly _ _, minpoly.monic hy, natDegree_minpoly_veluY E H, minpoly.aeval _ _⟩

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
