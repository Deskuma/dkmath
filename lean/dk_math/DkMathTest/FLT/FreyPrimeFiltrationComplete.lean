/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeFiltration
import DkMathTest.FLT.FreyPrimeFiltration

#print "file: DkMathTest.FLT.FreyPrimeFiltrationComplete"

/-!
# NOTE-031-004 第2部: 実際の有限還元と指数37での全ケース接続

節点モデルy²=x³+x²上のP=(3,6)を5上で還元する。還元点は有限かつ滑らかなので零にならない。
零成分の5-torsionは還元核へ入るという定理から、このPは5-torsionではないと分かる。
これは位数を剰余へ運ぶ新しい接続を実際の座標で検証する例である。
Source37の例は同じSourceを入力とするAPI特殊化であり、整数反例の存在は主張しない。
-/
namespace FreyPrimeFiltrationCompleteTest
open WeierstrassCurve Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticGoodReductionSeparation EllipticSmoothReduction
open ValuationInertia DkMath.Lib.RepresentationTheory LocalFixedCofixed
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 一般ファイバーも剰余も同じ係数で表す節点モデル。 -/
noncomputable def nodeModel (A : ValuationSubring (AlgebraicClosure ℚ)) : WeierstrassCurve A := ⟨0, 1, 0, 0, 0⟩

/-- P=(3,6)は一般ファイバーで滑らかな有限点である。 -/
theorem node_point_nonsingular (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((nodeModel A).map A.subtype).toAffine.Nonsingular 3 6 := by
  norm_num [nodeModel, nonsingular_iff, equation_iff, negY]

/-- 5上の全付値環で、Pの還元は有限滑らかな点である。 -/
theorem node_point_reduction_nonsingular (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 5) :
    ((nodeModel A).map (residue A)).toAffine.Nonsingular 3 6 := by
  have : CharP (ResidueField A) 5 := ValuationPrimeSupport.charP_residueField A (by decide) hA
  rw [nonsingular_iff]
  constructor
  · norm_num [nodeModel, equation_iff]
  · right
    simp only [nodeModel, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_zero,
      zero_mul, sub_zero]
    intro he
    have h12 : (12 : ResidueField A) = 0 := by linear_combination he
    have hb := (CharP.cast_eq_zero_iff (ResidueField A) 5 12).mp h12
    norm_num at hb

/-- 実際の座標還元は無限遠点と異なる。全域関数の特異点分岐へ落ちていない。 -/
theorem node_point_reduction_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 5) :
    reducePointSmooth (nodeModel A) (.some 3 6 (node_point_nonsingular A)) ≠ 0 := by
  have hx : (3 : AlgebraicClosure ℚ) ∈ A := intCast_mem A 3
  have hy : (6 : AlgebraicClosure ℚ) ∈ A := intCast_mem A 6
  have hns : ((nodeModel A).map (residue A)).toAffine.Nonsingular
      (residue A ⟨3, hx⟩) (residue A ⟨6, hy⟩) := by
    simpa only [show (⟨3, hx⟩ : A) = 3 from rfl, show (⟨6, hy⟩ : A) = 6 from rfl,
      map_ofNat] using node_point_reduction_nonsingular A hA
  rw [reducePointSmooth_some_of_mem (nodeModel A) _ hx hns]
  exact Point.some_ne_zero hns

/-- 零成分上の倍算を還元へ運ぶ接続と節点p-torsion排除を合わせる具体例。 -/
theorem node_point_not_five_torsion (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 5) :
    5 • (Point.some 3 6 (node_point_nonsingular A)) ≠ 0 := by
  classical
  have : CharP (ResidueField A) 5 := ValuationPrimeSupport.charP_residueField A (by decide) hA
  intro ht
  have hP : HasSmoothReduction (nodeModel A) (.some 3 6 (node_point_nonsingular A)) := by
    rw [hasSmoothReduction_some_iff]
    intro hx hy
    simpa only [show (⟨3, hx⟩ : A) = 3 from rfl, show (⟨6, hy⟩ : A) = 6 from rfl,
      map_ofNat] using node_point_reduction_nonsingular A hA
  have hk := EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion (nodeModel A) 0 0
    (by norm_num [nodeModel, equation_iff])
    (by norm_num [nodeModel, nonsingular_iff, equation_iff, negY])
    (by
      have h4 : (4 : ResidueField A) ≠ 0 := by
        intro he
        have hb := (CharP.cast_eq_zero_iff (ResidueField A) 5 4).mp he
        norm_num at hb
      simpa [nodeModel, WeierstrassCurve.b₂] using h4) hP ht
  have hpole := (EllipticReductionKernel.some_mem_iff A (nodeModel A) _).mp hk
  exact hpole (intCast_mem A 3)

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 指数37の悪還元で、追加の零成分providerなしに同じ還元核が慣性変化量を吸収する。 -/
theorem source37_bad_absorbs (S : DkMath.FLT.Frey.Source 37)
    (hbad : (37 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 37) :
    CofixedOn S.residualRepresentation (S.residualReductionKernel A) (inertiaSubgroupIn A ℚ) := by
  exact S.residualReductionKernel_absorbs_at_bad_prime (by norm_num) hbad A hA

/-- 指数37でabcの可除性を入力に要求せず、全ての場所で同じ側の二択を得る。 -/
theorem source37_common_side (S : DkMath.FLT.Frey.Source 37)
    (N : Submodule (ZMod 37) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 37 →
      FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 37 →
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) := by
  exact S.residual_common_side_at_p (by norm_num) N hN hbot htop

end FreyPrimeFiltrationCompleteTest
