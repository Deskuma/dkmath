/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeGoodFiltration
import DkMath.Lib.NumberTheory.EllipticNodalTorsion

#print "file: DkMathTest.FLT.FreyPrimeFiltration"

/-!
# NOTE-031-004: 還元核と節点p捩れ排除の実例、指数37の良還元入口

尖点曲線y²=x³は楕円曲線ではないが、その滑らかな点群において還元核の一般構成を試せる。
P=(1/4,1/8)は2上の全付値環で極を持ち、P+Pも同じ還元核に入る。
整点R=(1,1)との和は(1/9,1/27)であり、整点＋極の点の整性を実際の加法でも確認する。
節点曲線y²=x³+x²については標数5の5捩れ点が零だけであることを確認する。
Source37の例は良還元を明示したAPI特殊化であり、整数反例の存在を主張しない。
-/
namespace FreyPrimeFiltrationTest
open WeierstrassCurve Affine
open DkMath.Lib.NumberTheory EllipticDyadicSeparation EllipticReductionKernel ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- 還元核の構成に楕円曲線性を要求しないことを試す尖点モデル。 -/
noncomputable def cusp : WeierstrassCurve (AlgebraicClosure ℚ) := ⟨0, 0, 0, 0, 0⟩

/-- P=(1/4,1/8)は尖点自身を除く滑らかな有限点である。 -/
theorem pole_nonsingular : cusp.toAffine.Nonsingular (1/4) (1/8) := by
  norm_num [cusp, nonsingular_iff, equation_iff, negY]

/-- 実際の極の候補点。 -/
noncomputable def polePoint : cusp.toAffine.Point := Point.some (1/4) (1/8) pole_nonsingular

/-- R=(1,1)も同じ尖点曲線の滑らかな整点である。 -/
theorem integral_nonsingular : cusp.toAffine.Nonsingular 1 1 := by
  norm_num [cusp, nonsingular_iff, equation_iff, negY]

/-- 同じ曲線の実際の整点。 -/
noncomputable def integralPoint : cusp.toAffine.Point := Point.some 1 1 integral_nonsingular

/-- 尖点モデルは任意の付値環において整である。 -/
theorem cusp_integral (A : ValuationSubring (AlgebraicClosure ℚ)) : Integral A cusp :=
  ⟨A.zero_mem, A.zero_mem, A.zero_mem, A.zero_mem, A.zero_mem⟩

/-- Pは任意の2上の付値環で還元核に属する。 -/
theorem pole_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    polePoint ∈ ofIntegral A cusp (cusp_integral A) := by
  rw [mem_ofIntegral_iff, polePoint, poleOrZero_some_iff]
  have h2 : A.valuation (2 : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
  have h4 : A.valuation (4 : AlgebraicClosure ℚ) < 1 := by
    rw [show (4 : AlgebraicClosure ℚ) = 2 ^ 2 by norm_num, map_pow]
    exact pow_lt_one₀ zero_le h2 (by decide)
  rw [one_div, map_inv₀, one_lt_inv₀]
  · exact h4
  · exact (Valuation.pos_iff _).mpr (by norm_num)

/-- 実際の二倍点も同じ還元核へ入る。単元位数の仮定を追加しない。 -/
theorem double_pole_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    polePoint + polePoint ∈ ofIntegral A cusp (cusp_integral A) :=
  (ofIntegral A cusp (cusp_integral A)).add_mem (pole_mem A hA) (pole_mem A hA)

/-- 整点と極の点の和のx座標は実際に1/9となる。 -/
theorem integral_plus_pole_x :
    cusp.toAffine.addX 1 (1/4) (cusp.toAffine.slope 1 (1/4) 1 (1/8)) = 1/9 := by
  norm_num [cusp, Affine.slope, addX]

/-- 和の候補(1/9,1/27)は同じ曲線の滑らかな点である。 -/
theorem sum_nonsingular : cusp.toAffine.Nonsingular (1/9) (1/27) := by
  norm_num [cusp, nonsingular_iff, equation_iff, negY]

/-- 実際の点の加法でも、整点と極の点の和は(1/9,1/27)となる。 -/
theorem integral_plus_pole : integralPoint + polePoint = Point.some (1/9) (1/27) sum_nonsingular := by
  rw [integralPoint, polePoint, Point.add_of_X_ne (by norm_num : (1 : AlgebraicClosure ℚ) ≠ 1/4)]
  norm_num [cusp, Affine.slope, addX, addY, negAddY, negY]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 剰余標数5の節点曲線。 -/
def node5 : WeierstrassCurve (ZMod 5) := ⟨0, 1, 0, 0, 0⟩

/-- 節点曲線の滑らかな点群には非零5捩れ点がない。 -/
theorem node5_no_five_torsion (P : node5.toAffine.Point) (hP : 5 • P = 0) : P = 0 := by
  exact EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion node5 0 0
    (by norm_num [node5, equation_iff])
    (by norm_num [node5, nonsingular_iff, equation_iff, negY])
    (by change (4 : ZMod 5) ≠ 0; decide) P hP

/-- 指数37の良還元ケースで、全ての37上の付値環に同じ側の二択が成立する。 -/
theorem source37_good_common_side (S : DkMath.FLT.Frey.Source 37)
    (hgood : ¬ (37 : ℤ) ∣ S.a * S.b * S.c)
    (N : Submodule (ZMod 37) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 37 →
      FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 37 →
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact S.residual_common_side_at_p_of_good (by norm_num) hgood N hN hbot htop

end FreyPrimeFiltrationTest
