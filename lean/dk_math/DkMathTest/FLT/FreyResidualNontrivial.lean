/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualNontrivial
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualNontrivial"

/-!
# NOTE-014: 根から作った実際の非零点と、楕円曲線性の境界

実在するSource 2の曲線で、その同じ曲線のE[37]の非零点と下界を検査する。
合成数4にも非零点の構成を適用し、素数性を必要とする線形代数と区別する。
n=1には非零点が存在しない。また尖点曲線の原点は曲線方程式を満たすが特異であり、
方程式の根だけで実際の非特異点群へ入れたことにしてはいけない。
-/
namespace FreyResidualNontrivialTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest
open WeierstrassCurve
open scoped WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- Source 37の仮想的な存在に頼らず、実在する同じ曲線の37-torsionの非零点を得る。 -/
theorem actualCurve37_exists_ne_zero : ∃ P : Torsion sample.rationalCurve 37, P ≠ 0 :=
  exists_nonzero_torsion_of_one_lt sample.rationalCurve 37 (by decide)

/-- 上界だけでなく下界1も、追加の点や位数を仮定せずに供給できる。 -/
theorem actualCurve37_dimension_bounds :
    1 ≤ Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) ∧
      Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) ≤ 2 :=
  finrank_torsion_bounds sample.rationalCurve 37

/-- 37点以上1369点以下。1369点の存在はこのテストでは主張しない。 -/
theorem actualCurve37_card_bounds :
    37 ≤ Nat.card (Torsion sample.rationalCurve 37) ∧
      Nat.card (Torsion sample.rationalCurve 37) ≤ 1369 :=
  card_torsion_bounds sample.rationalCurve 37

/-- 標準torsionBy表示でも、点を保つ線形同型から正の次元が得られる。 -/
theorem actualCurve37_standard_positive :
    0 < Module.finrank (ZMod 37) (StandardTorsion sample.rationalCurve 37) :=
  finrank_standardTorsion_pos sample.rationalCurve 37

/-- 非零点の幾何学的構成は合成数にも使える。F₄という体を仮定してはいない。 -/
theorem actualCurve4_exists_ne_zero : ∃ P : Torsion sample.rationalCurve 4, P ≠ 0 :=
  exists_nonzero_torsion_of_one_lt sample.rationalCurve 4 (by decide)

/-- 素数Sourceの同じ曲線から、次元・点数の上下界と有限レベルをまとめる。 -/
theorem source37_profile (S : Source 37) :
    (1 ≤ Module.finrank (ZMod 37) S.ResidualSpace ∧
      Module.finrank (ZMod 37) S.ResidualSpace ≤ 2) ∧
      (37 ≤ Nat.card S.ResidualSpace ∧ Nat.card S.ResidualSpace ≤ 37 ^ 2) ∧
      S.ResidualFactorsThroughFiniteLevel :=
  S.residual_nontrivial_profile

/-- 尖点曲線y²=x³。非特異性のガードを検査するための退化した三次曲線。 -/
def cuspidal : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

/-- 原点は曲線方程式の解である。 -/
theorem cuspidal_origin_equation :
    (cuspidal.toAffine⁄(AlgebraicClosure ℚ)).Equation 0 0 := by
  rw [Affine.equation_iff]
  norm_num [cuspidal, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- しかし原点は特異点であり、実際の点群の有限座標点として構成できない。 -/
theorem cuspidal_origin_singular :
    ¬ (cuspidal.toAffine⁄(AlgebraicClosure ℚ)).Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  norm_num [cuspidal, WeierstrassCurve.baseChange, WeierstrassCurve.map]

example : ¬ ∃ P : Torsion sample.rationalCurve 1, P ≠ 0 := by
  rintro ⟨P, hP⟩
  exact hP (torsion_one_eq_zero _ P)
example : Nontrivial (Torsion sample.rationalCurve 37) := inferInstance
example : Nontrivial sample.ResidualSpace := sample.residual_nontrivial
example : Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) = 1 ∨
    Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) = 2 :=
  finrank_torsion_one_or_two sample.rationalCurve 37

end FreyResidualNontrivialTest
