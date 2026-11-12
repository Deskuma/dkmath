/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualRankTwo
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualRankTwo"

/-!
# NOTE-016: 仮想反例に依存しないE[37]の位数・次元と、正則性の境界

実在するSource 2の曲線のE[37]で位数1369・次元2・相異なる根684個を確認する。
任意の非零点の直線の外にも実際の点がある。合成数4では下界16だけを検査し、
素数の上界を合成数へ流用しない。一般有理関数ではX²の零ファイバーが重根を持つ例を検査する。
-/
namespace FreyResidualRankTwoTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra
open FreyResidualRepresentationTest
open Polynomial
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- 仮想的なSource 37ではなく、実在する同じ曲線の37-torsionは1369点である。 -/
theorem actualCurve37_card : Nat.card (Torsion sample.rationalCurve 37) = 1369 :=
  card_torsion_prime_sq sample.rationalCurve 37

/-- 幾何学的providerによって、以前の次元1の候補を排除する。 -/
theorem actualCurve37_dimension : Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) = 2 :=
  finrank_torsion_prime sample.rationalCurve 37

/-- 18個を超えるという従来のfrontierを越え、相異なる根は684個に確定する。 -/
theorem actualCurve37_roots : divisionRootCount sample.rationalCurve 37 = 684 :=
  divisionRootCount_odd_prime sample.rationalCurve 37 (by decide)

/-- 同じ実際のE[37]の任意の非零点に対し、直線の外の第二の点を供給する。 -/
theorem actualCurve37_outside (P : Torsion sample.rationalCurve 37) (hP : P ≠ 0) :
    ∃ Q : Torsion sample.rationalCurve 37,
      Q ∉ Submodule.span (ZMod 37) ({P} : Set (Torsion sample.rationalCurve 37)) :=
  exists_torsion_prime_outside_span sample.rationalCurve 37 P hP

/-- 入力点も幾何学から作り、同じ実在するE[37]の中に独立な二点が存在することを確認する。 -/
theorem actualCurve37_independent_pair :
    ∃ P Q : Torsion sample.rationalCurve 37, P ≠ 0 ∧
      Q ∉ Submodule.span (ZMod 37) ({P} : Set (Torsion sample.rationalCurve 37)) := by
  obtain ⟨P, hP⟩ := exists_nonzero_torsion_of_one_lt sample.rationalCurve 37 (by decide)
  obtain ⟨Q, hQ⟩ := actualCurve37_outside P hP
  exact ⟨P, Q, hP, hQ⟩

/-- 素数性がない場合にも幾何学的下界は適用されるが、ここで位数の等号は主張しない。 -/
theorem actualCurve4_lower : 16 ≤ Nat.card (Torsion sample.rationalCurve 4) :=
  square_le_card_torsion sample.rationalCurve 4 (by decide)

/-- 標準torsionByでも同じ二次元が得られる。 -/
theorem actualCurve37_standard : Module.finrank (ZMod 37) (StandardTorsion sample.rationalCurve 37) = 2 :=
  finrank_standardTorsion_prime sample.rationalCurve 37

/-- Source 37を入力する入口も、位数・次元の追加仮定を必要としない。 -/
theorem source37_profile (S : Source 37) :
    Nat.card S.ResidualSpace = 37 ^ 2 ∧ Module.finrank (ZMod 37) S.ResidualSpace = 2 ∧
      S.ResidualFactorsThroughFiniteLevel := S.residual_rank_two_profile

/-- X²−cでc=0は重根を持つ。例外値を避ける工程を省略してはいけない。 -/
theorem quadratic_zero_not_separable :
    ¬ (RationalPolynomialFiber.fiberPolynomial (X ^ 2 : Polynomial (AlgebraicClosure ℚ)) 1 0).Separable := by
  intro h
  have hh : (X ^ 2 : Polynomial (AlgebraicClosure ℚ)).Separable := by
    simpa only [RationalPolynomialFiber.fiberPolynomial, C_0, zero_mul, sub_zero] using h
  have hn := (Polynomial.Separable.of_pow Polynomial.not_isUnit_X (by decide : 2 ≠ 0) hh).2
  norm_num at hn

example : 18 < divisionRootCount sample.rationalCurve 37 := by rw [actualCurve37_roots]; decide
example : Module.finrank (ZMod 2) sample.ResidualSpace = 2 := finrank_torsion_prime sample.rationalCurve 2
example : RationalPolynomialFiber.wronskian
    ((sample.rationalCurve.baseChange (AlgebraicClosure ℚ)).Φ 0)
    ((sample.rationalCurve.baseChange (AlgebraicClosure ℚ)).ΨSq 0) = 0 := by
  simp [RationalPolynomialFiber.wronskian]

end FreyResidualRankTwoTest
