/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualDimensionCriteria
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber

#print "file: DkMath.FLT.FreyResidualRankTwo"

/-!
# 同じFrey曲線の実際の残余空間は二次元である

正則ファイバーから核への単射による下界と、NOTE-013の上界を合わせた一般定理へ
同じSourceの楕円曲線性を供給する。位数・次元・独立な二点を追加入力にせず、
実際の残余空間の位数p²・次元2を得る。既存の有限レベルも同じ曲線のまま保持する。
これはガロア不変直線の不存在や既約性、Weil対・行列式・Artin導手・FLTの終点ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p) [Fact p.Prime]

/-- 実際のE[p]の位数はp²である。幾何学的な下界を外部の仮定にしない。 -/
theorem residual_card_prime_sq : Nat.card S.ResidualSpace = p ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_prime_sq S.rationalCurve p

/-- 同じ曲線の素数残余空間は二次元である。 -/
theorem residual_finrank_eq_two : Module.finrank (ZMod p) S.ResidualSpace = 2 := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_prime S.rationalCurve p

/-- 任意の非零点の直線の外に、同じ実際の残余空間の第二の点が存在する。 -/
theorem residual_exists_outside_span (P : S.ResidualSpace) (hP : P ≠ 0) :
    ∃ Q : S.ResidualSpace, Q ∉ Submodule.span (ZMod p) ({P} : Set S.ResidualSpace) := by
  have := S.rationalCurve_isElliptic
  exact exists_torsion_prime_outside_span S.rationalCurve p P hP

/-- 位数・二次元・有限ガロアレベルを同じSourceから供給する。 -/
theorem residual_rank_two_profile :
    Nat.card S.ResidualSpace = p ^ 2 ∧ Module.finrank (ZMod p) S.ResidualSpace = 2 ∧
      S.ResidualFactorsThroughFiniteLevel :=
  ⟨S.residual_card_prime_sq, S.residual_finrank_eq_two,
    S.residual_factorsThroughFiniteLevel_of_prime⟩

/-- 奇素数ではΨSqₚの相異なる根の数も(p²−1)/2に確定する。 -/
theorem residual_odd_prime_roots (hp : Odd p) :
    divisionRootCount S.rationalCurve p = (p ^ 2 - 1) / 2 := by
  have := S.rationalCurve_isElliptic
  exact divisionRootCount_odd_prime S.rationalCurve p hp

end DkMath.FLT.Frey.Source
