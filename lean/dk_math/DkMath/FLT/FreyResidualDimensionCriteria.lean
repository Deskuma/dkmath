/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualNontrivial
import DkMath.Lib.NumberTheory.EllipticTwoTorsionRank

#print "file: DkMath.FLT.FreyResidualDimensionCriteria"

/-!
# 同じFrey曲線で、一次元を排除する残りの条件を比較する

奇数指数の根と点の正確な対応を同じSourceへ運ぶ。素数指数では次元2への残りの入力を
「pより多い点」「非零点の直線の外の点」「相異なる根が(p−1)/2個を超えること」へ翻訳する。
一般の奇素数ではこの条件自体を供給していない。指数2では三次式の判別式によって
幾何学的な入力を供給でき、同じ曲線の位数4・次元2・直線の外の点まで無条件に得る。
ガロア不変直線の不存在、既約性やFLT37の終点とは区別する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} (S : Source p)

/-- 奇数指数では、同じ残余空間の点数は1+2r。rは相異なる根の数である。 -/
theorem residual_odd_card_eq_roots (hp : Odd p) :
    Nat.card S.ResidualSpace = 1 + 2 * divisionRootCount S.rationalCurve p := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_eq_one_add_twice_roots S.rationalCurve hp

variable [Fact p.Prime]

/-- pを超える小さい追加下界で、同じSourceの位数p²が確定する。 -/
theorem residual_card_eq_prime_sq_of_prime_lt (h : p < Nat.card S.ResidualSpace) :
    Nat.card S.ResidualSpace = p ^ 2 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_eq_prime_sq_of_prime_lt S.rationalCurve p h

/-- 同じ残余空間の次元2と、pより多い点の存在は同値である。 -/
theorem residual_finrank_eq_two_iff_prime_lt_card :
    Module.finrank (ZMod p) S.ResidualSpace = 2 ↔ p < Nat.card S.ResidualSpace := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_eq_two_iff_prime_lt_card S.rationalCurve p

/-- 任意に指定した非零点について、その直線の外にある点を探せば十分である。 -/
theorem residual_finrank_eq_two_iff_exists_outside_span (P : S.ResidualSpace) (hP : P ≠ 0) :
    Module.finrank (ZMod p) S.ResidualSpace = 2 ↔
      ∃ Q : S.ResidualSpace, Q ∉ Submodule.span (ZMod p) ({P} : Set S.ResidualSpace) :=
  finrank_torsion_eq_two_iff_exists_outside_span S.rationalCurve p P hP

/-- 奇素数の幾何学的な残りの入力を、相異なる根の下界として明示する。 -/
theorem residual_finrank_eq_two_iff_root_count (hp : Odd p) :
    Module.finrank (ZMod p) S.ResidualSpace = 2 ↔
      (p - 1) / 2 < divisionRootCount S.rationalCurve p := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_eq_two_iff_root_count S.rationalCurve p hp

/-- 非零点の直線の外を探すことと、根の下界の供給は同じSource上で同値である。 -/
theorem residual_exists_outside_span_iff_root_count (hp : Odd p) (P : S.ResidualSpace) (hP : P ≠ 0) :
    (∃ Q : S.ResidualSpace, Q ∉ Submodule.span (ZMod p) ({P} : Set S.ResidualSpace)) ↔
      (p - 1) / 2 < divisionRootCount S.rationalCurve p := by
  have := S.rationalCurve_isElliptic
  exact exists_outside_span_iff_root_count S.rationalCurve p hp P hP

end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable (S : Source 2)

/-- 指数2では同じFrey曲線の実際の残余空間の位数が4である。 -/
theorem residual_two_card : Nat.card S.ResidualSpace = 4 := by
  have := S.rationalCurve_isElliptic
  exact card_torsion_two S.rationalCurve

/-- 指数2では追加の位数・次元の仮定なしで二次元を得る。 -/
theorem residual_two_finrank : Module.finrank (ZMod 2) S.ResidualSpace = 2 := by
  have := S.rationalCurve_isElliptic
  exact finrank_torsion_two S.rationalCurve

/-- 指数2では、任意の非零残余点の直線の外に実際の第二の点を供給する。 -/
theorem residual_two_exists_outside_span (P : S.ResidualSpace) (hP : P ≠ 0) :
    ∃ Q : S.ResidualSpace, Q ∉ Submodule.span (ZMod 2) ({P} : Set S.ResidualSpace) := by
  have := S.rationalCurve_isElliptic
  exact exists_torsion_two_outside_span S.rationalCurve P hP

end DkMath.FLT.Frey.Source
