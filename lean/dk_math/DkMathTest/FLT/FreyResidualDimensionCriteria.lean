/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualDimensionCriteria
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualDimensionCriteria"

/-!
# NOTE-015: 実際の独立な第二の点と、37次で残る根の下界

実在するSource 2の曲線のE[2]は4点・二次元である。既存の非零点twoPointを固定しても
その直線の外に点を取れる。一方、同じ曲線のE[37]では根の正確な計数と判定条件を検査し、
相異なる根が18個を超えるという未供給の下界を結論へ紛れ込ませない。
-/
namespace FreyResidualDimensionCriteriaTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- 判別式から得た実際の相異なる三根。多重度込みの次数だけで数えてはいない。 -/
theorem actualCurve2_roots : divisionRootCount sample.rationalCurve 2 = 3 :=
  divisionRootCount_two sample.rationalCurve

/-- 同じ曲線の実際のE[2]の位数は4である。 -/
theorem actualCurve2_card : Nat.card sample.ResidualSpace = 4 := sample.residual_two_card

/-- 次元の候補を並べるだけでなく、この指数では次元2に確定できる。 -/
theorem actualCurve2_dimension : Module.finrank (ZMod 2) sample.ResidualSpace = 2 :=
  sample.residual_two_finrank

/-- 既知のtwoPointと、その直線の外の第二の点が同じ実際の曲線に存在する。 -/
theorem actualTwoPoint_outside_span :
    ∃ Q : sample.ResidualSpace,
      Q ∉ Submodule.span (ZMod 2) ({twoPoint} : Set sample.ResidualSpace) :=
  sample.residual_two_exists_outside_span twoPoint twoPoint_ne_zero

/-- 同じ曲線のE[37]で、相異なる根ごとに異なる二点があることを検査する。 -/
theorem actualCurve37_count : Nat.card (Torsion sample.rationalCurve 37) =
    1 + 2 * divisionRootCount sample.rationalCurve 37 :=
  card_torsion_eq_one_add_twice_roots sample.rationalCurve (by decide)

/-- 指数37の残る課題は、相異なる根の数が18を超えることである。 -/
theorem actualCurve37_frontier :
    Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) = 2 ↔
      18 < divisionRootCount sample.rationalCurve 37 :=
  finrank_torsion_eq_two_iff_root_count sample.rationalCurve 37 (by decide)

/-- 指定した非零37-torsion点の直線の外を探す問題も、同じ根の下界へ翻訳される。 -/
theorem actualCurve37_outside_frontier (P : Torsion sample.rationalCurve 37) (hP : P ≠ 0) :
    (∃ Q : Torsion sample.rationalCurve 37,
      Q ∉ Submodule.span (ZMod 37) ({P} : Set (Torsion sample.rationalCurve 37))) ↔
      18 < divisionRootCount sample.rationalCurve 37 :=
  exists_outside_span_iff_root_count sample.rationalCurve 37 (by decide) P hP

/-- Source 37を入力する場合も、追加の位数・次元の入力なしで同じ条件へ到達する。 -/
theorem source37_frontier (S : Source 37) :
    Module.finrank (ZMod 37) S.ResidualSpace = 2 ↔ 18 < divisionRootCount S.rationalCurve 37 :=
  S.residual_finrank_eq_two_iff_root_count (by decide)

example : divisionRootCount sample.rationalCurve 1 = 0 := by
  classical
  simp [divisionRootCount, divisionRoots]
example : Nat.card sample.ResidualSpace ≠ 1 + 2 * divisionRootCount sample.rationalCurve 2 := by
  rw [actualCurve2_card, actualCurve2_roots]
  decide
example : Module.finrank (ZMod 2) (StandardTorsion sample.rationalCurve 2) = 2 :=
  finrank_standardTorsion_two sample.rationalCurve

end FreyResidualDimensionCriteriaTest
