/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualDimensionBound
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualDimensionBound"

/-!
# NOTE-013: 実在する曲線の37-torsionと、小さい指数での境界検査

Source 2の原始ピタゴラス解から作った同じ有理曲線でE[37]を検査する。
Source 37の存在を仮定するテストとは異なり、この曲線自体は実在する。
一方E[2]では既知の非零点から次元の正値性も得られるが、それだけで次元2とは言わない。
x=0のファイバーが1点だけになる例は、「高々2点」を「常に2点」と読めないことも示す。
-/
namespace FreyResidualDimensionBoundTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest
open WeierstrassCurve
open scoped WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- 実在する同じ曲線のE[37]。有限性や位数の仮定を追加しない。 -/
theorem actualCurve37_dimension :
    Module.finrank (ZMod 37) (Torsion sample.rationalCurve 37) ≤ 2 :=
  finrank_torsion_le_two sample.rationalCurve 37

/-- 粗い2737点の上界を、線形代数に戻すことで1369点に改善する。 -/
theorem actualCurve37_card : Nat.card (Torsion sample.rationalCurve 37) ≤ 1369 := by
  exact card_torsion_le_prime_sq sample.rationalCurve 37

/-- 同じ点を保つ標準torsionBy表示でも上界は変わらない。 -/
theorem actualCurve37_standard_dimension :
    Module.finrank (ZMod 37) (StandardTorsion sample.rationalCurve 37) ≤ 2 :=
  finrank_standardTorsion_le_two sample.rationalCurve 37

/-- E[2]には実際の非零点がある。一般定理の0次元という候補を、この例では排除できる。 -/
theorem actualCurve2_dimension :
    0 < Module.finrank (ZMod 2) sample.ResidualSpace ∧
      Module.finrank (ZMod 2) sample.ResidualSpace ≤ 2 := by
  refine ⟨?_, sample.residual_finrank_le_two⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨twoPoint, twoPoint_ne_zero⟩

/-- 自己反転する2-torsion点では、同じxのファイバーが1点に縮む。 -/
theorem zero_fiber_singleton :
    affineXFiber sample.rationalCurve 0 = {twoPoint.val} := by
  classical
  have hn : -(twoPoint.val) = twoPoint.val := by
    apply neg_eq_of_add_eq_zero_left
    have h := twoPoint.property
    change 2 • twoPoint.val = 0 at h
    simpa only [two_nsmul] using h
  ext P
  change P.xRep = ![0, 1] ↔ P = twoPoint.val
  have hx : twoPoint.val.xRep = ![0, 1] := rfl
  rw [← hx]
  have he : P.xRep = twoPoint.val.xRep ↔ P = twoPoint.val ∨ P = -twoPoint.val :=
    Affine.Point.xRep_eq_xRep_iff
  simpa only [hn, or_self] using he

/-- Source 37を仮定する入口も、同じSourceのまま上界と有限レベルを供給する。 -/
theorem source37_profile (S : Source 37) :
    Module.finrank (ZMod 37) S.ResidualSpace ≤ 2 ∧
      Nat.card S.ResidualSpace ≤ 37 ^ 2 ∧ S.ResidualFactorsThroughFiniteLevel :=
  S.residual_bounded_profile

example : 1 + 2 * (2 ^ 2 - 1) < 2 ^ 3 := degree_bound_lt_cube 2 (by decide)
example : 1 + 2 * (37 ^ 2 - 1) < 37 ^ 3 := degree_bound_lt_cube 37 (by decide)
example : Nat.card (Torsion sample.rationalCurve 1) ≤ 1 :=
  card_torsion_le_degree_bound sample.rationalCurve 1 (by decide)
example : (affineXFiber sample.rationalCurve 0).ncard = 1 := by
  rw [zero_fiber_singleton, Set.ncard_singleton]

end FreyResidualDimensionBoundTest
