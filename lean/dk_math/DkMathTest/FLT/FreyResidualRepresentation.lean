/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualRepresentation"

/-!
# NOTE-010 回帰: 実際の非零torsion点と、Pascal差分の限界

p=2の実在するFrey Sourceの点(0,0)は非零の2-torsionで、ガロア作用が固定する。
従って構成した表現は零作用素ではない。E[1]は逆に零点だけになる。
37次は反例を入力とする条件付き入口として検査する。
F₃₇²の非自明shearはT³⁷=1かつ(T−1)²=0であり、冪零差分からT=1は導けない。
-/
namespace FreyResidualRepresentationTest
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation FreyGapCubic
open DkMath.Lib.RepresentationTheory.PascalDifference
open WeierstrassCurve Module
open scoped WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 実在する原始ピタゴラス解。p≥5の反例の存在とは区別する。 -/
def sample : Source 2 where
  a := 4
  b := 3
  c := 5
  a_ne := by decide
  b_ne := by decide
  c_ne := by decide
  coprime := ⟨1, -1, by norm_num⟩
  equation := by norm_num
  normalization := ⟨by norm_num, by norm_num⟩

/-- 同じFrey曲線で(0,0)は非特異である。 -/
theorem zero_coordinates_nonsingular :
    (sample.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  norm_num [Source.rationalCurve, sample, normalized, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- 実際のE[2]の非零点。二倍零の証拠を同じ点とともに記録する。 -/
noncomputable def twoPoint : sample.ResidualSpace := by
  classical
  refine ⟨Affine.Point.some 0 0 zero_coordinates_nonsingular, ?_⟩
  change 2 • (Affine.Point.some 0 0 zero_coordinates_nonsingular) = 0
  rw [two_nsmul]
  apply Affine.Point.add_self_of_Y_eq
  simp [Affine.negY, Source.rationalCurve, sample, normalized,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- 零点を形式的に用意しただけの空間でないことを確認する。 -/
theorem twoPoint_ne_zero : twoPoint ≠ 0 := by
  intro h
  have he := congrArg (underlying sample.rationalCurve) h
  exact Affine.Point.some_ne_zero zero_coordinates_nonsingular he

/-- 有理座標の同じ点は、全ガロア元で固定される。 -/
theorem twoPoint_fixed (σ : Field.absoluteGaloisGroup ℚ) :
    sample.residualRepresentation σ twoPoint = twoPoint := by
  apply Subtype.ext
  change Affine.Point.some (σ.toAlgHom 0) (σ.toAlgHom 0) _ =
    Affine.Point.some 0 0 zero_coordinates_nonsingular
  simp only [map_zero]

example (σ : Field.absoluteGaloisGroup ℚ) : sample.residualRepresentation σ ≠ 0 := by
  intro h
  have he : sample.residualRepresentation σ twoPoint = 0 := by rw [h, LinearMap.zero_apply]
  exact twoPoint_ne_zero ((twoPoint_fixed σ).symm.trans he)
example (P : Torsion sample.rationalCurve 1) : P = 0 := torsion_one_eq_zero _ P
example : Continuous (fun z : Field.absoluteGaloisGroup ℚ × sample.ResidualSpace =>
    sample.residualRepresentation z.1 z.2) := sample.residual_action_continuous
example (S : Source 37) (σ : Field.absoluteGaloisGroup ℚ) (P : S.ResidualSpace) :
    S.residualRepresentation σ⁻¹ (S.residualRepresentation σ P) = P :=
  representation_inverse _ _ σ P
example (S : Source 37) (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualRepresentation σ - 1) ^ 37 = S.residualRepresentation (σ ^ 37) - 1 :=
  S.residual_difference_pow σ
example (S : Source 37) (σ : Field.absoluteGaloisGroup ℚ)
    (hσ : S.residualRepresentation (σ ^ 37) = 1) :
    (S.residualRepresentation σ - 1) ^ 37 = 0 := S.residual_difference_nilpotent σ hσ
example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) :
    let S := Source.ofCounterexample 37 (by decide) (by decide) a b c ha hb hc he
    Continuous (fun z : Field.absoluteGaloisGroup ℚ × S.ResidualSpace => S.residualRepresentation z.1 z.2) :=
  (Source.ofCounterexample_residual_entrance 37 (by decide) (by decide) a b c ha hb hc he).2.1

abbrev Plane := ZMod 37 × ZMod 37
/-- 差分N(x,y)=(y,0)。 -/
noncomputable def shift : End (ZMod 37) Plane where
  toFun x := (x.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp
/-- N²=0を成分ごとに確認する。 -/
theorem shift_square : shift ^ 2 = 0 := by rfl
/-- 非自明な上三角shear。 -/
noncomputable def shear : End (ZMod 37) Plane := 1 + shift
/-- 同じ作用素の差分を記録する。 -/
theorem shear_difference : shear - 1 = shift := by unfold shear; abel
/-- 37回の逐次展開なしで、Pascal差分等式からT³⁷=1を得る。 -/
theorem shear_pow : shear ^ 37 = 1 := by
  have hn : shift ^ 37 = 0 := pow_eq_zero_of_le (by decide : 2 ≤ 37) shift_square
  have h := end_difference_pow (p := 37) shear
  rw [shear_difference, hn] at h
  exact sub_eq_zero.mp h.symm
/-- 冪零な差分を持っていても、作用そのものが恒等になるとは限らない。 -/
theorem shear_ne_one : shear ≠ 1 := by
  intro h
  have he := congrArg (fun f : End (ZMod 37) Plane => (f (0, 1)).1) h
  change (1 : ZMod 37) = 0 at he
  exact one_ne_zero he

example : (shear - 1) ^ 37 = 0 := by rw [end_difference_pow, shear_pow, sub_self]
example : shear ^ 37 = 1 ∧ shear ≠ 1 := ⟨shear_pow, shear_ne_one⟩
example : (Polynomial.X - 1 : Polynomial (ZMod 37)) ^ 37 = Polynomial.X ^ 37 - 1 :=
  polynomial_difference_pow
end FreyResidualRepresentationTest
