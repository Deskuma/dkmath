/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualCyclotomic
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualCyclotomic"

/-!
# NOTE-018: 交代対の行列式、非退化性の必要性、実際の37次入口

F₃₇²で面積対と非自明な対角作用を構成し、同変性から行列式指標を同定する。
零の対も任意の指標について同変になるので、非退化性を落とすと結論が偽になる例も検査する。
実在するSource 2の曲線の37倍写像は全射である。円分行列式の入口には実際のE[37]上の
Weil対データを明示入力し、その存在をこの回帰で作ったとは扱わない。
-/
namespace FreyResidualCyclotomicTest
open Module
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
open FreyResidualRepresentationTest
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic
abbrev Plane := Fin 2 → ZMod 37

/-- 二次元の標準的な面積対。乗法的Weil対の幾何学とは独立の線形代数の実例。 -/
def area : Plane →ₗ[ZMod 37] Plane →ₗ[ZMod 37] ZMod 37 :=
  LinearMap.mk₂ _ (fun x y => x 0 * y 1 - x 1 * y 0)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem area_alternating (x : Plane) : area x x = 0 := by
  change x 0 * x 1 - x 1 * x 0 = 0
  ring

theorem area_nondegenerate (x : Plane) (h : ∀ y, area x y = 0) : x = 0 := by
  have hx : x 0 = 0 := by simpa [area] using h ![0, 1]
  have hy : x 1 = 0 := by simpa [area] using h ![1, 0]
  ext i
  fin_cases i
  · exact hx
  · exact hy

/-- 第一座標だけをu倍する非自明な作用。 -/
def diagonalMap (u : (ZMod 37)ˣ) : Plane →ₗ[ZMod 37] Plane where
  toFun x := ![(u : ZMod 37) * x 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' a x := by ext i; fin_cases i <;> simp [mul_left_comm]

def diagonalRepresentation : Representation (ZMod 37) (ZMod 37)ˣ Plane where
  toFun := diagonalMap
  map_one' := by ext x i; fin_cases i <;> simp [diagonalMap]
  map_mul' u v := by ext x i; fin_cases i <;> simp [diagonalMap, mul_assoc]

theorem area_equivariant (u : (ZMod 37)ˣ) (x y : Plane) :
    area (diagonalRepresentation u x) (diagonalRepresentation u y) = (u : ZMod 37) * area x y := by
  change ((u : ZMod 37) * x 0) * y 1 - x 1 * ((u : ZMod 37) * y 0) =
    (u : ZMod 37) * (x 0 * y 1 - x 1 * y 0)
  ring

/-- 行列式の計算結果を仮定せず、交代対の同変性から非自明な指標を復元する。 -/
theorem diagonal_determinant :
    determinantCharacterWithBasis diagonalRepresentation (Pi.basisFun (ZMod 37) (Fin 2)) =
      MonoidHom.id (ZMod 37)ˣ := by
  apply determinantCharacter_eq_of_equivariant_pairing _ _ _ area area_alternating area_nondegenerate
  exact area_equivariant

/-- 零の対は自明指標について同変だが、この表現の行列式は自明ではない。
非退化性を忘れた形の円分行列式の推論は成立しない。 -/
theorem degenerate_pairing_does_not_determine_character :
    (∀ u x y, (0 : Plane →ₗ[ZMod 37] Plane →ₗ[ZMod 37] ZMod 37)
      (diagonalRepresentation u x) (diagonalRepresentation u y) =
        (1 : ZMod 37) • (0 : Plane →ₗ[ZMod 37] Plane →ₗ[ZMod 37] ZMod 37) x y) ∧
    determinantCharacterWithBasis diagonalRepresentation (Pi.basisFun (ZMod 37) (Fin 2)) ≠ 1 := by
  refine ⟨by intros; simp, ?_⟩
  rw [diagonal_determinant]
  intro h
  have hh := congrArg (fun χ : (ZMod 37)ˣ →* (ZMod 37)ˣ =>
    (χ (Units.mk0 2 (by decide)) : ZMod 37)) h
  change (2 : ZMod 37) = 1 at hh
  exact (by decide : (2 : ZMod 37) ≠ 1) hh

/-- 実際の円分指標の定義式。楕円曲線の対を仮定しない。 -/
theorem actual37_cyclotomic_action (σ : Field.absoluteGaloisGroup ℚ)
    (z : rootsOfUnity 37 (AlgebraicClosure ℚ)) :
    σ.toAlgHom (z.val : AlgebraicClosure ℚ) =
      (z.val : AlgebraicClosure ℚ) ^ (cyclotomicCharacter 37 σ : ZMod 37).val :=
  cyclotomicCharacter_spec 37 σ z

/-- 乗法的な37乗根へのスカラー倍翻訳。任意のZMod値を扱い代表元の演算を固定する。 -/
theorem actual37_root_smul (a : ZMod 37) (z : RootSpace (AlgebraicClosure ℚ) 37) :
    (a • z).toMul = z.toMul ^ a.val := smul_toMul _ _ a z

/-- 仮想的Source 37によらず、実在する同じ曲線の37倍写像は全射。 -/
theorem actual37_multiplication_surjective :
    Function.Surjective (nsmulAddMonoidHom 37 : Points sample.rationalCurve →+ Points sample.rationalCurve) :=
  multiplication_surjective sample.rationalCurve 37 (by decide)

/-- 合成数も扱える。素数の点数公式に依存しない全射性。 -/
theorem actual4_multiplication_surjective :
    Function.Surjective (nsmulAddMonoidHom 4 : Points sample.rationalCurve →+ Points sample.rationalCurve) :=
  multiplication_surjective sample.rationalCurve 4 (by decide)

/-- 全射性にn≠0が必要である。既存の実際の非零点を使って零倍写像を反例とする。 -/
theorem zero_multiplication_not_surjective :
    ¬ Function.Surjective (nsmulAddMonoidHom 0 : Points sample.rationalCurve →+ Points sample.rationalCurve) := by
  intro h
  obtain ⟨P, hP⟩ := h (underlying sample.rationalCurve twoPoint)
  have hz : underlying sample.rationalCurve twoPoint = 0 := by simpa using hP.symm
  apply twoPoint_ne_zero
  exact underlying_injective sample.rationalCurve hz

/-- 実在する曲線のE[37]についての、Weil対入力を保持する条件付き円分行列式。 -/
theorem actual37_determinant_of_pairing (w : WeilPairingData sample.rationalCurve 37) :
    determinantCharacterWithBasis (representation sample.rationalCurve 37) (torsionBasis sample.rationalCurve 37) =
      cyclotomicCharacter 37 := torsion_determinant_eq_cyclotomic_of_pairing _ _ w

/-- 同じ基底対の値の原始性も、非退化なWeil対入力から得る。 -/
theorem actual37_primitive_of_pairing (w : WeilPairingData sample.rationalCurve 37) :
    IsPrimitiveRoot (w.pairing.value (torsionBasis sample.rationalCurve 37 0)
      (torsionBasis sample.rationalCurve 37 1) : AlgebraicClosure ℚ) 37 :=
  weil_basis_isPrimitiveRoot _ _ w

/-- 仮想反例のSource側も、明示した対入力だけで同じ指標へ接続する。 -/
theorem source37_determinant_of_pairing (S : DkMath.FLT.Frey.Source 37) (w : S.ResidualWeilPairingData) :
    S.residualDeterminantCharacter = cyclotomicCharacter 37 :=
  S.residual_determinant_eq_cyclotomic_of_pairing w

end FreyResidualCyclotomicTest
