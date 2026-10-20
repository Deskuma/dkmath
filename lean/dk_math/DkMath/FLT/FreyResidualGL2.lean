/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualRankTwo
import DkMath.Lib.NumberTheory.EllipticTorsionGL2

#print "file: DkMath.FLT.FreyResidualGL2"

/-!
# 同じSourceのGL₂実現と不変直線の判定基準

Sourceは整数のデータから定めた同じ有理Frey曲線を保持する。ここで新しい空間や
仮想的な表現へ置き換えることはせず、実際のResidualSpaceの基底を選び直す。
既存のResidualIsIrreducibleとIsGaloisStableをそのまま用い、安定直線の不存在との
同値を得る。二次元性・GL₂表示・有限レベルの供給には、追加の位数公式も
Weil対もMazur型仮定も必要ない。ただし安定直線が存在しないという算術は別の問題である。
-/
namespace DkMath.FLT.Frey.Source
open Module
open scoped Matrix
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} (S : Source p) [Fact p.Prime]

/-- 前章の無条件の次元2から選ぶ、同じ残余空間の基底。 -/
noncomputable def residualBasis : Basis (Fin 2) (ZMod p) S.ResidualSpace :=
  Module.finBasisOfFinrankEq (ZMod p) S.ResidualSpace S.residual_finrank_eq_two

/-- 任意の基底による同じ残余表現のGL₂表示。基底比較の入口にもなる。 -/
noncomputable def residualGL2WithBasis (b : Basis (Fin 2) (ZMod p) S.ResidualSpace) :
    Field.absoluteGaloisGroup ℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  matrixGroupHom S.residualRepresentation b

/-- 同じSourceから得るGL₂表現。 -/
noncomputable def residualGL2 :
    Field.absoluteGaloisGroup ℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  S.residualGL2WithBasis S.residualBasis

/-- 同じ作用の列ベクトル表示。 -/
noncomputable def residualCoordinateRepresentation :
    Representation (ZMod p) (Field.absoluteGaloisGroup ℚ) (Fin 2 → ZMod p) :=
  coordinateRepresentation S.residualRepresentation S.residualBasis

/-- 行列の作用と実際のねじれ点のガロア作用の対応。 -/
theorem residualGL2_mulVec (σ : Field.absoluteGaloisGroup ℚ) (P : S.ResidualSpace) :
    (S.residualGL2 σ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ S.residualBasis.equivFun P =
      S.residualBasis.equivFun (S.residualRepresentation σ P) :=
  matrixGroupHom_mulVec S.residualRepresentation S.residualBasis σ P

/-- 基底を変更すると、同じ表現の行列は共役になる。 -/
theorem residualGL2_basis_change (b c : Basis (Fin 2) (ZMod p) S.ResidualSpace)
    (σ : Field.absoluteGaloisGroup ℚ) :
    S.residualGL2WithBasis c σ =
      basisChange b c * S.residualGL2WithBasis b σ * (basisChange b c)⁻¹ :=
  matrixGroupHom_basis_change S.residualRepresentation b c σ

/-- 行列化しても元の残余表現の核を保つ。 -/
theorem residualGL2_ker : S.residualGL2.ker = S.residualKernel :=
  matrixGroupHom_ker S.residualRepresentation S.residualBasis

/-- 行列表示の核はKrull位相で開く。 -/
theorem residualGL2_kernel_isOpen :
    IsOpen (S.residualGL2.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  have := S.rationalCurve_isElliptic
  rw [S.residualGL2_ker]
  exact S.residualKernel_isOpen

/-- 同じ有限正規中間体を固定する群は、行列表現にも恒等に作用する。 -/
theorem residualGL2_normal_finite_level :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ Normal ℚ L ∧
      L.fixingSubgroup ≤ S.residualGL2.ker := by
  have := S.rationalCurve_isElliptic
  rw [S.residualGL2_ker]
  exact exists_normal_finite_level S.rationalCurve p

/-- NOTE-017の判定基準。既存の二つの述語を変更せず、次元2だけで証明する。
安定直線の不存在を証明すれば既約性を得るが、その不存在はこの定理の結論ではない。 -/
theorem residual_isIrreducible_iff_no_stable_line :
    S.ResidualIsIrreducible ↔ ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L := by
  have := S.rationalCurve_isElliptic
  exact isIrreducible_iff_no_stable_line S.residualRepresentation S.residual_finrank_eq_two

/-- 座標表示で既約性を論じても、元のSourceの既約性と同じである。 -/
theorem residualCoordinate_isIrreducible_iff :
    DkMath.Lib.RepresentationTheory.IsIrreducible S.residualCoordinateRepresentation ↔
      S.ResidualIsIrreducible :=
  coordinate_isIrreducible_iff S.residualRepresentation S.residualBasis

/-- 行列式指標。円分指標との一致の証明はWeil対の算術へ残す。 -/
noncomputable def residualDeterminantCharacter : Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ :=
  determinantCharacterWithBasis S.residualRepresentation S.residualBasis

/-- 行列式指標の値を元の作用素の行列式と照合する。 -/
theorem residualDeterminantCharacter_val (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualDeterminantCharacter σ : ZMod p) = LinearMap.det (S.residualRepresentation σ) :=
  determinantCharacterWithBasis_val S.residualRepresentation S.residualBasis σ

/-- 同じSourceの二次元性・行列表示の忠実性・有限正規レベル・不変直線判定をまとめる。
GL₂準同型そのものはresidualGL2として構成済みであり、ここには追加仮定がない。 -/
theorem residual_gl2_profile :
    finrank (ZMod p) S.ResidualSpace = 2 ∧
      S.residualGL2.ker = S.residualKernel ∧
      (∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ Normal ℚ L ∧
        L.fixingSubgroup ≤ S.residualGL2.ker) ∧
      (S.ResidualIsIrreducible ↔ ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
        finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L) :=
  ⟨S.residual_finrank_eq_two, S.residualGL2_ker, S.residualGL2_normal_finite_level,
    S.residual_isIrreducible_iff_no_stable_line⟩

end DkMath.FLT.Frey.Source
