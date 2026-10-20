/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber
import DkMath.Lib.RepresentationTheory.MatrixRealization

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionGL2"

/-!
# 実際の楕円曲線のp-torsionからGL₂へ

標数0の楕円曲線について証明済みの次元公式から基底を選ぶ。
選択は非計算的だが、作用する点・ガロア群・線形作用素は既存のものと同じである。
座標化は忠実なので核を変えず、既存の開核・有限正規中間体をそのまま運べる。
二次元性のもう一つの用途は、既約性の障害を安定な直線だけに絞ることにある。
直線の不存在そのもの、Weil対、円分指標との一致はこの線形代数からは導かない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module
open scoped Matrix
open DkMath.Lib.RepresentationTheory
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime]

/-- 正則ファイバーによる次元定理から選ぶ実際のE[p]の基底。位数を仮定しない。 -/
noncomputable def torsionBasis : Basis (Fin 2) (ZMod p) (Torsion E p) :=
  Module.finBasisOfFinrankEq (ZMod p) (Torsion E p) (finrank_torsion_prime E p)

/-- 任意の基底で実際の座標ガロア作用をGL₂へ移す。 -/
noncomputable def torsionGL2WithBasis (b : Basis (Fin 2) (ZMod p) (Torsion E p)) :
    Field.absoluteGaloisGroup K →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  matrixGroupHom (representation E p) b

/-- 証明済みの二次元性で選んだ基底によるGL₂表現。 -/
noncomputable def torsionGL2 :
    Field.absoluteGaloisGroup K →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  torsionGL2WithBasis E p (torsionBasis E p)

/-- 列ベクトル上の線形表現。実際の点の表現と基底座標によって同変同型になる。 -/
noncomputable def torsionCoordinateRepresentation :
    Representation (ZMod p) (Field.absoluteGaloisGroup K) (Fin 2 → ZMod p) :=
  coordinateRepresentation (representation E p) (torsionBasis E p)

/-- GL₂行列を掛けることと、実際の点にガロア作用してから座標を取ることが一致する。 -/
theorem torsionGL2_mulVec (σ : Field.absoluteGaloisGroup K) (P : Torsion E p) :
    (torsionGL2 E p σ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ (torsionBasis E p).equivFun P =
      (torsionBasis E p).equivFun (representation E p σ P) :=
  matrixGroupHom_mulVec (representation E p) (torsionBasis E p) σ P

omit [CharZero K] [E.IsElliptic] in
/-- 基底変更はGL₂内の共役である。変更行列の向きも一般定理で固定される。 -/
theorem torsionGL2_basis_change (b c : Basis (Fin 2) (ZMod p) (Torsion E p))
    (σ : Field.absoluteGaloisGroup K) :
    torsionGL2WithBasis E p c σ =
      basisChange b c * torsionGL2WithBasis E p b σ * (basisChange b c)⁻¹ :=
  matrixGroupHom_basis_change (representation E p) b c σ

/-- GL₂表示の核は点への作用の核と等しい。 -/
theorem torsionGL2_ker : (torsionGL2 E p).ker = representationKernel E p :=
  matrixGroupHom_ker (representation E p) (torsionBasis E p)

/-- 行列化された表現も開核を持つ。有限torsionの既存の連続性を運ぶだけでよい。 -/
theorem torsionGL2_kernel_isOpen :
    IsOpen ((torsionGL2 E p).ker : Set (Field.absoluteGaloisGroup K)) := by
  rw [torsionGL2_ker]
  exact representationKernel_isOpen E p

/-- 同じ有限正規中間体を固定する群が、GL₂表現の核にも入る。 -/
theorem torsionGL2_normal_finite_level :
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧ Normal K L ∧
      L.fixingSubgroup ≤ (torsionGL2 E p).ker := by
  rw [torsionGL2_ker]
  exact exists_normal_finite_level E p

/-- 二次元性により、既存の既約性条件は安定直線の不存在に等しい。
これは判定基準の同値であって、任意の楕円曲線の既約性の主張ではない。 -/
theorem torsion_isIrreducible_iff_no_stable_line :
    IsIrreducible E p ↔ ¬ ∃ L : Submodule (ZMod p) (Torsion E p),
      finrank (ZMod p) L = 1 ∧ IsGaloisStable E p L :=
  isIrreducible_iff_no_stable_line (representation E p) (finrank_torsion_prime E p)

/-- 列ベクトル表示と点の表示の既約性は同値である。 -/
theorem torsionCoordinate_isIrreducible_iff :
    DkMath.Lib.RepresentationTheory.IsIrreducible (torsionCoordinateRepresentation E p) ↔
      IsIrreducible E p :=
  coordinate_isIrreducible_iff (representation E p) (torsionBasis E p)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
