/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.InvariantLine
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

#print "file: DkMath.Lib.RepresentationTheory.MatrixRealization"

/-!
# 同じ表現のGL行列による実現と、基底によらない不変量

群表現の各作用素は可逆である。選んだ基底で行列化しても可逆性を保つため、
単なる行列の列ではなくGLへの群準同型を構成できる。座標作用は元の作用と同変である。
基底bからcへの変更では、行列はc.toMatrix bによって共役変換される。
行列式・特性多項式・既約性・核は変わらない。行列式指標は定義するが、
円分指標との一致はWeil対などの別の算術的入力を必要とする。
-/
namespace DkMath.Lib.RepresentationTheory
open Module
open scoped Matrix
variable {k G V ι : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [Fintype ι] [DecidableEq ι]

/-- 同じ群作用の可逆な行列。任意の有限基底に対する一般のGL実現。 -/
noncomputable def matrixGroupHom (ρ : Representation k G V) (b : Basis ι k V) :
    G →* Matrix.GeneralLinearGroup ι k :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.asGroupHom

/-- GL元の中身は、元の線形作用素を同じ基底で行列化したものである。 -/
theorem matrixGroupHom_val (ρ : Representation k G V) (b : Basis ι k V) (g : G) :
    (matrixGroupHom ρ b g : Matrix ι ι k) = LinearMap.toMatrix b b (ρ g) := rfl

/-- 行列の列ベクトルへの作用は、元の作用を基底座標に移したものと一致する。 -/
theorem matrixGroupHom_mulVec (ρ : Representation k G V) (b : Basis ι k V) (g : G) (x : V) :
    (matrixGroupHom ρ b g : Matrix ι ι k) *ᵥ b.equivFun x = b.equivFun (ρ g x) := by
  simpa only [matrixGroupHom_val, Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr b b (ρ g) x

/-- 同じ表現の座標空間上での表示。基底の線形同型に沿って作用を運ぶ。 -/
noncomputable def coordinateRepresentation (ρ : Representation k G V) (b : Basis ι k V) :
    Representation k G (ι → k) := b.equivFun.conjRingEquiv.toMonoidHom.comp ρ

omit [DecidableEq ι] in
/-- 基底座標への線形同型は群作用と可換する。 -/
theorem coordinate_equivariant (ρ : Representation k G V) (b : Basis ι k V) (g : G) (x : V) :
    b.equivFun (ρ g x) = coordinateRepresentation ρ b g (b.equivFun x) := by
  change b.equivFun (ρ g x) = b.equivFun (ρ g (b.equivFun.symm (b.equivFun x)))
  rw [b.equivFun.symm_apply_apply]

/-- 座標表示の線形作用は、構成したGL行列のmulVecそのものである。 -/
theorem coordinate_apply_eq_mulVec (ρ : Representation k G V) (b : Basis ι k V) (g : G) (v : ι → k) :
    coordinateRepresentation ρ b g v = (matrixGroupHom ρ b g : Matrix ι ι k) *ᵥ v := by
  have h := matrixGroupHom_mulVec ρ b g (b.equivFun.symm v)
  have he := (coordinate_equivariant ρ b g (b.equivFun.symm v)).symm
  have he' : coordinateRepresentation ρ b g v =
      b.equivFun (ρ g (b.equivFun.symm v)) := by
    simpa only [b.equivFun.apply_symm_apply] using he
  exact he'.trans (by simpa only [b.equivFun.apply_symm_apply] using h.symm)

/-- 基底変更のGL行列。逆行列は逆向きの座標変換である。 -/
noncomputable def basisChange (b c : Basis ι k V) : Matrix.GeneralLinearGroup ι k where
  val := c.toMatrix b
  inv := b.toMatrix c
  val_inv := c.toMatrix_mul_toMatrix_flip b
  inv_val := b.toMatrix_mul_toMatrix_flip c

/-- 新しい基底での行列は、座標変換による共役になる。向きも式で固定する。 -/
theorem matrixGroupHom_basis_change (ρ : Representation k G V) (b c : Basis ι k V) (g : G) :
    matrixGroupHom ρ c g = basisChange b c * matrixGroupHom ρ b g * (basisChange b c)⁻¹ := by
  apply Units.ext
  change LinearMap.toMatrix c c (ρ g) = c.toMatrix b * LinearMap.toMatrix b b (ρ g) * b.toMatrix c
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c b c b (ρ g)).symm

/-- 行列化は忠実なので、作用が恒等となる群元、従って核は変わらない。 -/
theorem matrixGroupHom_ker (ρ : Representation k G V) (b : Basis ι k V) :
    (matrixGroupHom ρ b).ker = ρ.ker := by
  ext g
  change matrixGroupHom ρ b g = 1 ↔ ρ g = 1
  constructor
  · intro h
    have hv := congrArg (fun u : Matrix.GeneralLinearGroup ι k => (u : Matrix ι ι k)) h
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact hv.trans (map_one (LinearMap.toMatrixAlgEquiv b)).symm
  · intro h
    apply Units.ext
    change LinearMap.toMatrix b b (ρ g) = 1
    rw [h, LinearMap.toMatrix_one]

omit [DecidableEq ι] in
/-- 基底に沿った同変同型は既約性を保つ。既約性そのものは仮定せず同値を与える。 -/
theorem coordinate_isIrreducible_iff (ρ : Representation k G V) (b : Basis ι k V) :
    IsIrreducible (coordinateRepresentation ρ b) ↔ IsIrreducible ρ :=
  (isIrreducible_iff ρ (coordinateRepresentation ρ b) b.equivFun (coordinate_equivariant ρ b)).symm

omit [DecidableEq ι] in
/-- 基底を二通りに選んだ座標表示の既約性は同値である。 -/
theorem coordinate_isIrreducible_basis_independent (ρ : Representation k G V) (b c : Basis ι k V) :
    IsIrreducible (coordinateRepresentation ρ b) ↔ IsIrreducible (coordinateRepresentation ρ c) :=
  (coordinate_isIrreducible_iff ρ b).trans (coordinate_isIrreducible_iff ρ c).symm

/-- 行列式は基底によらない元の作用素の行列式である。 -/
theorem matrixGroupHom_det (ρ : Representation k G V) (b : Basis ι k V) (g : G) :
    (matrixGroupHom ρ b g : Matrix ι ι k).det = LinearMap.det (ρ g) := by
  rw [matrixGroupHom_val, LinearMap.det_toMatrix]

/-- 行列式の基底不変性。円分指標との一致は結論しない。 -/
theorem matrixGroupHom_det_basis_independent (ρ : Representation k G V) (b c : Basis ι k V) (g : G) :
    (matrixGroupHom ρ b g : Matrix ι ι k).det = (matrixGroupHom ρ c g : Matrix ι ι k).det := by
  rw [matrixGroupHom_det, matrixGroupHom_det]

/-- 可逆行列の行列式を取って得る乗法的指標。円分指標との比較は別問題である。 -/
noncomputable def determinantCharacterWithBasis (ρ : Representation k G V) (b : Basis ι k V) :
    G →* kˣ := Matrix.GeneralLinearGroup.det.comp (matrixGroupHom ρ b)

/-- 行列式指標の値は元の作用素の行列式である。 -/
theorem determinantCharacterWithBasis_val (ρ : Representation k G V) (b : Basis ι k V) (g : G) :
    (determinantCharacterWithBasis ρ b g : k) = LinearMap.det (ρ g) := by
  exact matrixGroupHom_det ρ b g

/-- 行列式指標全体も基底の選択に依存しない。 -/
theorem determinantCharacterWithBasis_independent (ρ : Representation k G V) (b c : Basis ι k V) :
    determinantCharacterWithBasis ρ b = determinantCharacterWithBasis ρ c := by
  ext g
  exact (determinantCharacterWithBasis_val ρ b g).trans
    (determinantCharacterWithBasis_val ρ c g).symm

variable [FiniteDimensional k V]

/-- 特性多項式も基底によらない元の作用素の特性多項式に一致する。 -/
theorem matrixGroupHom_charpoly (ρ : Representation k G V) (b : Basis ι k V) (g : G) :
    (matrixGroupHom ρ b g : Matrix ι ι k).charpoly = (ρ g).charpoly := by
  rw [matrixGroupHom_val, LinearMap.charpoly_toMatrix]

/-- 基底変更による特性多項式の不変性。 -/
theorem matrixGroupHom_charpoly_basis_independent (ρ : Representation k G V) (b c : Basis ι k V) (g : G) :
    (matrixGroupHom ρ b g : Matrix ι ι k).charpoly = (matrixGroupHom ρ c g : Matrix ι ι k).charpoly := by
  rw [matrixGroupHom_charpoly, matrixGroupHom_charpoly]

end DkMath.Lib.RepresentationTheory
