/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Proof inspired by anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv.lean.
Upstream blob: 4542e0df895bf2fecf64a96a630035070ddc12b6
Reconstructed for DkMath: concrete equivariance, equality transport and rational base-change formulas.
-/

import DkMath.Lib.NumberTheory.WeierstrassVariableChangeHom
import DkMath.Lib.NumberTheory.EllipticFixedTorsion

#print "file: DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois"

/-!
# 元の体で定義された変数変換の、幾何学的点と有理点の整合

[DkMath.Lib] 変数変換Cを係数体の代数閉包へ写し、同じ座標変換の加法同型を構成する。
Cの四つの係数は元の体の元なので、絶対Galois作用で固定される。
座標の多項式公式から、同型とGalois作用の可換性および有理点の基底変換との可換性を証明する。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVariableChange
open WeierstrassCurve WeierstrassCurve.Affine EllipticTorsionRepresentation
noncomputable local instance instDecidableEqWeierstrassVariableChangeGalois {α : Type*} :
    DecidableEq α := Classical.decEq _
variable {K : Type*} [Field K]

/-- [DkMath.Lib] モデルの等式による点群の加法同型。座標値は変えない。 -/
noncomputable def pointEquivOfModelEq [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V) :
    W.toAffine.Point ≃+ V.toAffine.Point := by
  subst V
  exact AddEquiv.refl _

/-- [DkMath.Lib] 同じモデルの等式による点の輸送は、有限点の二座標を保持する。 -/
theorem pointEquivOfModelEq_some [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V) {x y : K}
    (hxy : W.toAffine.Nonsingular x y) :
    pointEquivOfModelEq h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst V
  rfl

/-- [DkMath.Lib] モデルの等式による幾何学的点の輸送はGalois作用と可換。 -/
theorem pointEquivOfModelEq_equivariant {W V : WeierstrassCurve K} (h : W = V)
    (σ : Field.absoluteGaloisGroup K) (P : Points W) :
    pointEquivOfModelEq (congrArg (fun E => E.map (algebraMap K (AlgebraicClosure K))) h)
        (pointAction W σ P) =
      pointAction V σ
        (pointEquivOfModelEq (congrArg (fun E => E.map (algebraMap K (AlgebraicClosure K))) h) P) := by
  subst V
  rfl

/-- [DkMath.Lib] モデルの等式による輸送は、有理点の基底変換とも可換。 -/
theorem pointEquivOfModelEq_baseChange [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V)
    (P : W.toAffine.Point) :
    pointEquivOfModelEq (congrArg (fun E => E.map (algebraMap K (AlgebraicClosure K))) h)
        (baseChangePoint W P) = baseChangePoint V (pointEquivOfModelEq h P) := by
  subst V
  rfl

/-- [DkMath.Lib] 元の体の変数変換を代数閉包へ延ばした、同じ幾何学的点の加法同型。 -/
noncomputable def geometricChangeEquiv (W : WeierstrassCurve K) (C : VariableChange K) :
    Points (C • W) ≃+ Points W :=
  (pointEquivOfModelEq (map_variableChange W C (algebraMap K (AlgebraicClosure K))).symm).trans
    (variableChangeAddEquiv (C.map (algebraMap K (AlgebraicClosure K)))
      (W.map (algebraMap K (AlgebraicClosure K))))

/-- [DkMath.Lib] 幾何学的同型は、元の体から写した同じu,r,s,tによる有限座標を持つ。 -/
theorem geometricChangeEquiv_some (W : WeierstrassCurve K) (C : VariableChange K)
    {x y : AlgebraicClosure K} (hxy : ((C • W).toAffine⁄(AlgebraicClosure K)).Nonsingular x y) :
    ∃ h, geometricChangeEquiv W C (.some x y hxy) =
      .some (vcX (C.map (algebraMap K (AlgebraicClosure K))) x)
        (vcY (C.map (algebraMap K (AlgebraicClosure K))) x y) h := by
  let Cbar := C.map (algebraMap K (AlgebraicClosure K))
  let Wbar := W.map (algebraMap K (AlgebraicClosure K))
  have heq : Cbar • Wbar = (C • W).map (algebraMap K (AlgebraicClosure K)) :=
    map_variableChange W C _
  let h' : (Cbar • Wbar).toAffine.Nonsingular x y := heq.symm ▸ hxy
  refine ⟨(nonsingular_variableChange_iff (C := Cbar) (W := Wbar) x y).mp h', ?_⟩
  change variableChangeAddEquiv Cbar Wbar (pointEquivOfModelEq heq.symm (.some x y hxy)) = _
  exact congrArg (variableChangeAddEquiv Cbar Wbar) (pointEquivOfModelEq_some heq.symm hxy)

/-- [DkMath.Lib] 同じ幾何学的点の変数変換は、標準の絶対Galois作用と可換。 -/
theorem geometricChangeEquiv_equivariant (W : WeierstrassCurve K) (C : VariableChange K)
    (σ : Field.absoluteGaloisGroup K) (P : Points (C • W)) :
    geometricChangeEquiv W C (pointAction (C • W) σ P) = pointAction W σ (geometricChangeEquiv W C P) := by
  cases P with
  | zero =>
    change geometricChangeEquiv W C ((pointAction (C • W) σ) 0) =
      pointAction W σ (geometricChangeEquiv W C 0)
    rw [map_zero, map_zero, map_zero]
  | some x y hxy =>
    obtain ⟨h, he⟩ := geometricChangeEquiv_some W C hxy
    have hm := Point.map_some (f := σ.toAlgHom) hxy
    obtain ⟨h', he'⟩ := geometricChangeEquiv_some W C
      (((C • W).toAffine.baseChange_nonsingular (f := σ.toAlgHom) σ.toAlgHom.injective x y).mpr hxy)
    change geometricChangeEquiv W C (Point.map σ.toAlgHom (.some x y hxy)) = _
    rw [hm, he', he]
    change Point.some _ _ _ = Point.map σ.toAlgHom (Point.some _ _ _)
    rw [Point.map_some]
    have hfix (c : K) : σ.toAlgHom (algebraMap K (AlgebraicClosure K) c) =
        algebraMap K (AlgebraicClosure K) c := σ.toAlgHom.commutes c
    congr 1 <;> simp only [vcX, vcY, VariableChange.map, Units.coe_map, MonoidHom.coe_coe,
      map_add, map_mul, map_pow] <;> simp only [hfix]

/-- [DkMath.Lib] 逆方向の幾何学的変数変換も、同じ絶対Galois作用と可換。 -/
theorem geometricChangeEquiv_symm_equivariant (W : WeierstrassCurve K) (C : VariableChange K)
    (σ : Field.absoluteGaloisGroup K) (P : Points W) :
    (geometricChangeEquiv W C).symm (pointAction W σ P) =
      pointAction (C • W) σ ((geometricChangeEquiv W C).symm P) := by
  apply (geometricChangeEquiv W C).injective
  rw [(geometricChangeEquiv W C).apply_symm_apply, geometricChangeEquiv_equivariant,
    (geometricChangeEquiv W C).apply_symm_apply]

/-- [DkMath.Lib] 元の体の有理点の変数変換と、代数閉包への基底変換は可換。 -/
theorem geometricChangeEquiv_baseChange (W : WeierstrassCurve K) (C : VariableChange K)
    (P : (C • W).toAffine.Point) :
    geometricChangeEquiv W C (baseChangePoint (C • W) P) =
      baseChangePoint W (variableChangeAddEquiv C W P) := by
  cases P with
  | zero => exact (geometricChangeEquiv W C).map_zero
  | some x y hxy =>
    obtain ⟨h, he⟩ := geometricChangeEquiv_some W C (((C • W).toAffine.baseChange_nonsingular
      (f := Algebra.ofId K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective x y).mpr hxy)
    change geometricChangeEquiv W C (Point.some _ _ _) = _
    rw [he]
    change Point.some _ _ _ = Point.some _ _ _
    congr 1 <;> simp only [vcX, vcY, VariableChange.map, Units.coe_map, MonoidHom.coe_coe,
      map_add, map_mul, map_pow] <;> rfl

end DkMath.Lib.NumberTheory.WeierstrassVariableChange
