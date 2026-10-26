/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
import DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois

#print "file: DkMath.Lib.NumberTheory.WeierstrassIntegralModelTransport"

/-!
# 同じ整数モデルへの有理点・幾何学的点・捩れ点の輸送

[DkMath.Lib] 整数化した係数をℚへ戻した曲線と元の曲線は、構成済みの同じ変数変換で結ぶ。
有理点の加法同型と幾何学的点のGalois同変な加法同型を構成し、基底変換との整合を証明する。
これにより、同じ点関数を整数モデルへ移した後も、元の像との対応を保持できる。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
open WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassVariableChange EllipticTorsionRepresentation
noncomputable local instance instDecidableEqWeierstrassIntegralModelTransport {α : Type*} :
    DecidableEq α := Classical.decEq _

/-- [DkMath.Lib] 構成したℤモデルを、同じ有理点を論じるためℚへ戻した曲線。 -/
def rationalModel (W : WeierstrassCurve ℚ) : WeierstrassCurve ℚ :=
  (integerModel W).map (Int.castRingHom ℚ)

/-- [DkMath.Lib] 同じ整数化モデルの有理点と元の有理点の加法同型。 -/
noncomputable def rationalPointEquiv (W : WeierstrassCurve ℚ) :
    (rationalModel W).toAffine.Point ≃+ W.toAffine.Point :=
  (pointEquivOfModelEq (integerModel_map W)).trans (variableChangeAddEquiv (clearingChange W) W)

/-- [DkMath.Lib] 同じ有理点の同型は、有限点で明示的な変数変換座標を持つ。 -/
theorem rationalPointEquiv_some (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hxy : (rationalModel W).toAffine.Nonsingular x y) :
    ∃ h, rationalPointEquiv W (.some x y hxy) =
      .some (vcX (clearingChange W) x) (vcY (clearingChange W) x y) h := by
  let h' : (clearingChange W • W).toAffine.Nonsingular x y := integerModel_map W ▸ hxy
  refine ⟨(nonsingular_variableChange_iff (C := clearingChange W) (W := W) x y).mp h', ?_⟩
  exact congrArg (variableChangeAddEquiv (clearingChange W) W)
    (pointEquivOfModelEq_some (integerModel_map W) hxy)

/-- [DkMath.Lib] 同じ整数化モデルの幾何学的点と元の幾何学的点の加法同型。 -/
noncomputable def geometricPointEquiv (W : WeierstrassCurve ℚ) :
    Points (rationalModel W) ≃+ Points W :=
  (pointEquivOfModelEq (congrArg (fun E : WeierstrassCurve ℚ => E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
    (integerModel_map W))).trans (geometricChangeEquiv W (clearingChange W))

/-- [DkMath.Lib] 同じ整数化モデルの幾何学的同型は、標準Galois作用と可換。 -/
theorem geometricPointEquiv_equivariant (W : WeierstrassCurve ℚ)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points (rationalModel W)) :
    geometricPointEquiv W (pointAction (rationalModel W) σ P) =
      pointAction W σ (geometricPointEquiv W P) :=
  (congrArg (geometricChangeEquiv W (clearingChange W))
    (pointEquivOfModelEq_equivariant (integerModel_map W) σ P)).trans
    (geometricChangeEquiv_equivariant W (clearingChange W) σ _)

/-- [DkMath.Lib] 元から整数化モデルへ送る逆同型もGalois同変。 -/
theorem geometricPointEquiv_symm_equivariant (W : WeierstrassCurve ℚ)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points W) :
    (geometricPointEquiv W).symm (pointAction W σ P) =
      pointAction (rationalModel W) σ ((geometricPointEquiv W).symm P) := by
  apply (geometricPointEquiv W).injective
  rw [(geometricPointEquiv W).apply_symm_apply, geometricPointEquiv_equivariant,
    (geometricPointEquiv W).apply_symm_apply]

/-- [DkMath.Lib] 同じ有理点の同型と幾何学的同型は、基底変換で正確に一致する。 -/
theorem geometricPointEquiv_baseChange (W : WeierstrassCurve ℚ)
    (P : (rationalModel W).toAffine.Point) :
    geometricPointEquiv W (baseChangePoint (rationalModel W) P) =
      baseChangePoint W (rationalPointEquiv W P) :=
  (congrArg (geometricChangeEquiv W (clearingChange W))
    (pointEquivOfModelEq_baseChange (integerModel_map W) P)).trans
    (geometricChangeEquiv_baseChange W (clearingChange W) _)

/-- [DkMath.Lib] 逆方向でも、元の有理点を同じ整数化モデルへ送る基底変換が可換。 -/
theorem geometricPointEquiv_symm_baseChange (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    (geometricPointEquiv W).symm (baseChangePoint W P) =
      baseChangePoint (rationalModel W) ((rationalPointEquiv W).symm P) := by
  apply (geometricPointEquiv W).injective
  rw [(geometricPointEquiv W).apply_symm_apply, geometricPointEquiv_baseChange,
    (rationalPointEquiv W).apply_symm_apply]

/-- [DkMath.Lib] 実際の非零有理n捩れ点は、同じ整数化モデルの非零有理n捩れ点へ運べる。
像が元の同じ点に戻ることも保持する。最小性や局所還元を仮定しない。 -/
theorem exists_nonzero_torsion_on_integerModel (W : WeierstrassCurve ℚ) (n : ℕ)
    (P : W.toAffine.Point) (hPn : n • P = 0) (hP : P ≠ 0) :
    ∃ Q : (rationalModel W).toAffine.Point,
      n • Q = 0 ∧ Q ≠ 0 ∧ rationalPointEquiv W Q = P := by
  refine ⟨(rationalPointEquiv W).symm P, ?_, ?_, (rationalPointEquiv W).apply_symm_apply P⟩
  · rw [← map_nsmul, hPn, map_zero]
  · intro hz
    apply hP
    exact ((rationalPointEquiv W).apply_symm_apply P).symm.trans
      ((congrArg (rationalPointEquiv W) hz).trans (map_zero _))

end DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
