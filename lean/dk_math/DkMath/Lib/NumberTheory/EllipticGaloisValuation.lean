/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.lean.
Upstream blob: 98fe0128d5c2a913dd127b273fb542d7d5102761
Modified for DkMath: use constructed canonical lifts and actual Point.map, not extension assumptions.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldGalois
import DkMath.Lib.NumberTheory.EllipticWeilValuation
import DkMath.Lib.Algebra.DedekindValuationEquiv

#print "file: DkMath.Lib.NumberTheory.EllipticGaloisValuation"

/-!
# ガロア作用による有限場所の輸送

座標環の同型は点イデアルm(P)をm(σP)へ写す。素イデアルの冪への所属と
分数体への包含を比較し、正規化された付値そのものの一致を証明する。
絶対ガロア作用との接続は既存のpointActionを使い、別の点作用を導入しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  (W : WeierstrassCurve F) (σ : K ≃ₐ[F] K)

/-- 係数作用で写した点のx座標は、元のx座標への係数自己同型の値である。 -/
theorem galPoint_xc (P : (W⁄K).Point) : (Point.map (W' := W) σ.toAlgHom P).xc = σ P.xc :=
  point_xc_map σ.toAlgHom P

/-- y座標も同じ係数自己同型で写る。Oでの便宜的座標0とも整合する。 -/
theorem galPoint_yc (P : (W⁄K).Point) : (Point.map (W' := W) σ.toAlgHom P).yc = σ P.yc :=
  point_yc_map σ.toAlgHom P

/-- 点の係数作用は単射で、O以外の点をOへ潰さない。 -/
theorem galPoint_ne_zero {P : (W⁄K).Point} (hP : P ≠ 0) : Point.map (W' := W) σ.toAlgHom P ≠ 0 := by
  intro h
  apply hP
  apply Point.map_injective σ.toAlgHom
  simpa only [map_zero] using h

/-- 有限場所のガロア輸送。全ての有理関数に成立し、零関数も許す。 -/
theorem valuation_galFunctionFieldEquiv [IsDedekindDomain (W⁄K).CoordinateRing]
    {P : (W⁄K).Point} (hP : P ≠ 0) (hσP : Point.map (W' := W) σ.toAlgHom P ≠ 0)
    (f : (W⁄K).FunctionField) :
    (placeOf W K (Point.map (W' := W) σ.toAlgHom P) hσP).valuation (W⁄K).FunctionField
      (galFunctionFieldEquiv W σ f) = (placeOf W K P hP).valuation (W⁄K).FunctionField f := by
  have hv : (placeOf W K (Point.map (W' := W) σ.toAlgHom P) hσP).comap
      (galRingEquiv W σ).toRingHom (galRingEquiv W σ).surjective = placeOf W K P hP := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change (placeOf W K (Point.map (W' := W) σ.toAlgHom P) hσP).asIdeal.comap
      (galRingEquiv W σ).toRingHom = (placeOf W K P hP).asIdeal
    rw [placeOf_asIdeal, placeOf_asIdeal,
      galPoint_xc, galPoint_yc, ← galRing_map_XYIdeal W σ (galRingEquiv W σ).toRingHom
        (galRingEquiv_mk W σ)]
    exact Ideal.comap_map_of_bijective _ (galRingEquiv W σ).bijective
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_comap_ringEquiv (galRingEquiv W σ)
    (galFunctionFieldEquiv W σ).toRingHom (galFunctionFieldEquiv_algebraMap W σ) _ f).trans
    (congrArg (fun v : IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing =>
      v.valuation (W⁄K).FunctionField f) hv)
end DkMath.Lib.NumberTheory.EllipticFunctionField

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
attribute [local instance] geometricCoordinateRing_isDedekindDomain

omit [E.IsElliptic] in
/-- 既存の座標ガロア作用も非零点を保つ。 -/
theorem pointAction_ne_zero (σ : Field.absoluteGaloisGroup K) {P : Points E} (hP : P ≠ 0) :
    pointAction E σ P ≠ 0 := by
  classical
  exact galPoint_ne_zero E σ hP

omit [E.IsElliptic] in
/-- 既存の点作用は単射であり、点の等号を反映する。 -/
theorem pointAction_injective (σ : Field.absoluteGaloisGroup K) : Function.Injective (pointAction E σ) := by
  classical
  exact Point.map_injective σ.toAlgHom

/-- 既存の点作用と、新しい半線形関数体作用の有限点付値の整合性。 -/
theorem finitePointValuation_galois (σ : Field.absoluteGaloisGroup K) (P : Points E) (hP : P ≠ 0)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    finitePointValuation E (pointAction E σ P) (pointAction_ne_zero E σ hP)
      (galFunctionFieldEquiv E σ f) = finitePointValuation E P hP f := by
  classical
  exact valuation_galFunctionFieldEquiv E σ hP (pointAction_ne_zero E σ hP) f

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
