/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_FunctionFieldPullback.lean.
Upstream blob: ce8783a9e9613db1c4c0323ce93fb0d89917ee65
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationFunctionDegree
import DkMath.Lib.NumberTheory.EllipticWeilTransport

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationValuation"

/-!
# 倍写像の引き戻しと有限場所の付値上界

xだけでなくy=ω/ψ³の有理式をJacobian表示から供給する。
Pと[n]Pがともに有限点なら分母はPで非零なので、一般座標の合同をこれらの有理式へ輸送できる。
既存のpointPullに対するイデアル冪の補題に渡し、局所付値の上界を保持する。
ここでは分岐指数1や付値の完全一致を仮定せず、後続の一重零点の降下に必要な不等式を証明する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open Polynomial WeierstrassCurve WeierstrassCurve.Affine

/-- 非零n倍点のy座標は同じ除法多項式からωₙ/ψₙ³で与えられる。 -/
theorem nsmul_y_formula {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) (n : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hnP : n • (Point.some x y h) ≠ 0) :
    (n • (Point.some x y h)).yc =
      (EllipticDivision.WeierstrassCurve.ωe W (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 3 := by
  have hψ : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := by
    intro hz
    have he := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ W h (n : ℤ)).mpr hz
    rw [natCast_zsmul] at he
    exact hnP he
  have key := EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval W h (n : ℤ)
  let V := EllipticDivision.WeierstrassCurve.smulEval W x y (n : ℤ)
  have hvz : V 2 ≠ 0 := hψ
  have hv := key ▸ ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have he : ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x y h)) = Jacobian.Point.mk hv :=
    Jacobian.Point.ext key
  have hp : n • (Point.some x y h) = Point.some (V 0 / V 2 ^ 2) (V 1 / V 2 ^ 3)
      ((Jacobian.nonsingular_of_Z_ne_zero hvz).mp hv) := by
    calc n • (Point.some x y h)
        = Jacobian.Point.toAffineAddEquiv W ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply, natCast_zsmul]
      _ = _ := by
        rw [he, Jacobian.Point.toAffineAddEquiv_apply]
        exact Jacobian.Point.toAffineLift_of_Z_ne_zero hvz
  rw [hp, Point.yc_some]
  rfl

end DkMath.Lib.NumberTheory.EllipticFunctionField

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticMultiplicationValuation : DecidableEq (AlgebraicClosure K) := Classical.decEq _
attribute [local instance] geometricCoordinateRing_isDedekindDomain

/-- [n]Pが有限点であれば、引き戻しは有限場所の各イデアル冪の付値上界を保つ。
原像の有限性・非零指数・分母の非零性を証明し、局所条件を仮定として残さない。 -/
theorem valuation_multiplicationPull_le (n : ℕ) (hn : n ≠ 0)
    (P : (E⁄(AlgebraicClosure K)).Point) (hP : P ≠ 0) (hnP : n • P ≠ 0)
    (h : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (k : ℕ)
    (hh : (placeOf E (AlgebraicClosure K) (n • P) hnP).valuation _ h ≤ exp (-(k : ℤ))) :
    (placeOf E (AlgebraicClosure K) P hP).valuation _ (multiplicationPull E n hn h) ≤ exp (-(k : ℤ)) := by
  classical
  let L := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure K) L).injective
  let W := E.baseChange (AlgebraicClosure K)
  let Φ := W.Φ (n : ℤ)
  let Ψ := W.ΨSq (n : ℤ)
  let ω := EllipticDivision.WeierstrassCurve.ωe W (n : ℤ)
  let ψ := W.ψ (n : ℤ)
  let gX := genericX E (AlgebraicClosure K)
  let gY := genericY E (AlgebraicClosure K)
  let f := IsScalarTower.toAlgHom K (AlgebraicClosure K) L
  have hφ : (E⁄L).Φ (n : ℤ) = Φ.map (algebraMap (AlgebraicClosure K) L) := E.baseChange_Φ f _
  have hΨ : (E⁄L).ΨSq (n : ℤ) = Ψ.map (algebraMap (AlgebraicClosure K) L) := E.baseChange_ΨSq f _
  have hψ : (E⁄L).ψ (n : ℤ) = ψ.map (mapRingHom (algebraMap (AlgebraicClosure K) L)) := E.baseChange_ψ f _
  have hω : EllipticDivision.WeierstrassCurve.ωe (E.baseChange L) (n : ℤ) =
      ω.map (mapRingHom (algebraMap (AlgebraicClosure K) L)) := by
    rw [← EllipticDivision.WeierstrassCurve.map_ωe]
    exact congrArg (fun V => EllipticDivision.WeierstrassCurve.ωe V (n : ℤ)) (WeierstrassCurve.map_baseChange E f).symm
  have hξ : (n • genericPoint E (AlgebraicClosure K)).xc =
      Φ.eval₂ (algebraMap (AlgebraicClosure K) L) gX / Ψ.eval₂ (algebraMap (AlgebraicClosure K) L) gX := by
    rw [← eval_map, ← eval_map, ← hφ, ← hΨ]
    exact nsmul_x_formula (E.baseChange L) n (generic_nonsingular E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn)
  have hη : (n • genericPoint E (AlgebraicClosure K)).yc =
      ω.eval₂ (eval₂RingHom (algebraMap (AlgebraicClosure K) L) gX) gY /
        ψ.eval₂ (eval₂RingHom (algebraMap (AlgebraicClosure K) L) gX) gY ^ 3 := by
    have hy := nsmul_y_formula (E.baseChange L) n (generic_nonsingular E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn)
    rw [hω, hψ, ← eval₂_eval₂RingHom_apply, ← eval₂_eval₂RingHom_apply] at hy
    exact hy
  have hP' : n • Point.some P.xc P.yc (Point.nonsingular_xc_yc hP) ≠ 0 := by
    rwa [← Point.eq_some_xc_yc hP]
  have hxP : (n • P).xc = Φ.eval P.xc / Ψ.eval P.xc := by
    conv_lhs => rw [Point.eq_some_xc_yc hP]
    exact nsmul_x_formula W n (Point.nonsingular_xc_yc hP) hP'
  have hyP : (n • P).yc = ω.evalEval P.xc P.yc / ψ.evalEval P.xc P.yc ^ 3 := by
    conv_lhs => rw [Point.eq_some_xc_yc hP]
    exact nsmul_y_formula W n (Point.nonsingular_xc_yc hP) hP'
  have hψ0 : ψ.evalEval P.xc P.yc ≠ 0 := by
    intro hz
    have he := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ W (Point.nonsingular_xc_yc hP) (n : ℤ)).mpr hz
    rw [natCast_zsmul] at he
    exact hP' he
  have hΨ0 : Ψ.eval P.xc ≠ 0 := by
    rw [← EllipticDivision.WeierstrassCurve.evalEval_ψ_sq W (Point.nonsingular_xc_yc hP).1]
    exact pow_ne_zero 2 hψ0
  let v := (placeOf E (AlgebraicClosure K) P hP).valuation L
  have hc1 := valuation_algebraMap_le_one E (AlgebraicClosure K) P hP
  have hX := cong_genericX E (AlgebraicClosure K) P hP
  have hY := cong_genericY E (AlgebraicClosure K) P hP
  have hx : v.Cong (n • genericPoint E (AlgebraicClosure K)).xc (algebraMap (AlgebraicClosure K) L (n • P).xc) := by
    rw [hξ, hxP, map_div₀, ← eval₂_at_apply, ← eval₂_at_apply]
    have hcΦ := Valuation.Cong.eval₂ (v := v) (algebraMap (AlgebraicClosure K) L) hc1 hX (hc1 _) Φ
    have hcΨ := Valuation.Cong.eval₂ (v := v) (algebraMap (AlgebraicClosure K) L) hc1 hX (hc1 _) Ψ
    refine hcΦ.1.div hcΨ.1 hcΦ.2 ?_
    rw [eval₂_at_apply]
    exact valuation_algebraMap_eq_one E (AlgebraicClosure K) P hP hΨ0
  have hy : v.Cong (n • genericPoint E (AlgebraicClosure K)).yc (algebraMap (AlgebraicClosure K) L (n • P).yc) := by
    rw [hη, hyP, map_div₀, map_pow, algebraMap_evalEval, algebraMap_evalEval]
    have hcω := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap (AlgebraicClosure K) L) hc1 hX (hc1 _) hY (hc1 _) ω
    have hcψ := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap (AlgebraicClosure K) L) hc1 hX (hc1 _) hY (hc1 _) ψ
    refine hcω.1.div (hcψ.1.pow hcψ.2 3) hcω.2 ?_
    rw [← algebraMap_evalEval, ← map_pow]
    exact valuation_algebraMap_eq_one E (AlgebraicClosure K) P hP (pow_ne_zero 3 hψ0)
  exact valuation_pointPull_le E (AlgebraicClosure K) _ _ _ hP hnP hx hy h k hh

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
