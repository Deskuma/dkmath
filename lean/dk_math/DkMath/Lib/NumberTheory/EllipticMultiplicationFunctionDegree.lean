/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean.
Upstream blob: 346a32fb08ba430a7125a16d9c7b96c9608ea417
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationPullback
import DkMath.Lib.NumberTheory.EllipticFunctionFieldGenerators
import DkMath.Lib.Algebra.QuadraticInvolutionDegree

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationFunctionDegree"

/-!
# 倍写像による関数体拡大の次数上界n²

x座標の除法多項式だけでは、yを加える際の余分な2が残る。
反転はxを固定するが、n倍点のyは固定しない。もし固定すればその点は2-torsionとなり、
一般点の2n倍が零になる。既存の非定数性がこれを排除するため、yは既に像の体とxで生成される。
二次反転の一般補題により、関数体全体の次数はxの方程式の次数n²以下となる。
-/
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
open Polynomial WeierstrassCurve WeierstrassCurve.Affine

/-- 非零n倍点のx座標はΦₙ/ΨSqₙで与えられる。
Jacobianの実際の倍写像を使うため、曲線点と有理式の対応を仮定しない。 -/
theorem nsmul_x_formula {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) (n : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hnP : n • (Point.some x y h) ≠ 0) :
    (n • (Point.some x y h)).xc = (W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x := by
  have hψ : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := by
    intro hz
    have he := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ W h (n : ℤ)).mpr hz
    rw [natCast_zsmul] at he
    exact hnP he
  have hs := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq W h.1 (n : ℤ)
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
  rw [hp, Point.xc_some]
  change (W.φ (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 2 = _
  rw [hs, EllipticDivision.WeierstrassCurve.evalEval_φ W h.1]

end DkMath.Lib.NumberTheory.EllipticFunctionField

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticMultiplicationFunctionDegree : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- 反転はn倍一般点のyを固定しない。固定すれば一般点の2n倍が零になってしまう。 -/
theorem negEquiv_multiplicationPull_genericY_ne (n : ℕ) (hn : n ≠ 0) :
    negEquiv E (AlgebraicClosure K) (multiplicationPull E n hn (genericY E (AlgebraicClosure K))) ≠
      multiplicationPull E n hn (genericY E (AlgebraicClosure K)) := by
  intro heq
  rw [negEquiv_multiplicationPull_genericY, multiplicationPull_genericY] at heq
  have hP := Point.eq_some_xc_yc (generic_nsmul_ne_zero E n hn)
  have h2 : (2 : ℕ) • (n • genericPoint E (AlgebraicClosure K)) = 0 := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg]
    conv_rhs => rw [hP, Point.neg_some]
    conv_lhs => rw [hP]
    congr 1
    exact heq.symm
  apply generic_nsmul_ne_zero E (2 * n) (Nat.mul_ne_zero (by decide) hn)
  rwa [mul_smul]

/-- 028-Aの次数定理。実際の引き戻しの像を基礎体とする有限次元性と上界n²。
点数n²の公式を次数上界の仮定に使わず、反転と除法多項式から独立に供給する。 -/
theorem finiteDimensional_finrank_multiplicationPull (n : ℕ) (hn : n ≠ 0) :
    FiniteDimensional (multiplicationPull E n hn).fieldRange (E.toAffine⁄(AlgebraicClosure K)).FunctionField ∧
      Module.finrank (multiplicationPull E n hn).fieldRange (E.toAffine⁄(AlgebraicClosure K)).FunctionField ≤ n ^ 2 := by
  classical
  let L := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure K) L).injective
  let gX := genericX E (AlgebraicClosure K)
  let gY := genericY E (AlgebraicClosure K)
  let A : L := (E⁄L).a₁ * gX + (E⁄L).a₃
  let B : L := -(gX ^ 3 + (E⁄L).a₂ * gX ^ 2 + (E⁄L).a₄ * gX + (E⁄L).a₆)
  have hcoef : ∀ a : K, algebraMap K L a ∈ (AlgebraicClosure K)⟮gX⟯ := fun a => by
    rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K) L]
    exact IntermediateField.algebraMap_mem _ _
  have hXKX : gX ∈ (AlgebraicClosure K)⟮gX⟯ := mem_adjoin_simple_self _ _
  have hAmem : A ∈ (AlgebraicClosure K)⟮gX⟯ :=
    add_mem (mul_mem (hcoef E.a₁) hXKX) (hcoef E.a₃)
  have hBmem : B ∈ (AlgebraicClosure K)⟮gX⟯ :=
    neg_mem (add_mem (add_mem (add_mem (pow_mem hXKX 3) (mul_mem (hcoef E.a₂) (pow_mem hXKX 2)))
      (mul_mem (hcoef E.a₄) hXKX)) (hcoef E.a₆))
  have hYq : gY ^ 2 + A * gY + B = 0 := by
    have h := (equation_iff _ _).mp (generic_equation E (AlgebraicClosure K))
    change gY ^ 2 + ((E⁄L).a₁ * gX + (E⁄L).a₃) * gY -
      (gX ^ 3 + (E⁄L).a₂ * gX ^ 2 + (E⁄L).a₄ * gX + (E⁄L).a₆) = 0
    linear_combination h
  have hιX : (negEquiv E (AlgebraicClosure K) : L →ₐ[AlgebraicClosure K] L) gX = gX :=
    negEquiv_genericX E (AlgebraicClosure K)
  have hιY' : (negEquiv E (AlgebraicClosure K) : L →ₐ[AlgebraicClosure K] L) gY = -gY - A := by
    change negEquiv E (AlgebraicClosure K) (genericY E (AlgebraicClosure K)) = -gY - A
    rw [negEquiv_genericY, negY]
    change -gY - (E⁄L).a₁ * gX - (E⁄L).a₃ = -gY - ((E⁄L).a₁ * gX + (E⁄L).a₃)
    ring
  have hιY : ((negEquiv E (AlgebraicClosure K) : L →ₐ[AlgebraicClosure K] L) gY) ^ 2 +
      A * (negEquiv E (AlgebraicClosure K) : L →ₐ[AlgebraicClosure K] L) gY + B = 0 := by
    rw [hιY']
    linear_combination hYq
  have hgen : adjoin (AlgebraicClosure K) {gX, gY} = ⊤ :=
    functionField_adjoin_X_Y (E.baseChange (AlgebraicClosure K))
  apply DkMath.Lib.Algebra.QuadraticInvolutionDegree.finrank_fieldRange_le
    gX gY hgen A B hAmem hBmem hYq (multiplicationPull E n hn)
    (negEquiv E (AlgebraicClosure K) : L →ₐ[AlgebraicClosure K] L) hιX hιY
    (negEquiv_multiplicationPull_genericY_ne E n hn)
    ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ))
    ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)) (pow_pos (Nat.pos_of_ne_zero hn) 2)
  · have hφ : (E⁄L).Φ (n : ℤ) = ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ)).map (algebraMap (AlgebraicClosure K) L) :=
      E.baseChange_Φ (IsScalarTower.toAlgHom K (AlgebraicClosure K) L) (n : ℤ)
    have hψ : (E⁄L).ΨSq (n : ℤ) = ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).map (algebraMap (AlgebraicClosure K) L) :=
      E.baseChange_ΨSq (IsScalarTower.toAlgHom K (AlgebraicClosure K) L) (n : ℤ)
    have hnP := generic_nsmul_ne_zero E n hn
    have hx : multiplicationPull E n hn gX = ((E⁄L).Φ (n : ℤ)).eval gX / ((E⁄L).ΨSq (n : ℤ)).eval gX :=
      (multiplicationPull_genericX E n hn).trans (nsmul_x_formula (E.baseChange L) n (generic_nonsingular E (AlgebraicClosure K)) hnP)
    have hψ0 : ((E⁄L).ΨSq (n : ℤ)).eval gX ≠ 0 := by
      rw [← EllipticDivision.WeierstrassCurve.evalEval_ψ_sq (E.baseChange L) (generic_equation E (AlgebraicClosure K))]
      apply pow_ne_zero
      intro hz
      apply hnP
      have he := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
        (E.baseChange L) (generic_nonsingular E (AlgebraicClosure K)) (n : ℤ)).mpr hz
      rwa [natCast_zsmul] at he
    rw [← eval_map_algebraMap, ← eval_map_algebraMap, ← hφ, ← hψ, hx, div_mul_cancel₀ _ hψ0]
  · intro M c
    rw [← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq,
      natDegree_sub_eq_left_of_natDegree_lt, WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
    apply lt_of_le_of_lt (natDegree_C_mul_le c _)
    have hd := ((E.baseChange (AlgebraicClosure K)).map (algebraMap (AlgebraicClosure K) M)).natDegree_ΨSq_le (n : ℤ)
    rw [Int.natAbs_natCast] at hd
    rw [WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
    have hp : 0 < n ^ 2 := pow_pos (Nat.pos_of_ne_zero hn) _
    omega

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
