/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, smul_formula_or_zero.
Modified for DkMath: actual kernel points, characteristic zero and a Jacobian proof of coprimality.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionNontrivial
import DkMath.Lib.Algebra.RationalPolynomialFiber

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationCoordinates"

/-!
# 倍写像の分子・分母の非退化性と、実際の有限座標

分母ΨSqₙが零でなければ、NOTE-012のJacobian公式を有限座標へ戻して
x([n]P)ΨSqₙ(x(P))=Φₙ(x(P))を得る。
分子・分母の共通根の排除には、隣り合う除法多項式の再帰を追加移植する必要がない。
根xを曲線上の非特異点へ持ち上げ、実際の[n]PのJacobian表示を使う。
共通根ならそのZ座標ψₙとX座標φₙが同時に零になるが、非特異な無限遠点ではX≠0である。

互いに素性とΦₙの正の次数から、一般の有理関数のWronskian非零補題を適用する。
これらは実際の倍写像に依存する幾何学的な供給であり、位数p²を仮定した結論ではない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- 分母が非零なら、実際のn倍点の有限座標はΦₙ/ΨSqₙで与えられる。
除算した等式ではなく分母を掛けた等式として公開する。 -/
theorem multiplication_finite_coordinates (n : ℕ) {x y : AlgebraicClosure K}
    (h : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular x y)
    (hd : ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).eval x ≠ 0) :
    ∃ (x' y' : AlgebraicClosure K) (h' : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular x' y'),
      (nsmulAddMonoidHom n : Points E →+ Points E) (Affine.Point.some x y h) =
        Affine.Point.some x' y' h' ∧
      x' * ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).eval x =
        ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ)).eval x := by
  classical
  let W := E.baseChange (AlgebraicClosure K)
  have hs := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq W h.1 (n : ℤ)
  have hψ : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := by
    intro hz
    exact hd (by rw [← hs, hz, zero_pow two_ne_zero])
  have key := EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval W h (n : ℤ)
  let V := EllipticDivision.WeierstrassCurve.smulEval W x y (n : ℤ)
  have hvz : V 2 ≠ 0 := hψ
  have hv := key ▸ ((n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h)).nonsingular
  have he : ((n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h)) =
      Jacobian.Point.mk hv := Jacobian.Point.ext key
  refine ⟨V 0 / V 2 ^ 2, V 1 / V 2 ^ 3, (Jacobian.nonsingular_of_Z_ne_zero hvz).mp hv, ?_, ?_⟩
  · calc n • (Affine.Point.some x y h : Points E)
        = Jacobian.Point.toAffineAddEquiv W
          ((n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h)) := by
            rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
              AddEquiv.apply_symm_apply, natCast_zsmul]
      _ = _ := by
        rw [he, Jacobian.Point.toAffineAddEquiv_apply]
        exact Jacobian.Point.toAffineLift_of_Z_ne_zero hvz
  · change (W.φ (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 2 *
      (W.ΨSq (n : ℤ)).eval x = (W.Φ (n : ℤ)).eval x
    rw [← hs, div_mul_cancel₀ _ (pow_ne_zero 2 hψ),
      EllipticDivision.WeierstrassCurve.evalEval_φ W h.1]

variable [E.IsElliptic]

/-- 共通根なら実際のn倍点のJacobian表示でX=Z=0となり、非特異性に反する。 -/
theorem multiplication_polynomials_no_common_root (n : ℕ) (x : AlgebraicClosure K) :
    ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ)).eval x ≠ 0 ∨
      ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).eval x ≠ 0 := by
  classical
  by_contra hh
  push Not at hh
  obtain ⟨hφ, hΨ⟩ := hh
  let W := E.baseChange (AlgebraicClosure K)
  obtain ⟨y, hy⟩ := exists_affine_equation_y E x
  have : W.IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  have key := EllipticDivision.WeierstrassCurve.zsmul_eq_smulEval W hns (n : ℤ)
  have hv := ((n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y hns)).nonsingular
  rw [key] at hv
  have hXYZ := (Jacobian.nonsingularLift_iff _).mp hv
  have hs := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq W hy (n : ℤ)
  have hz : (EllipticDivision.WeierstrassCurve.smulEval W x y (n : ℤ)) 2 = 0 :=
    eq_zero_of_pow_eq_zero (hs.trans hΨ)
  have hx : (EllipticDivision.WeierstrassCurve.smulEval W x y (n : ℤ)) 0 = 0 :=
    (EllipticDivision.WeierstrassCurve.evalEval_φ W hy (n : ℤ)).trans hφ
  exact Jacobian.X_ne_zero_of_Z_eq_zero hXYZ hz hx

/-- 代数閉包上で共通根がないので、倍写像の分子・分母は互いに素である。 -/
theorem multiplication_polynomials_isCoprime (n : ℕ) :
    IsCoprime ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ))
      ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := AlgebraicClosure K) (K := AlgebraicClosure K)]
  intro x
  simpa only [coe_aeval_eq_eval] using multiplication_polynomials_no_common_root E n x

/-- 非零指数ならΦₙは非定数であり、互いに素性からWronskianは非零となる。 -/
theorem multiplication_wronskian_ne_zero (n : ℕ) (hn : n ≠ 0) :
    DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian
      ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ))
      ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)) ≠ 0 := by
  apply DkMath.Lib.Algebra.RationalPolynomialFiber.wronskian_ne_zero
    (multiplication_polynomials_isCoprime E n)
  rw [WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
  exact pow_pos (Nat.pos_of_ne_zero hn) 2

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
