/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase
import DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization
import DkMath.Lib.NumberTheory.EllipticFiniteKernelTwoTorsion
import DkMath.Lib.Algebra.WronskianCrossMultiplication

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization"

/-!
# Wronskian 局所評価の二捩れ入口

この層は、関数体上の Wronskian 恒等式そのものを再証明しない。
既存の `kernelXAt_translation`、`kernelYAt_translation`、`kernelYAt_neg` を
使い、源の二捩れ点を核の半代表で平行移動した点で、

`z_source ≠ 0` と `z_target = 0`

を別々に固定する。したがって、後続の点評価では「源では分母因子が非零」
と「標的の平方完成座標が零」を独立した入力として渡せる。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.Algebra.RationalPolynomialFiber
open scoped BigOperators

variable {K : Type*} [Field K] [NeZero (2 : K)]

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianSpecialization
    {α : Type*} : DecidableEq α := Classical.decEq _

omit [NeZero (2 : K)] in
/-- `genericX` is transcendental over the algebraic closure, by its double pole at `O`.

This is the coefficient-descent guard used when an equality of rational functions
is upgraded to an equality in `(AlgebraicClosure K)[X]`.  The proof uses only the
valuation of the Weierstrass x-coordinate at the point at infinity; it does not
assume that evaluation at an arbitrary function-field element is injective.
-/
theorem genericX_transcendental_for_wronskian
    (E : WeierstrassCurve K) [E.IsElliptic] :
    Transcendental (AlgebraicClosure K) (genericX E (AlgebraicClosure K)) := by
  apply transcendental_of_point_pole E 0
  change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point)
    (genericX E (AlgebraicClosure K))
  rw [pointValuation_zero_genericX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

omit [NeZero (2 : K)] in
/-- Every base-coefficient polynomial in `genericX` is regular at a finite point.

The proof is the valuation-theoretic form of polynomial substitution: `genericX`
is congruent to the point's x-coordinate, and `Valuation.Cong.eval₂` propagates
that congruence through the polynomial.  This lemma is the basic regularity
input for evaluating the base Vélu numerator, denominator, and Wronskian.
-/
theorem pointValuation_aeval_le_one
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E) (hP : P ≠ 0) (p : (AlgebraicClosure K)[X]) :
    pointValuation E P
        (Polynomial.aeval (genericX E (AlgebraicClosure K)) p) ≤ 1 := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let x := genericX E (AlgebraicClosure K)
  have hc : ∀ c : AlgebraicClosure K,
      pointValuation E P (algebraMap (AlgebraicClosure K) F c) ≤ 1 := by
    intro c
    exact pointValuation_const_le_one E P c
  have hxc : (pointValuation E P).Cong x
      (algebraMap (AlgebraicClosure K) F P.xc) := by
    have h := value_spec E P x (pointValuation_genericX_le_one E P hP)
    rw [value_genericX E P hP] at h
    exact h
  have hh := (Valuation.Cong.eval₂ (algebraMap (AlgebraicClosure K) F)
    hc hxc (hc P.xc) p).1
  rw [eval₂_at_apply] at hh
  exact hh.le_one (hc _)

omit [NeZero (2 : K)] in
/-- The finite value of a base polynomial is its ordinary x-coordinate evaluation. -/
theorem value_aeval_eq_eval
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E) (hP : P ≠ 0) (p : (AlgebraicClosure K)[X]) :
    value E P (Polynomial.aeval (genericX E (AlgebraicClosure K)) p)
        (pointValuation_aeval_le_one E P hP p) = p.eval P.xc := by
  apply value_eq
  have hc : ∀ c : AlgebraicClosure K,
      pointValuation E P (algebraMap (AlgebraicClosure K)
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField c) ≤ 1 := by
    intro c
    exact pointValuation_const_le_one E P c
  have hxc : (pointValuation E P).Cong (genericX E (AlgebraicClosure K))
      (algebraMap (AlgebraicClosure K)
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField P.xc) := by
    have h := value_spec E P (genericX E (AlgebraicClosure K))
      (pointValuation_genericX_le_one E P hP)
    rw [value_genericX E P hP] at h
    exact h
  have hh := (Valuation.Cong.eval₂
    (algebraMap (AlgebraicClosure K)
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    hc hxc (hc P.xc) p).1
  rw [eval₂_at_apply] at hh
  exact hh

omit [NeZero (2 : K)] in
/-- Congruence form of `value_aeval_eq_eval`, convenient for products and sums. -/
theorem pointValuation_aeval_congr_eval
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E) (hP : P ≠ 0) (p : (AlgebraicClosure K)[X]) :
    (pointValuation E P).Cong
      (Polynomial.aeval (genericX E (AlgebraicClosure K)) p)
      (algebraMap _ _ (p.eval P.xc)) := by
  have h := value_spec E P
    (Polynomial.aeval (genericX E (AlgebraicClosure K)) p)
    (pointValuation_aeval_le_one E P hP p)
  rw [value_aeval_eq_eval E P hP p] at h
  exact h

omit [NeZero (2 : K)] in
/-- Specialize a cleared identity through the regular-point evaluation hom.

This generic packet is the reusable `evalHom` core of the Vélu specialization:
all six function-field terms are supplied with regularity and a congruence to a
constant.  The conclusion is the corresponding coefficient-field identity.
It avoids repeating valuation-level product bookkeeping in every geometric
application.
-/
theorem evalHom_cleared_identity
    (E : WeierstrassCurve K) [E.IsElliptic]
    (P : Points E)
    (d dp a ap z zH : AlgebraicClosure K)
    (fD fDp fA fAp fZ fZH :
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hD : pointValuation E P fD ≤ 1)
    (hDp : pointValuation E P fDp ≤ 1)
    (hA : pointValuation E P fA ≤ 1)
    (hAp : pointValuation E P fAp ≤ 1)
    (hZ : pointValuation E P fZ ≤ 1)
    (hZH : pointValuation E P fZH ≤ 1)
    (hDval : (pointValuation E P).Cong fD (algebraMap _ _ d))
    (hDpval : (pointValuation E P).Cong fDp (algebraMap _ _ dp))
    (hAval : (pointValuation E P).Cong fA (algebraMap _ _ a))
    (hApval : (pointValuation E P).Cong fAp (algebraMap _ _ ap))
    (hZval : (pointValuation E P).Cong fZ (algebraMap _ _ z))
    (hZHval : (pointValuation E P).Cong fZH (algebraMap _ _ zH))
    (hidentity : fD ^ 2 * fZH = fZ * (fAp * fD - fA * fDp)) :
    d ^ 2 * zH = z * (ap * d - a * dp) := by
  let d' : regularAlgebra E P := ⟨fD, hD⟩
  let dp' : regularAlgebra E P := ⟨fDp, hDp⟩
  let a' : regularAlgebra E P := ⟨fA, hA⟩
  let ap' : regularAlgebra E P := ⟨fAp, hAp⟩
  let z' : regularAlgebra E P := ⟨fZ, hZ⟩
  let zH' : regularAlgebra E P := ⟨fZH, hZH⟩
  have hreg : d' ^ 2 * zH' = z' * (ap' * d' - a' * dp') := by
    apply Subtype.ext
    exact hidentity
  have hd : evalHom E P d' = d := by
    rw [evalHom_apply]
    exact value_eq E P fD hD d hDval
  have hdp : evalHom E P dp' = dp := by
    rw [evalHom_apply]
    exact value_eq E P fDp hDp dp hDpval
  have ha : evalHom E P a' = a := by
    rw [evalHom_apply]
    exact value_eq E P fA hA a hAval
  have hap : evalHom E P ap' = ap := by
    rw [evalHom_apply]
    exact value_eq E P fAp hAp ap hApval
  have hz : evalHom E P z' = z := by
    rw [evalHom_apply]
    exact value_eq E P fZ hZ z hZval
  have hzH : evalHom E P zH' = zH := by
    rw [evalHom_apply]
    exact value_eq E P fZH hZH zH hZHval
  have hev := congrArg (evalHom E P) hreg
  simpa only [map_mul, map_pow, map_sub, hd, hdp, ha, hap, hz, hzH] using hev

omit [NeZero (2 : K)] in
/-- The base-field common denominator is non-zero at the generic x-coordinate.

Each finite-product factor is a square of `genericX - x(Q)`.  The generic
coordinate is transcendental, hence cannot equal the algebraic x-coordinate of
any half-kernel representative.  This is the function-field counterpart of
the finite-point collision lemma proved below.
-/
theorem veluHalfDenominatorBase_eval_genericX_ne_zero
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H] :
    Polynomial.aeval (genericX E (AlgebraicClosure K))
      (veluHalfDenominatorBase E H) ≠ 0 := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  simp only [map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun Q hQ => by
    simp only [xCorrectionDenominator, map_mul, map_sub, aeval_X, aeval_C]
    exact mul_ne_zero (sub_ne_zero.mpr (genericX_ne_const E Q.val.xc))
      (sub_ne_zero.mpr (genericX_ne_const E Q.val.xc)))

omit [NeZero (2 : K)] in
/-- The function-field Vélu quotient can be read from the base-coefficient pair.

`map_veluHalfNumeratorBase` and `map_veluHalfDenominatorBase` identify the
coefficient images.  `eval_map_algebraMap` then turns evaluation of those images
back into `aeval` of the algebraic-closure polynomials, so the quotient is
available in exactly the coefficient type required by `cross_relation_of_aeval_div_eq`.
-/
theorem veluX_eq_veluHalfNumeratorBase_div_denominator
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K))
        (veluHalfNumeratorBase E H) /
        Polynomial.aeval (genericX E (AlgebraicClosure K))
          (veluHalfDenominatorBase E H) := by
  have h := veluX_eq_veluHalfNumerator_div_denominator E H ho
  have hN := map_veluHalfNumeratorBase E H
  have hD := map_veluHalfDenominatorBase E H
  dsimp only at hN hD
  rw [← hN, ← hD] at h
  simpa only [eval_map_algebraMap] using h

omit [NeZero (2 : K)] in
/-- Rewrite the cleared Wronskian identity using the base-coefficient pair.

This is still an identity in the elliptic function field.  The point-specialized
theorem below is deliberately separated from it: coefficient descent is handled
here, while regularity and `evalHom` are handled at the finite point.
-/
theorem veluHalf_base_cleared_identity_function_field
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let W := E.map (algebraMap K F)
    let x := genericX E (AlgebraicClosure K)
    let z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
    (Polynomial.aeval x (veluHalfDenominatorBase E H)) ^ 2 *
        (2 * veluY E H + W.a₁ * veluX E H + W.a₃) =
      z * (Polynomial.aeval x (derivative (veluHalfNumeratorBase E H)) *
          Polynomial.aeval x (veluHalfDenominatorBase E H) -
        Polynomial.aeval x (veluHalfNumeratorBase E H) *
          Polynomial.aeval x (derivative (veluHalfDenominatorBase E H))) := by
  dsimp only
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let x := genericX E (AlgebraicClosure K)
  have h := veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian E H ho
  dsimp only at h
  have hN := map_veluHalfNumeratorBase E H
  have hD := map_veluHalfDenominatorBase E H
  dsimp only at hN hD
  rw [← hN, ← hD] at h
  simpa only [eval_map_algebraMap, derivative_map] using h

/-- Pointwise specialization of the cleared Vélu/Wronskian identity.

The function-field identity is transported through `evalHom` at a point outside
the kernel.  Every polynomial term is regular by `pointValuation_aeval_le_one`,
while the two Vélu coordinates are regular by the existing pole-support
theorem.  This is the textbook bridge from the formal identity in the generic
coordinate to the finite-point equation used for Wronskian roots.
-/
theorem veluHalf_cleared_identity_at_kernel_outside
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (R : Points E) (hR : R ∉ H) :
    (veluHalfDenominatorBase E H).eval R.xc ^ 2 *
        (2 * kernelYAt E H R hR +
          (kernelModel E H).a₁ * kernelXAt E H R hR +
          (kernelModel E H).a₃) =
      (2 * R.yc + (E⁄(AlgebraicClosure K)).a₁ * R.xc +
        (E⁄(AlgebraicClosure K)).a₃) *
        (wronskian (veluHalfNumeratorBase E H)
          (veluHalfDenominatorBase E H)).eval R.xc := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let x := genericX E (AlgebraicClosure K)
  let D := Polynomial.aeval x (veluHalfDenominatorBase E H)
  let Dp := Polynomial.aeval x (derivative (veluHalfDenominatorBase E H))
  let A := Polynomial.aeval x (veluHalfNumeratorBase E H)
  let Ap := Polynomial.aeval x (derivative (veluHalfNumeratorBase E H))
  let Z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
  let ZH := 2 * veluY E H + W.a₁ * veluX E H + W.a₃
  have hR0 : R ≠ 0 := by
    intro h0
    exact hR (h0 ▸ H.zero_mem)
  have hD : pointValuation E R D ≤ 1 := by
    dsimp [D]
    exact pointValuation_aeval_le_one E R hR0 _
  have hDp : pointValuation E R Dp ≤ 1 := by
    dsimp [Dp]
    exact pointValuation_aeval_le_one E R hR0 _
  have hA : pointValuation E R A ≤ 1 := by
    dsimp [A]
    exact pointValuation_aeval_le_one E R hR0 _
  have hAp : pointValuation E R Ap ≤ 1 := by
    dsimp [Ap]
    exact pointValuation_aeval_le_one E R hR0 _
  have hW₁ : algebraMap (AlgebraicClosure K) F
      (E⁄(AlgebraicClosure K)).a₁ = W.a₁ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₁).symm
  have hW₃ : algebraMap (AlgebraicClosure K) F
      (E⁄(AlgebraicClosure K)).a₃ = W.a₃ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₃).symm
  let V := (pointValuation E R).valuationSubring
  have hxV : x ∈ V := pointValuation_genericX_le_one E R hR0
  have hyV : genericY E (AlgebraicClosure K) ∈ V :=
    pointValuation_genericY_le_one E R hR0
  have hcoef (c : AlgebraicClosure K) : algebraMap (AlgebraicClosure K) F c ∈ V :=
    pointValuation_const_le_one E R c
  have hXv : veluX E H ∈ V := veluX_regular_outside E H R hR
  have hYv : veluY E H ∈ V := veluY_regular_outside E H R hR
  have h2v : (2 : F) ∈ V := by simpa only [map_ofNat] using hcoef (2 : AlgebraicClosure K)
  have hW₁v : W.a₁ ∈ V := by rw [← hW₁]; exact hcoef _
  have hW₃v : W.a₃ ∈ V := by rw [← hW₃]; exact hcoef _
  have hZ : pointValuation E R Z ≤ 1 := by
    dsimp [Z]
    exact V.toSubring.add_mem
      (V.toSubring.add_mem
        (V.toSubring.mul_mem h2v hyV)
        (V.toSubring.mul_mem hW₁v hxV))
      hW₃v
  have hZH : pointValuation E R ZH ≤ 1 := by
    dsimp [ZH]
    exact V.toSubring.add_mem
      (V.toSubring.add_mem (V.toSubring.mul_mem h2v hYv)
        (V.toSubring.mul_mem hW₁v hXv)) hW₃v
  have hDval : (pointValuation E R).Cong D
      (algebraMap _ _ ((veluHalfDenominatorBase E H).eval R.xc)) := by
    dsimp [D]
    exact pointValuation_aeval_congr_eval E R hR0 _
  have hDpval : (pointValuation E R).Cong Dp
      (algebraMap _ _ ((derivative (veluHalfDenominatorBase E H)).eval R.xc)) := by
    dsimp [Dp]
    exact pointValuation_aeval_congr_eval E R hR0 _
  have hAval : (pointValuation E R).Cong A
      (algebraMap _ _ ((veluHalfNumeratorBase E H).eval R.xc)) := by
    dsimp [A]
    exact pointValuation_aeval_congr_eval E R hR0 _
  have hApval : (pointValuation E R).Cong Ap
      (algebraMap _ _ ((derivative (veluHalfNumeratorBase E H)).eval R.xc)) := by
    dsimp [Ap]
    exact pointValuation_aeval_congr_eval E R hR0 _
  have hx : (pointValuation E R).Cong x
      (algebraMap _ _ R.xc) := by
    have h := value_spec E R x (pointValuation_genericX_le_one E R hR0)
    rw [value_genericX E R hR0] at h
    exact h
  have hy : (pointValuation E R).Cong (genericY E (AlgebraicClosure K))
      (algebraMap _ _ R.yc) := by
    have h := value_spec E R (genericY E (AlgebraicClosure K))
      (pointValuation_genericY_le_one E R hR0)
    rw [value_genericY E R hR0] at h
    exact h
  have hZval : (pointValuation E R).Cong Z
      (algebraMap _ _ (2 * R.yc + (E⁄(AlgebraicClosure K)).a₁ * R.xc +
        (E⁄(AlgebraicClosure K)).a₃)) := by
    dsimp [Z]
    have htwo : (pointValuation E R).Cong
        (2 * genericY E (AlgebraicClosure K))
        (2 * algebraMap _ _ R.yc) := by
      simpa only [map_ofNat] using
        ((Valuation.Cong.rfl (v := pointValuation E R) (a := (2 : F))).mul hy
          h2v (pointValuation_const_le_one E R R.yc))
    have hax : (pointValuation E R).Cong
        (W.a₁ * x)
        (W.a₁ * algebraMap _ _ R.xc) :=
      (Valuation.Cong.rfl (v := pointValuation E R) (a := W.a₁)).mul hx
        hW₁v (pointValuation_const_le_one E R R.xc)
    have h3 : (pointValuation E R).Cong W.a₃
        (algebraMap _ _ (E⁄(AlgebraicClosure K)).a₃) := by
      rw [← hW₃]
    have hz' := (htwo.add hax).add h3
    rw [← hW₁, ← hW₃]
    rw [← hW₁, ← hW₃] at hz'
    simpa only [map_add, map_mul, map_ofNat] using hz'
  have hX : (pointValuation E R).Cong (veluX E H)
      (algebraMap _ _ (kernelXAt E H R hR)) := (kernelAt_congr E H R hR).1
  have hY : (pointValuation E R).Cong (veluY E H)
      (algebraMap _ _ (kernelYAt E H R hR)) := (kernelAt_congr E H R hR).2
  have hZHval : (pointValuation E R).Cong ZH
      (algebraMap _ _ (2 * kernelYAt E H R hR +
        (kernelModel E H).a₁ * kernelXAt E H R hR +
        (kernelModel E H).a₃)) := by
    dsimp [ZH]
    have htwo : (pointValuation E R).Cong
        (2 * veluY E H)
        (2 * algebraMap _ _ (kernelYAt E H R hR)) := by
      simpa only [map_ofNat] using
        ((Valuation.Cong.rfl (v := pointValuation E R) (a := (2 : F))).mul hY
          h2v (pointValuation_const_le_one E R (kernelYAt E H R hR)))
    have hax : (pointValuation E R).Cong
        (W.a₁ * veluX E H)
        (W.a₁ * algebraMap _ _ (kernelXAt E H R hR)) :=
      (Valuation.Cong.rfl (v := pointValuation E R) (a := W.a₁)).mul hX
        hW₁v (pointValuation_const_le_one E R (kernelXAt E H R hR))
    have h3 : (pointValuation E R).Cong W.a₃
        (algebraMap _ _ (kernelModel E H).a₃) := by
      rw [kernelModel_a₃, ← hW₃]
    have hz' := (htwo.add hax).add h3
    rw [← hW₁, ← hW₃]
    rw [← hW₁, ← hW₃] at hz'
    simpa only [map_add, map_mul, map_ofNat, kernelModel_a₁,
      kernelModel_a₃] using hz'
  have hidentity : D ^ 2 * ZH = Z * (Ap * D - A * Dp) := by
    simpa only [D, Dp, A, Ap, Z, ZH] using
      veluHalf_base_cleared_identity_function_field E H ho
  have hpoint := evalHom_cleared_identity (K := K) (E := E) (P := R)
    (d := (veluHalfDenominatorBase E H).eval R.xc)
    (dp := (derivative (veluHalfDenominatorBase E H)).eval R.xc)
    (a := (veluHalfNumeratorBase E H).eval R.xc)
    (ap := (derivative (veluHalfNumeratorBase E H)).eval R.xc)
    (z := 2 * R.yc + (E⁄(AlgebraicClosure K)).a₁ * R.xc +
      (E⁄(AlgebraicClosure K)).a₃)
    (zH := 2 * kernelYAt E H R hR + (kernelModel E H).a₁ * kernelXAt E H R hR +
      (kernelModel E H).a₃)
    (fD := D) (fDp := Dp) (fA := A) (fAp := Ap) (fZ := Z) (fZH := ZH)
    hD hDp hA hAp hZ hZH hDval hDpval hAval hApval hZval hZHval hidentity
  simpa only [wronskian, eval_sub, eval_mul, mul_assoc] using hpoint

omit [NeZero (2 : K)] in
/-- A standard `RatFunc` presentation cross-multiplies with the base Vélu pair.

The two quotient presentations of `veluX` are first aligned in the function
field.  `genericX_transcendental_for_wronskian` and
`cross_relation_of_aeval_div_eq` then turn that evaluated equality into the
polynomial identity required for Wronskian transport.  The denominator guard is
kept explicit rather than being inferred from a formal fraction.
-/
theorem veluX_standard_pair_cross_relation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G) :
    F * veluHalfDenominatorBase E H =
      veluHalfNumeratorBase E H * G := by
  let x := genericX E (AlgebraicClosure K)
  have hD : Polynomial.aeval x (veluHalfDenominatorBase E H) ≠ 0 := by
    simpa [x] using veluHalfDenominatorBase_eval_genericX_ne_zero E H
  have hbase := veluX_eq_veluHalfNumeratorBase_div_denominator E H ho
  have hfrac : Polynomial.aeval x F / Polynomial.aeval x G =
      Polynomial.aeval x (veluHalfNumeratorBase E H) /
        Polynomial.aeval x (veluHalfDenominatorBase E H) := by
    calc
      Polynomial.aeval x F / Polynomial.aeval x G = veluX E H := by
        simpa [x] using hrel.symm
      _ = Polynomial.aeval x (veluHalfNumeratorBase E H) /
          Polynomial.aeval x (veluHalfDenominatorBase E H) := by
        simpa [x] using hbase
  exact cross_relation_of_aeval_div_eq F G (veluHalfNumeratorBase E H)
    (veluHalfDenominatorBase E H) x
    (genericX_transcendental_for_wronskian E) hG hD hfrac

omit [NeZero (2 : K)] in
/-- 源曲線上で、有限点の平方完成座標が零なら反転固定点になる。 -/
theorem eq_neg_of_completedSquare_eq_zero
    (E : WeierstrassCurve K) (P : Points E) (hP : P ≠ 0)
    (hz : 2 * P.yc + (E⁄(AlgebraicClosure K)).a₁ * P.xc +
        (E⁄(AlgebraicClosure K)).a₃ = 0) :
    -P = P := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hns =>
      change -(Point.some x y hns : (E⁄(AlgebraicClosure K)).Point) =
        (Point.some x y hns : (E⁄(AlgebraicClosure K)).Point)
      rw [Affine.Point.neg_some, Affine.Point.some.injEq]
      constructor
      · rfl
      · dsimp only [Affine.negY]
        change -y - (E⁄(AlgebraicClosure K)).a₁ * x -
          (E⁄(AlgebraicClosure K)).a₃ = y
        change 2 * y + (E⁄(AlgebraicClosure K)).a₁ * x +
          (E⁄(AlgebraicClosure K)).a₃ = 0 at hz
        linear_combination -hz

omit [NeZero (2 : K)] in
/-- 反転非固定な有限点では、源の平方完成座標は非零である。 -/
theorem completedSquare_ne_zero_of_neg_ne
    (E : WeierstrassCurve K) (P : Points E) (hP : P ≠ 0)
    (hneg : -P ≠ P) :
    2 * P.yc + (E⁄(AlgebraicClosure K)).a₁ * P.xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0 := by
  intro hz
  exact hneg (eq_neg_of_completedSquare_eq_zero E P hP hz)

/-- 核外の源二捩れ点は、標的側の平方完成座標を零に送る。 -/
theorem kernelAt_completedSquare_eq_zero_of_neg_fixed
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    2 * kernelYAt E H P hP + (kernelModel E H).a₁ * kernelXAt E H P hP +
        (kernelModel E H).a₃ = 0 := by
  have hy := kernelYAt_neg E H P hP
  have hy' : kernelYAt E H P hP =
      -kernelYAt E H P hP - (E⁄(AlgebraicClosure K)).a₁ * kernelXAt E H P hP -
        (E⁄(AlgebraicClosure K)).a₃ := by
    simpa only [hneg] using hy
  rw [kernelModel_a₁, kernelModel_a₃]
  linear_combination hy'

/-- 二捩れ点を半核代表で移動しても、標的の平方完成座標は零である。 -/
theorem kernelAt_completedSquare_eq_zero_of_neg_fixed_translation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) :
    2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0 := by
  rw [kernelYAt_translation E H P hP Q,
    kernelXAt_translation E H P hP Q]
  exact kernelAt_completedSquare_eq_zero_of_neg_fixed E H P hP hneg

/-! `T + Q` は核の外に残るので、源側の平方完成座標へも同じ点評価 API を
適用できる。ここでは `T + Q` が反転固定でないことを仮定として明示する。
奇数核からこの仮定を供給する群論補題は、核の位数条件を扱う別層に残す。 -/

omit [NeZero (2 : K)] in
/-- 核外の点を核点で移動したとき、源側の平方完成座標が非零なら
標的側の平方完成座標零性と同じ軌道で利用できる。 -/
theorem completedSquare_ne_zero_of_neg_ne_translation
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E))
    (P : Points E) (hP : P ∉ H) (Q : H)
    (hneg : -(P + Q.val) ≠ P + Q.val) :
    2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0 := by
  apply completedSquare_ne_zero_of_neg_ne E (P + Q.val) ?_ hneg
  intro hz
  apply hP
  rw [eq_neg_of_add_eq_zero_left hz]
  exact H.neg_mem Q.property

omit [NeZero (2 : K)] in
/-- 奇数位数の核では、非零核点を二捩れ点へ加えても反転固定にはならない。
反転固定を仮定すると、二捩れ点の差である核点自身も反転固定になり、
`eq_zero_of_mem_odd_kernel_fixed` により零点へ落ちる。 -/
theorem neg_ne_of_odd_kernel_twoTorsion_translate
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E))
    (hodd : Odd (Nat.card H))
    (P : Points E) (hneg : -P = P) (Q : H) (hQ : Q ≠ 0) :
    -(P + Q.val) ≠ P + Q.val := by
  intro hnegTranslation
  have htwoP : P + P = 0 := by
    simpa only [hneg] using add_neg_cancel P
  have htwoPQ : (P + Q.val) + (P + Q.val) = 0 := by
    simpa only [hnegTranslation] using add_neg_cancel (P + Q.val)
  have htwoQ : Q.val + Q.val = 0 := by
    calc
      Q.val + Q.val = (P + Q.val) + (P + Q.val) - (P + P) := by abel
      _ = 0 - 0 := by rw [htwoPQ, htwoP]
      _ = 0 := sub_self 0
  have hnegQ : -Q.val = Q.val :=
    (eq_neg_of_add_eq_zero_left htwoQ).symm
  have hQval : Q.val = 0 :=
    eq_zero_of_mem_odd_kernel_fixed E H hodd Q.val Q.property hnegQ
  apply hQ
  exact Subtype.ext hQval

omit [NeZero (2 : K)] in
/-- 基礎係数体側の共通分母は、評価点のx座標が各半核代表と衝突しなければ
非零である。これは後続の Wronskian 恒等式を点へ特殊化する際の分母条件を、
有限積の各因子へ分解した形で供給する。 -/
theorem veluHalfDenominatorBase_eval_ne_zero
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (R : Points E) (hcollision : ∀ Q : halfKernel E H,
      R.xc ≠ Q.val.val.xc) :
    (veluHalfDenominatorBase E H).eval R.xc ≠ 0 := by
  classical
  unfold veluHalfDenominatorBase commonDenominator
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro Q hQ
  simp only [xCorrectionDenominator, eval_mul, eval_sub, eval_X, eval_C]
  exact mul_ne_zero
    (sub_ne_zero.mpr (hcollision ⟨Q, hQ⟩))
    (sub_ne_zero.mpr (hcollision ⟨Q, hQ⟩))

omit [NeZero (2 : K)] in
/-- 核外点を核点で移動した点の x 座標は、半核のどの代表とも衝突しない。
同じ x 座標なら有限点は同一点か反転対であり、いずれの場合も `P ∈ H` を
導くため、核外仮定に反する。 -/
theorem translated_x_ne_halfKernel_of_kernel_outside
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) (S : halfKernel E H) :
    (P + Q.val).xc ≠ S.val.val.xc := by
  intro hx
  have hR : P + Q.val ≠ 0 := by
    intro hzero
    apply hP
    rw [eq_neg_of_add_eq_zero_left hzero]
    exact H.neg_mem Q.property
  have hS : S.val.val ≠ 0 := by
    intro hzero
    have hsub : S.val = 0 := Subtype.ext hzero
    exact ((mem_halfKernel E H S.val).mp S.property).1 hsub
  rcases point_eq_or_eq_neg_of_xc_eq E (P + Q.val) S.val.val hR hS hx with he | he
  · apply hP
    have hp0 : P = S.val.val - Q.val := by
      calc
        P = (P + Q.val) - Q.val := by abel
        _ = S.val.val - Q.val := by rw [he]
    rw [hp0]
    exact H.sub_mem S.val.property Q.property
  · apply hP
    have hp0 : P = -S.val.val - Q.val := by
      calc
        P = (P + Q.val) - Q.val := by abel
        _ = -S.val.val - Q.val := by rw [he]
    rw [hp0]
    exact H.sub_mem (H.neg_mem S.val.property) Q.property

omit [NeZero (2 : K)] in
/-- 前の衝突排除を有限積へ適用した、翻訳点での基礎共通分母非零性。 -/
theorem veluHalfDenominatorBase_eval_ne_zero_translation
    (E : WeierstrassCurve K)
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (Q : H) :
    (veluHalfDenominatorBase E H).eval (P + Q.val).xc ≠ 0 := by
  apply veluHalfDenominatorBase_eval_ne_zero E H (P + Q.val)
  intro S
  exact translated_x_ne_halfKernel_of_kernel_outside E H P hP Q S

omit [NeZero (2 : K)] in
/-- Transport a base-pair Wronskian root to any translated kernel point.

The cross relation is supplied by the standard `veluX` quotient, while the
finite denominator is discharged by the x-coordinate collision lemma for
`P + Q`.  Thus the only geometric input left to the caller is the Wronskian
root for the base pair itself.
-/
theorem veluX_standard_pair_wronskian_root_of_translation
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (P : Points E) (hP : P ∉ H) (Q : H)
    (hbase :
      (wronskian (veluHalfNumeratorBase E H)
        (veluHalfDenominatorBase E H)).IsRoot (P + Q.val).xc) :
    (wronskian F G).IsRoot (P + Q.val).xc := by
  apply wronskian_isRoot_of_cross_relation F G
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H)
    (P + Q.val).xc
    (veluX_standard_pair_cross_relation E H ho F G hG hrel)
    (veluHalfDenominatorBase_eval_ne_zero_translation E H P hP Q)
    hbase

/-- Extract the base-pair Wronskian root from a cleared identity at `P + Q`.

The odd-kernel two-torsion packet supplies the two scalar facts
`z_source ≠ 0` and `z_target = 0`.  The remaining hypothesis is precisely the
point-specialized, denominator-cleared Vélu identity; keeping it explicit
marks the boundary where regular evaluation of the function-field identity
must still be proved.
-/
theorem veluHalf_base_wronskian_root_of_cleared_identity
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0)
    (hidentity :
      (veluHalfDenominatorBase E H).eval (P + Q.val).xc ^ 2 *
          (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
            (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
              (add_not_mem_kernel E H P hP Q) + (kernelModel E H).a₃) =
        (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
            (E⁄(AlgebraicClosure K)).a₃) *
          (wronskian (veluHalfNumeratorBase E H)
            (veluHalfDenominatorBase E H)).eval (P + Q.val).xc) :
    (wronskian (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).IsRoot (P + Q.val).xc := by
  have hnegTranslation := neg_ne_of_odd_kernel_twoTorsion_translate
    E H ho P hneg Q hQ
  have hz := completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hnegTranslation
  have hzH := kernelAt_completedSquare_eq_zero_of_neg_fixed_translation
    E H P hP hneg Q
  exact wronskian_isRoot_of_denominator_cleared_identity
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H)
    (P + Q.val).xc
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
      (E⁄(AlgebraicClosure K)).a₃)
    (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
      (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
        (add_not_mem_kernel E H P hP Q) + (kernelModel E H).a₃)
    hidentity hz hzH

/-- Odd-kernel two-torsion specialization of the base-pair Wronskian root.

The pointwise cleared identity is now supplied by
`veluHalf_cleared_identity_at_kernel_outside`; the completed-square packet
removes the scalar hypotheses used by the generic root-extraction lemma.
-/
theorem veluHalf_base_wronskian_root_of_odd_twoTorsion
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0) :
    (wronskian (veluHalfNumeratorBase E H)
      (veluHalfDenominatorBase E H)).IsRoot (P + Q.val).xc := by
  have hnegTranslation := neg_ne_of_odd_kernel_twoTorsion_translate
    E H ho P hneg Q hQ
  have hz := completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hnegTranslation
  have hzH := kernelAt_completedSquare_eq_zero_of_neg_fixed_translation
    E H P hP hneg Q
  exact wronskian_isRoot_of_denominator_cleared_identity
    (veluHalfNumeratorBase E H) (veluHalfDenominatorBase E H)
    (P + Q.val).xc
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
      (E⁄(AlgebraicClosure K)).a₃)
    (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
      (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
        (add_not_mem_kernel E H P hP Q) + (kernelModel E H).a₃)
    (veluHalf_cleared_identity_at_kernel_outside E H ho (P + Q.val)
      (add_not_mem_kernel E H P hP Q)) hz hzH

/-- Standard-pair form of the odd-kernel two-torsion Wronskian root.

The finite-point specialization first produces a root for the canonical
Vélu numerator/denominator pair.  The already established cross-relation
transport then carries that root to any polynomial pair `(F,G)` presenting
the same quotient `veluX`.  This is the first theorem in this file whose
conclusion is stated directly for the standard rational-function numerator
and denominator used by downstream fiber arguments.
-/
theorem veluX_standard_pair_wronskian_root_of_odd_twoTorsion
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H))
    (F G : (AlgebraicClosure K)[X])
    (hG : Polynomial.aeval (genericX E (AlgebraicClosure K)) G ≠ 0)
    (hrel : veluX E H =
      Polynomial.aeval (genericX E (AlgebraicClosure K)) F /
        Polynomial.aeval (genericX E (AlgebraicClosure K)) G)
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : H) (hQ : Q ≠ 0) :
    (wronskian F G).IsRoot (P + Q.val).xc := by
  apply veluX_standard_pair_wronskian_root_of_translation E H ho F G hG hrel P hP Q
  exact veluHalf_base_wronskian_root_of_odd_twoTorsion E H ho P hP hneg Q hQ

/-! 点評価へ渡す最小の「源非零・標的零」パケット。 -/

theorem completedSquare_translation_pair
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H)
    (hnegTranslation : -(P + Q.val) ≠ P + Q.val) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) := by
  constructor
  · exact completedSquare_ne_zero_of_neg_ne_translation E H P hP Q hnegTranslation
  · exact kernelAt_completedSquare_eq_zero_of_neg_fixed_translation E H P hP hneg Q

/-- 奇数核の非零点を半核代表として選んだ場合の、局所評価パケットの
仮定を `hnegTranslation` なしで供給する公開版。 -/
theorem completedSquare_translation_pair_of_odd_kernel
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) (hQ : Q ≠ 0) :
    (2 * (P + Q.val).yc + (E⁄(AlgebraicClosure K)).a₁ * (P + Q.val).xc +
        (E⁄(AlgebraicClosure K)).a₃ ≠ 0) ∧
      (2 * kernelYAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₁ * kernelXAt E H (P + Q.val)
          (add_not_mem_kernel E H P hP Q) +
        (kernelModel E H).a₃ = 0) := by
  exact completedSquare_translation_pair E H P hP hneg Q
    (neg_ne_of_odd_kernel_twoTorsion_translate E H hodd P hneg Q hQ)

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
