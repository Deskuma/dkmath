/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianAssembly

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianHalf"

/-!
# 実際の半核への共通分母特殊化

有限積 Wronskian の一般補題を、`halfKernel E H` の各点へ代入する。
`veluX_half` の既存表示と、評価された共通分母分数和を比較することで、
Vélu x 座標を明示的な `A_H / D_H` 表示へ接続する。

ここではまだ二捩れ点、標準 `RatFunc` 係数対、幾何学的 Wronskian 零点は
扱わない。必要な分母非零性は `genericX_ne_const` から関数体上で供給する。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped BigOperators
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.NumberTheory.EllipticFunctionField
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.WeierstrassVeluPair
open DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial

variable {K : Type*} [Field K]

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianHalf
    {α : Type*} : DecidableEq α := Classical.decEq _

/-- 半核補正項の分子族を関数体上で構成する。 -/
noncomputable def veluHalfNumerator
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    ((E.toAffine⁄(AlgebraicClosure K)).FunctionField)[X] :=
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let c := algebraMap (AlgebraicClosure K) F
  commonNumerator (halfKernel E H)
    (fun Q => xCorrectionNumerator W (c Q.val.xc) (c Q.val.yc))
    (fun Q => xCorrectionDenominator (c Q.val.xc))

/-- 半核補正項の共通分母を関数体上で構成する。 -/
noncomputable def veluHalfDenominator
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    ((E.toAffine⁄(AlgebraicClosure K)).FunctionField)[X] :=
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let c := algebraMap (AlgebraicClosure K) F
  commonDenominator (halfKernel E H)
    (fun Q => xCorrectionDenominator (c Q.val.xc))

/-- `genericX` は各半核点の x 座標と異なるため、半核分母の各因子は非零。 -/
theorem veluHalf_denominator_factor_ne_zero
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    [E.IsElliptic] (Q : halfKernel E H) :
    (xCorrectionDenominator
        (algebraMap (AlgebraicClosure K)
          (E.toAffine⁄(AlgebraicClosure K)).FunctionField Q.val.val.xc)).eval
      (genericX E (AlgebraicClosure K)) ≠ 0 := by
  simp only [xCorrectionDenominator, eval_mul, eval_sub, eval_X, eval_C]
  exact mul_ne_zero (sub_ne_zero.mpr (genericX_ne_const E Q.val.val.xc))
    (sub_ne_zero.mpr (genericX_ne_const E Q.val.val.xc))

/-- `veluX_half` を明示的共通分母 `A_H / D_H` へ輸送する。 -/
theorem veluX_eq_veluHalfNumerator_div_denominator
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) [E.IsElliptic] :
    veluX E H =
      (veluHalfNumerator E H).eval (genericX E (AlgebraicClosure K)) /
        (veluHalfDenominator E H).eval (genericX E (AlgebraicClosure K)) := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let c := algebraMap (AlgebraicClosure K) F
  let x := genericX E (AlgebraicClosure K)
  have hD : ∀ Q : H, Q ∈ halfKernel E H →
      (xCorrectionDenominator (c Q.val.xc)).eval x ≠ 0 := by
    intro Q hQ
    exact veluHalf_denominator_factor_ne_zero E H ⟨Q, hQ⟩
  have hsum := commonNumerator_eval_div_commonDenominator
    (K := F) (halfKernel E H)
    (fun Q => xCorrectionNumerator W (c Q.val.xc) (c Q.val.yc))
    (fun Q => xCorrectionDenominator (c Q.val.xc)) x hD
  have hcorr : ∀ Q : H,
      let q : (E.toAffine⁄(AlgebraicClosure K)).Point := Q.val
      xCorrection W (c q.xc) (c q.yc) x =
        (xCorrectionNumerator W (c q.xc) (c q.yc)).eval x /
          (xCorrectionDenominator (c q.xc)).eval x := by
    intro Q
    let q : (E.toAffine⁄(AlgebraicClosure K)).Point := Q.val
    have hxa : x ≠ c q.xc := genericX_ne_const E q.xc
    exact xCorrection_eq_eval_numerator_div_denominator W
      hxa
  have hv := veluX_half E H ho
  calc
    veluX E H = x + ∑ Q ∈ halfKernel E H,
        xCorrection W (c Q.val.xc) (c Q.val.yc) x := by
      simpa [F, W, c, x] using hv
    _ = x + ∑ Q ∈ halfKernel E H,
        (xCorrectionNumerator W (c Q.val.xc) (c Q.val.yc)).eval x /
          (xCorrectionDenominator (c Q.val.xc)).eval x := by
      congr 1
      apply Finset.sum_congr rfl
      intro Q hQ
      exact congrArg id (hcorr Q)
    _ = (veluHalfNumerator E H).eval x /
        (veluHalfDenominator E H).eval x := by
      simpa [veluHalfNumerator, veluHalfDenominator, F, W, c, x] using hsum.symm

/-! The next identity is the denominator-cleared bridge to `veluZ_half`.
It is still a function-field identity: no point evaluation or two-torsion
geometry is used here. -/

/-- 共通分母 Wronskian と Vélu の平方完成座標を接続する無分母恒等式。 -/
theorem veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H]
    (ho : Odd (Nat.card H)) [E.IsElliptic] :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let W := E.map (algebraMap K F)
    let x := genericX E (AlgebraicClosure K)
    let z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
    (veluHalfDenominator E H).eval x ^ 2 *
        (2 * veluY E H + W.a₁ * veluX E H + W.a₃) =
      z * ((veluHalfNumerator E H).derivative.eval x *
          (veluHalfDenominator E H).eval x -
        (veluHalfNumerator E H).eval x *
          (veluHalfDenominator E H).derivative.eval x) := by
  dsimp only
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W := E.map (algebraMap K F)
  let x := genericX E (AlgebraicClosure K)
  let z := 2 * genericY E (AlgebraicClosure K) + W.a₁ * x + W.a₃
  let c := algebraMap (AlgebraicClosure K) F
  let a : H → F := fun Q => c Q.val.xc
  let b : H → F := fun Q => c Q.val.yc
  have hxa : ∀ i ∈ halfKernel E H, x ≠ a i := by
    intro i hi
    exact genericX_ne_const E i.val.xc
  have hw := finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z
    (halfKernel E H) W a b x hxa
  have hw' :
      (veluHalfNumerator E H).derivative.eval x *
          (veluHalfDenominator E H).eval x -
        (veluHalfNumerator E H).eval x *
          (veluHalfDenominator E H).derivative.eval x =
        (veluHalfDenominator E H).eval x ^ 2 *
          (1 + ∑ i ∈ halfKernel E H, zCorrection W (a i) (b i) x) := by
    simpa [a, b, veluHalfNumerator, veluHalfDenominator, F, W, c, x] using hw
  have hz := veluZ_half E H ho
  have hz' :
      2 * veluY E H + W.a₁ * veluX E H + W.a₃ =
        z * (1 + ∑ i ∈ halfKernel E H, zCorrection W (a i) (b i) x) := by
    simpa [a, b, F, W, c, x, z] using hz
  calc
    (veluHalfDenominator E H).eval x ^ 2 *
          (2 * veluY E H + W.a₁ * veluX E H + W.a₃) =
        (veluHalfDenominator E H).eval x ^ 2 *
          (z * (1 + ∑ i ∈ halfKernel E H, zCorrection W (a i) (b i) x)) := by
      rw [hz']
    _ = z * ((veluHalfDenominator E H).eval x ^ 2 *
          (1 + ∑ i ∈ halfKernel E H, zCorrection W (a i) (b i) x)) := by
      ring
    _ = z * ((veluHalfNumerator E H).derivative.eval x *
          (veluHalfDenominator E H).eval x -
        (veluHalfNumerator E H).eval x *
          (veluHalfDenominator E H).derivative.eval x) := by
      rw [hw']

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
