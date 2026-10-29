/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianHalf

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase"

/-!
# 半核共通分母の係数体を代数閉包へ戻す

`EllipticFiniteKernelWronskianHalf` の共通分母は、評価を直接行うために
関数体係数で定義されている。このファイルでは、同じ有限積をまず
`AlgebraicClosure K[X]` 上に作り、その係数写像で関数体版へ送る。
以後の `RatFunc` 係数対との比較は、この基礎体側の多項式を使う。
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
open DkMath.Lib.Algebra.RationalPolynomialFiber

variable {K : Type*} [Field K]

noncomputable local instance instDecidableEqEllipticFiniteKernelWronskianBase
    {α : Type*} : DecidableEq α := Classical.decEq _

/-- 代数閉包係数で作った半核共通分子。 -/
noncomputable def veluHalfNumeratorBase
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    (AlgebraicClosure K)[X] :=
  let W := E.map (algebraMap K (AlgebraicClosure K))
  commonNumerator (halfKernel E H)
    (fun Q => xCorrectionNumerator W Q.val.xc Q.val.yc)
    (fun Q => xCorrectionDenominator Q.val.xc)

/-- 代数閉包係数で作った半核共通分母。 -/
noncomputable def veluHalfDenominatorBase
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    (AlgebraicClosure K)[X] :=
  commonDenominator (halfKernel E H)
    (fun Q => xCorrectionDenominator Q.val.xc)

/-! `moments_map` が局所補正の係数写像を供給する。 -/

theorem map_xCorrectionNumerator_base
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E))
    (Q : H) :
    let q : (E.toAffine⁄(AlgebraicClosure K)).Point := Q.val
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let W₀ := E.map (algebraMap K (AlgebraicClosure K))
    let W := E.map (algebraMap K F)
    let c := algebraMap (AlgebraicClosure K) F
    Polynomial.map (algebraMap (AlgebraicClosure K) F)
        (xCorrectionNumerator W₀ q.xc q.yc) =
      xCorrectionNumerator W (c q.xc) (c q.yc) := by
  dsimp only
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let W₀ := E.map (algebraMap K (AlgebraicClosure K))
  let W := E.map (algebraMap K F)
  let c := algebraMap (AlgebraicClosure K) F
  let q : (E.toAffine⁄(AlgebraicClosure K)).Point := Q.val
  have h₁ : c W₀.a₁ = W.a₁ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₁).symm
  have h₃ : c W₀.a₃ = W.a₃ := by
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F E.a₃).symm
  have hm := (moments_map (algebraMap (AlgebraicClosure K) F) W₀
    q.xc q.yc).1
  have hW : W₀.map c = W := by
    ext <;> dsimp [W₀, W, c]
    all_goals exact IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F _
  rw [hW] at hm
  dsimp [W₀, W, c, q] at hm h₁ h₃ ⊢
  simp only [xCorrectionNumerator, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_pow, map_pow, map_add, map_mul, map_ofNat]
  have htwo : Polynomial.map c (2 : (AlgebraicClosure K)[X]) =
      (2 : F[X]) := by
    norm_num
  rw [htwo]
  rw [← hm, h₁, h₃]

theorem map_xCorrectionDenominator_base
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E))
    (Q : H) :
    let q : (E.toAffine⁄(AlgebraicClosure K)).Point := Q.val
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let c := algebraMap (AlgebraicClosure K) F
    Polynomial.map c (xCorrectionDenominator q.xc) =
      xCorrectionDenominator (c q.xc) := by
  dsimp only
  simp [xCorrectionDenominator]

theorem map_veluHalfNumeratorBase
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let c := algebraMap (AlgebraicClosure K) F
    Polynomial.map c (veluHalfNumeratorBase E H) = veluHalfNumerator E H := by
  classical
  dsimp only
  unfold veluHalfNumeratorBase veluHalfNumerator commonNumerator
    commonDenominator erasedProduct
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_prod]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· * ·)
    · rfl
    · apply Finset.prod_congr rfl
      intro Q hQ
      rw [map_xCorrectionDenominator_base E H Q]
  · apply Finset.sum_congr rfl
    intro Q hQ
    apply congrArg₂ (· * ·)
    · exact map_xCorrectionNumerator_base E H Q
    · apply Finset.prod_congr rfl
      intro R hR
      rw [map_xCorrectionDenominator_base E H R]

theorem map_veluHalfDenominatorBase
    (E : WeierstrassCurve K) (H : AddSubgroup (Points E)) [Fintype H] :
    let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
    let c := algebraMap (AlgebraicClosure K) F
    Polynomial.map c (veluHalfDenominatorBase E H) = veluHalfDenominator E H := by
  classical
  dsimp only
  unfold veluHalfDenominatorBase veluHalfDenominator commonDenominator
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro Q hQ
  exact map_xCorrectionDenominator_base E H Q

/-! 微分は係数写像と可換する。これにより、基礎体係数で作った
Wronskian を関数体係数の Wronskianへ移す最後の代数段が明示される。 -/

theorem map_wronskian
    {R S : Type*} [Field R] [Field S] (f : R →+* S)
    (P Q : R[X]) :
    Polynomial.map f (wronskian P Q) =
      wronskian (Polynomial.map f P) (Polynomial.map f Q) := by
  unfold wronskian
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    derivative_map, derivative_map]

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
