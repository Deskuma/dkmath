/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.Algebra.FiniteProductWronskian
import DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskian

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianAssembly"

/-!
# Vélu 補正族の共通分母 Wronskian

前段の一対補正恒等式を、有限添字族へ持ち上げる。各添字 `i` に対して

`Nᵢ = xCorrectionNumerator W (a i) (b i)`、
`Dᵢ = xCorrectionDenominator (a i)`、
`Zᵢ = (X-C(a i)) * zCorrectionNumerator W (a i) (b i)`

と置くと、一般有限積補題の局所項
`Nᵢ' Dᵢ - Nᵢ Dᵢ'` を `Zᵢ` へ置き換えられる。本ファイルはこの代入だけを
担当し、半核の選択、関数体への係数写像、二捩れ点での評価はまだ仮定しない。
-/

namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel

open Polynomial
open WeierstrassCurve
open scoped BigOperators
open DkMath.Lib.Algebra.FiniteProductWronskian
open DkMath.Lib.NumberTheory.WeierstrassVeluPair

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- Vélu 一対補正の有限族に対する共通分母 Wronskian 恒等式。

`A = X∏ᵢDᵢ + ΣᵢNᵢEᵢ` の Wronskian は、単純な分母項と
`Eᵢ² (X-C(aᵢ)) Zᵢ` の有限和へ分解される。 -/
theorem finite_xCorrection_wronskian_eq
    (s : Finset ι) (W : WeierstrassCurve F)
    (a b : ι → F) :
    (commonNumerator s
        (fun i => xCorrectionNumerator W (a i) (b i))
        (fun i => xCorrectionDenominator (a i))).derivative *
        commonDenominator s (fun i => xCorrectionDenominator (a i)) -
      commonNumerator s
          (fun i => xCorrectionNumerator W (a i) (b i))
          (fun i => xCorrectionDenominator (a i)) *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).derivative =
      (commonDenominator s (fun i => xCorrectionDenominator (a i))) ^ 2 +
        ∑ i ∈ s,
          (erasedProduct s (fun j => xCorrectionDenominator (a j)) i) ^ 2 *
            ((X - C (a i)) * zCorrectionNumerator W (a i) (b i)) := by
  apply commonNumerator_wronskian_eq_of_local
  intro i hi
  exact xCorrection_numerator_wronskian_eq W (a i) (b i)

/-- 有限補正族の Wronskian を `zCorrection` の評価へ戻す。

各 `x-aᵢ` が非零なら、共通分母恒等式の局所項を
`(D(x))² zCorrectionᵢ(x)` へ組み替えられる。これはレビューの式 (3) に
対応するが、まだ標準 `RatFunc` の係数対や二捩れ点を仮定しない純粋な
有限補正族の評価定理である。 -/
theorem finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z
    (s : Finset ι) (W : WeierstrassCurve F)
    (a b : ι → F) (x : F)
    (hxa : ∀ i ∈ s, x ≠ a i) :
    ((commonNumerator s
        (fun i => xCorrectionNumerator W (a i) (b i))
        (fun i => xCorrectionDenominator (a i))).derivative.eval x *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).eval x -
      (commonNumerator s
          (fun i => xCorrectionNumerator W (a i) (b i))
          (fun i => xCorrectionDenominator (a i))).eval x *
        (commonDenominator s (fun i => xCorrectionDenominator (a i))).derivative.eval x) =
      (commonDenominator s (fun i => xCorrectionDenominator (a i))).eval x ^ 2 *
        (1 + ∑ i ∈ s, zCorrection W (a i) (b i) x) := by
  have hpoly := congrArg (fun p : F[X] => p.eval x)
    (finite_xCorrection_wronskian_eq s W a b)
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    Polynomial.eval_finsetSum] at hpoly
  rw [hpoly]
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hfactor := commonDenominator_eq_factor_mul_erasedProduct s
    (fun j => xCorrectionDenominator (a j)) hi
  have hfactor_eval := congrArg (fun p : F[X] => p.eval x) hfactor
  simp only [eval_mul] at hfactor_eval
  have hfactor_eval' :
      (commonDenominator s (fun j => xCorrectionDenominator (a j))).eval x =
        (x - a i) ^ 2 * (erasedProduct s (fun j => xCorrectionDenominator (a j)) i).eval x := by
    calc
      _ = (x - a i) * (x - a i) *
          (erasedProduct s (fun j => xCorrectionDenominator (a j)) i).eval x := by
        simpa [xCorrectionDenominator] using hfactor_eval
      _ = _ := by ring
  rw [hfactor_eval']
  have hz :
      (x - a i) * (zCorrectionNumerator W (a i) (b i)).eval x =
        (x - a i) ^ 4 * zCorrection W (a i) (b i) x := by
    simp [zCorrection, zCorrectionNumerator]
    field_simp [sub_ne_zero.mpr (hxa i hi)]
  rw [hz]
  ring

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
