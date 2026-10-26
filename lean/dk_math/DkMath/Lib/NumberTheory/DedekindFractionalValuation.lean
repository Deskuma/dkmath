/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization

#print "file: DkMath.Lib.NumberTheory.DedekindFractionalValuation"

/-!
# 分数イデアルの指数と、生成関数の離散付値

[DkMath.Lib] Dedekind整域の非零分数イデアルは、全ての高さ1素点での整数指数で決まる。
主分数イデアル(f)の指数は、同じfの正規化付値の負の対数である。
これにより、点での零・極の情報を、座標環の類群が扱う実際の分数イデアルへ戻す。
-/
namespace DkMath.Lib.NumberTheory.DedekindFractionalValuation
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors
variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- [DkMath.Lib] 全素点での指数が一致する二つの非零分数イデアルは等しい。 -/
theorem ext_count {I J : FractionalIdeal R⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count F v I = FractionalIdeal.count F v J) :
    I = J := by
  calc
    I = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^
        FractionalIdeal.count F v I := (FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI).symm
    _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^
        FractionalIdeal.count F v J := finprod_congr fun v => congrArg
      (fun n : ℤ => (v.asIdeal : FractionalIdeal R⁰ F) ^ n) (h v)
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ

/-- [DkMath.Lib] 主分数イデアル(f)の素点指数は、同じ非零関数fの付値の負の対数。
f=a/bへ戻し、分子・分母のイデアル指数の差と付値の商を比較する。 -/
theorem count_spanSingleton (v : HeightOneSpectrum R) (f : F) (hf : f ≠ 0) :
    FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ f) = -log (v.valuation F f) := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have hb0 : (algebraMap R F) b ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R F) hb
  have ha0 : a ≠ 0 := by intro ha; exact hf (by rw [ha, map_zero, zero_div])
  have hI : FractionalIdeal.spanSingleton R⁰ ((algebraMap R F) a / (algebraMap R F) b) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R F) b)⁻¹ * (Ideal.span {a} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) hI,
    map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_if_neg _ ha0, intValuation_if_neg _ (nonZeroDivisors.ne_zero hb),
    log_div (by exact exp_ne_zero) (by exact exp_ne_zero), log_exp, log_exp]
  omega

end DkMath.Lib.NumberTheory.DedekindFractionalValuation
