/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadratic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

#print "file: DkMath.Lib.NumberTheory.EisensteinCyclotomic"

/-!
# Eisenstein 座標と三次円分整数環

`τ²=τ−1` という座標規約を `τ ↦ 1+ζ` で円分整数環へ送る。
逆写像は整数冪基底 `1,ζ` の普遍性から作り、`ζ ↦ τ²` とする。
両合成が恒等写像であることを証明するので、ノルムだけの比較ではなく、
元・積・冪・単元を運べる環同型である。FLT の仮定は使用しない。
-/

namespace DkMath.Lib.NumberTheory

open NumberField
open DkMath.NumberTheory.TraceOneQuadratic

/-- 二次関係を満たす元で Eisenstein 座標を評価する。 -/
def eisensteinEval {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = t - 1) :
    TraceOneInt (-1) →+* R where
  toFun x := (x.fst : R) + (x.snd : R) * t
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp only [fst_add, snd_add, Int.cast_add]; ring
  map_mul' x y := by
    simp only [fst_mul, snd_mul, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one]
    linear_combination -(x.snd : R) * (y.snd : R) * ht

variable {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {3} ℚ K] {ζ : K}

omit [IsCyclotomicExtension {3} ℚ K] [CharZero K] in
/-- 三次の `1+ζ` は六乗根型の二次関係を満たす。 -/
theorem one_add_cubic_root_sq (hζ : IsPrimitiveRoot ζ 3) :
    (1 + hζ.toInteger) ^ 2 = (1 + hζ.toInteger) - 1 := by
  have hz : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 := by
    apply RingOfIntegers.coe_injective
    change ζ ^ 2 + ζ + 1 = 0
    simpa [Polynomial.cyclotomic_three] using hζ.isRoot_cyclotomic (by decide)
  linear_combination hz

/-- `r+sτ ↦ r+s(1+ζ)`。 -/
def eisensteinToCyclotomic (hζ : IsPrimitiveRoot ζ 3) :
    TraceOneInt (-1) →+* 𝓞 K :=
  eisensteinEval (1 + hζ.toInteger) (one_add_cubic_root_sq hζ)

omit [IsCyclotomicExtension {3} ℚ K] in
private theorem cubic_minpoly (hζ : IsPrimitiveRoot ζ 3) :
    minpoly ℤ hζ.toInteger = Polynomial.cyclotomic 3 ℤ := by
  rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
    RingOfIntegers.coe_injective hζ.toInteger]
  exact (Polynomial.cyclotomic_eq_minpoly hζ (by decide)).symm

omit [IsCyclotomicExtension {3} ℚ K] in
private theorem eisenstein_cubic_root_aeval (hζ : IsPrimitiveRoot ζ 3) :
    Polynomial.aeval (tau (-1) ^ 2) (minpoly ℤ hζ.toInteger) = 0 := by
  rw [cubic_minpoly hζ, Polynomial.cyclotomic_three]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext <;> norm_num [tau, pow_succ]

/-- 整数冪基底を使った逆写像。`ζ` を `τ²` に送る。 -/
noncomputable def cyclotomicToEisenstein (hζ : IsPrimitiveRoot ζ 3) :
    𝓞 K →ₐ[ℤ] TraceOneInt (-1) :=
  hζ.integralPowerBasis.lift
    (tau (-1) ^ 2) (by simpa using eisenstein_cubic_root_aeval hζ)

/-- 逆写像の生成元での値。 -/
@[simp] theorem cyclotomicToEisenstein_root (hζ : IsPrimitiveRoot ζ 3) :
    cyclotomicToEisenstein hζ hζ.toInteger = tau (-1) ^ 2 := by
  unfold cyclotomicToEisenstein
  conv_lhs => arg 2; rw [← hζ.integralPowerBasis_gen]
  exact hζ.integralPowerBasis.lift_gen _ _

/-- 座標環と三次円分整数環の環同型。写像と逆写像の両方を固定する。 -/
noncomputable def eisensteinCyclotomicEquiv (hζ : IsPrimitiveRoot ζ 3) :
    TraceOneInt (-1) ≃+* 𝓞 K := by
  let f := eisensteinToCyclotomic hζ
  let g := cyclotomicToEisenstein hζ
  refine RingEquiv.ofRingHom f g.toRingHom ?_ ?_
  · have hfg : f.toIntAlgHom.comp g = AlgHom.id ℤ (𝓞 K) := by
      apply hζ.integralPowerBasis.algHom_ext
      rw [hζ.integralPowerBasis_gen]
      change f (g hζ.toInteger) = hζ.toInteger
      rw [cyclotomicToEisenstein_root]
      norm_num [f, eisensteinToCyclotomic, eisensteinEval, tau, pow_two]
    exact congrArg AlgHom.toRingHom hfg
  · apply RingHom.ext
    intro x
    change g ((x.fst : 𝓞 K) + (x.snd : 𝓞 K) * (1 + hζ.toInteger)) = x
    simp only [map_add, map_mul, map_intCast, map_one,
      show g hζ.toInteger = tau (-1) ^ 2 from cyclotomicToEisenstein_root hζ]
    change (⟨x.fst, 0⟩ : TraceOneInt (-1)) + ⟨x.snd, 0⟩ * (1 + tau (-1) ^ 2) = x
    ext <;> simp [tau, pow_two]

/-- 同型の計算規則。これにより元の座標の来歴を追跡できる。 -/
@[simp] theorem eisensteinCyclotomicEquiv_apply (hζ : IsPrimitiveRoot ζ 3)
    (x : TraceOneInt (-1)) :
    eisensteinCyclotomicEquiv hζ x = (x.fst : 𝓞 K) + (x.snd : 𝓞 K) * (1 + hζ.toInteger) := rfl

end DkMath.Lib.NumberTheory
