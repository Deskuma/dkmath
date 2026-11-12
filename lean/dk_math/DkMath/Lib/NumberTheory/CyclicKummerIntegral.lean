/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclicKummer
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Integral

#print "file: DkMath.Lib.NumberTheory.CyclicKummerIntegral"

/-!
# 同じ Kummer 表示の冪による整数化

非零の底体元 `c` によって根を `c α`、定数を `c^p b` に変える。
生成する同じ体と既約性を保ち、数体では整数の分母払いから
根・定数の両方を代数的整数にできる。底体の単元であることは主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclicKummerIntegral

open CyclicKummer Polynomial
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F M : Type*} [Field F] [Field M] [Algebra F M]
    (P : Presentation p F M)

/-- 同じ体・同じ包含での根の非零スカラー倍。 -/
def rescale (c : F) (hc : c ≠ 0) : Presentation p F M where
  radical := algebraMap F M c * P.radical
  constant := c ^ p * P.constant
  radical_pow := by rw [mul_pow, P.radical_pow, map_mul, map_pow]
  adjoin_eq_top := by
    rw [mul_comm, IntermediateField.adjoin_simple_mul_algebraMap P.radical c hc, P.adjoin_eq_top]
  irreducible := by
    apply (X_pow_sub_C_irreducible_iff_of_prime (Fact.out : p.Prime)).mpr
    intro z hz
    apply P.constant_not_pow (Fact.out : p.Prime).ne_one (z / c)
    rw [div_pow, hz]
    exact mul_div_cancel_left₀ _ (pow_ne_zero p hc)

theorem rescale_radical (c : F) (hc : c ≠ 0) :
    (rescale P c hc).radical = algebraMap F M c * P.radical := rfl

theorem rescale_constant (c : F) (hc : c ≠ 0) :
    (rescale P c hc).constant = c ^ p * P.constant := rfl

/-- 数体の任意の元は、整数の非零分母を掛ければ整になる。 -/
theorem exists_integral_multiple [NumberField F] (b : F) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : F) * b) := by
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (R := ℤ) (Rₘ := ℚ) (M := nonZeroDivisors ℤ) b (IsIntegral.of_finite ℚ b)
  refine ⟨d.val, nonZeroDivisors.ne_zero d.property, ?_⟩
  simp only [Submonoid.smul_def, Algebra.smul_def, algebraMap_int_eq] at hd
  exact hd

/-- 分母の `p` 乗で定数を払う。これにより同じ Kummer 類を保てる。 -/
theorem exists_integral_power_multiple [NumberField F] (b : F) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : F) ^ p * b) := by
  obtain ⟨d, hd, hi⟩ := exists_integral_multiple b
  have hdint : IsIntegral ℤ (d : F) := isIntegral_algebraMap
  refine ⟨d, hd, ?_⟩
  have h := (hdint.pow (p - 1)).mul hi
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos] at h
  exact h

/-- 整数化された表示も同じ `M/F` にある。根と定数の整性を同時に供給する。 -/
theorem exists_integral_rescale [NumberField F] :
    ∃ (d : ℤ) (hd : (d : F) ≠ 0),
      IsIntegral ℤ (rescale P (d : F) hd).constant ∧
      IsIntegral ℤ (rescale P (d : F) hd).radical := by
  obtain ⟨d, hd, hb⟩ := exists_integral_power_multiple (p := p) P.constant
  have hc : (d : F) ≠ 0 := Int.cast_ne_zero.mpr hd
  refine ⟨d, hc, hb, ?_⟩
  apply IsIntegral.of_pow (Fact.out : p.Prime).pos
  rw [(rescale P (d : F) hc).radical_pow]
  exact hb.algebraMap

/-- 元の表示との整数スカラーによる関係を保った、実際の整数環の元。 -/
structure IntegralModel where
  denominator : ℤ
  denominator_ne_zero : (denominator : F) ≠ 0
  constant : NumberField.RingOfIntegers F
  radical : NumberField.RingOfIntegers M
  constant_eq : (constant : F) = (rescale P (denominator : F) denominator_ne_zero).constant
  radical_eq : (radical : M) = (rescale P (denominator : F) denominator_ne_zero).radical

namespace IntegralModel

variable {P} (D : IntegralModel P)

/-- 同じ体上で元の表示を整数スカラー倍した表示。 -/
def presentation : Presentation p F M := rescale P (D.denominator : F) D.denominator_ne_zero

/-- 同じ整数環の元も、元の包含の上で同じ Kummer 方程式を満たす。 -/
theorem radical_pow : (D.radical : M) ^ p = algebraMap F M (D.constant : F) := by
  rw [D.radical_eq, D.constant_eq]
  exact (rescale P (D.denominator : F) D.denominator_ne_zero).radical_pow

theorem constant_ne_zero : D.constant ≠ 0 := by
  intro h
  have hz := congrArg (fun b : NumberField.RingOfIntegers F => (b : F)) h
  exact D.presentation.constant_ne_zero (Fact.out : p.Prime).one_lt (D.constant_eq.symm.trans hz)

theorem radical_ne_zero : D.radical ≠ 0 := by
  intro h
  have hz := congrArg (fun a : NumberField.RingOfIntegers M => (a : M)) h
  exact D.presentation.radical_ne_zero (Fact.out : p.Prime).one_lt (D.radical_eq.symm.trans hz)

end IntegralModel

/-- 整数代表も同じ表示から内部構成し、その関係式を保存する。 -/
theorem exists_integral_model [NumberField F] : Nonempty (IntegralModel P) := by
  obtain ⟨d, hd, hb, hα⟩ := exists_integral_rescale P
  exact ⟨⟨d, hd, ⟨_, hb⟩, ⟨_, hα⟩, rfl, rfl⟩⟩

end
end DkMath.Lib.NumberTheory.CyclicKummerIntegral
