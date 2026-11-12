/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.RationalPrimeDenominator
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.ValuationPrimeExistence

#print "file: DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport"

/-!
# 素数住所を持つ任意の延長付値環と、有理数の分母

[DkMath.Lib] q上の付値環Aの値群を正規化せず、有理数のA所属を既約分母で判定する。
分母がqで割れれば分子はAの単元、分母は非単元となり、有理数はAに入れない。
分母がqで割れなければその逆数をA内で使用できる。
-/
namespace DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
open ValuationPrimeSupport RationalPrimeDenominator
variable {K : Type*} [Field K] [CharZero K]

/-- [DkMath.Lib] q上の任意の延長付値環における有理数の整性は、同じ分母の非可除性と同値。 -/
theorem ratCast_mem_iff (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) (r : ℚ) : (r : K) ∈ A ↔ ¬ q ∣ r.den := by
  have hr : (r : K) = (r.num : K) / (r.den : K) := Rat.cast_def r
  constructor
  · intro hm hd
    have hn : A.valuation (r.num : K) = 1 :=
      valuation_intCast_eq_one_of_not_dvd A hq hA (not_dvd_num_of_dvd_den r hq hd)
    have hdv : A.valuation (r.den : K) < 1 := by
      simpa only [Int.cast_natCast] using valuation_intCast_lt_one_of_dvd A hA (z := (r.den : ℤ)) (by exact_mod_cast hd)
    have he : (r.num : K) = (r : K) * (r.den : K) := by
      rw [hr, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr r.den_ne_zero)]
    have hlt : A.valuation (r.num : K) < 1 := by
      rw [he, map_mul]
      exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr hm)).trans_lt hdv
    exact hn.not_lt hlt
  · intro hd
    have hdv : A.valuation (r.den : K) = 1 := by
      simpa only [Int.cast_natCast] using
        valuation_intCast_eq_one_of_not_dvd A hq hA (z := (r.den : ℤ)) (by exact_mod_cast hd)
    apply (A.valuation_le_one_iff _).mp
    rw [hr, map_div₀, hdv, div_one]
    exact (A.valuation_le_one_iff _).mpr (intCast_mem A r.num)

/-- [DkMath.Lib] 同じ延長付値環への有理数の所属は、通常のq進整数位数の非負性と同値。 -/
theorem ratCast_mem_iff_padicValRat_nonneg (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) (r : ℚ) : (r : K) ∈ A ↔ 0 ≤ padicValRat q r :=
  (ratCast_mem_iff A hq hA r).trans (padicValRat_nonneg_iff r hq).symm

/-- [DkMath.Lib] q上の全ての延長付値環への所属と、有理数のq進局所整性は同値。
逆向きには指定したq上の付値環を内部構成するため、全称条件の空虚性は使わない。 -/
theorem all_valuation_mem_iff {q : ℕ} (hq : q.Prime) (r : ℚ) :
    (∀ A : ValuationSubring K, ValuationInertia.LiesOverPrime A q → (r : K) ∈ A) ↔
      0 ≤ padicValRat q r := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := K) hq
    exact (ratCast_mem_iff_padicValRat_nonneg A hq ((ValuationSubring.mem_nonunits_iff _).mp hA) r).mp
      (h A hA)
  · intro h A hA
    exact (ratCast_mem_iff_padicValRat_nonneg A hq ((ValuationSubring.mem_nonunits_iff _).mp hA) r).mpr h

/-- [DkMath.Lib] p以外の全ての素数住所で整なら、同じ有理数の分母はp冪である。 -/
theorem den_eq_pow_of_all_valuation_mem (r : ℚ) (p : ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ A : ValuationSubring K, ValuationInertia.LiesOverPrime A q → (r : K) ∈ A) :
    ∃ e : ℕ, r.den = p ^ e :=
  exists_den_eq_pow r p (fun q hq hqp => (all_valuation_mem_iff (K := K) hq r).mp (h q hq hqp))

omit [CharZero K] in
/-- [DkMath.Lib] q以外の素数pの冪は、q上の同じ延長付値環で単元付値1となる。 -/
theorem prime_power_value_one (A : ValuationSubring K) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) (hqp : q ≠ p) (e : ℕ) : A.valuation ((p : K) ^ e) = 1 := by
  have hu : A.valuation (p : K) = 1 := by
    simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq hA (z := (p : ℤ)) (by
      intro h; exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast h)))
  rw [map_pow, hu, one_pow]

end DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
