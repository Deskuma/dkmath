/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.BinomialPrimePower
import Mathlib.Data.Nat.Choose.Lucas

#print "file: DkMath.NumberTheory.PascalPrebirthBoundary"

/-! Exact prime-power synchronization and the maximal common Pascal modulus.
The common divisor below is unrelated to exponent reduction in PowerGauge. -/

namespace DkMath.NumberTheory

/-- The exact inner interval used by Mathlib's Pascal gcd classification. -/
def pascalInnerCommonDivisor (N : ℕ) : ℕ :=
  (Finset.Icc 1 (N - 1)).gcd (Nat.choose N)

/-- Divisors of the inner gcd are exactly common inner-row moduli. -/
theorem dvd_pascalInnerCommonDivisor_iff (N m : ℕ) :
    m ∣ pascalInnerCommonDivisor N ↔ AllInnerChooseDivisible N m := by
  rw [pascalInnerCommonDivisor, Finset.dvd_gcd_iff]
  constructor
  · intro H k hk0 hkN
    exact H k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro H k hk
    obtain ⟨hk0, hkN⟩ := Finset.mem_Icc.mp hk
    exact H k (by omega) (by omega)

/-- The gcd is the maximal common cancellation modulus of the preceding row. -/
theorem pascalPrebirthAlternationMod_iff_dvd_commonDivisor (d m : ℕ) :
    PascalPrebirthAlternationMod d m ↔ m ∣ pascalInnerCommonDivisor (d + 1) := by
  rw [dvd_pascalInnerCommonDivisor_iff, pascalPrebirthAlternationMod_iff_allInnerChooseDivisible]

/-- Lucas classifies common prime support by a positive power witness. -/
theorem allInnerChooseDivisible_prime_iff {N p : ℕ} (hp : p.Prime) (hN : 1 < N) :
    AllInnerChooseDivisible N p ↔ ∃ a, 0 < a ∧ N = p ^ a := by
  constructor
  · intro H
    let : Fact p.Prime := ⟨hp⟩
    have heq := Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (by omega : 0 < N)
      (p := p) (fun k hk => Nat.modEq_zero_iff_dvd.mpr
        (H k (by have := (Finset.mem_Icc.mp hk).1; omega)
          (by have := (Finset.mem_Icc.mp hk).2; omega)))
    refine ⟨multiplicity p N, ?_, heq⟩
    by_contra ha
    have hz : multiplicity p N = 0 := by omega
    simp [hz] at heq
    omega
  · rintro ⟨a, _, rfl⟩
    exact prime_power_allInnerChooseDivisible hp

/-- Alternating unit residues predict exactly a positive prime-power next row. -/
theorem pascalPrebirthAlternationMod_prime_iff {d p : ℕ}
    (hp : p.Prime) (hd : 1 < d + 1) :
    PascalPrebirthAlternationMod d p ↔ ∃ a, 0 < a ∧ d + 1 = p ^ a := by
  rw [pascalPrebirthAlternationMod_iff_allInnerChooseDivisible]
  exact allInnerChooseDivisible_prime_iff hp hd

/-- Prime powers have their base prime as common inner gcd. -/
theorem pascalInnerCommonDivisor_eq_minFac {N : ℕ} (h : IsPrimePow N) :
    pascalInnerCommonDivisor N = N.minFac :=
  Choose.gcd_choose_eq_minFac_of_isPrimePow h

/-- A non-prime-power row above one has no nontrivial common modulus. -/
theorem pascalInnerCommonDivisor_eq_one {N : ℕ} (hN : 1 < N) (h : ¬ IsPrimePow N) :
    pascalInnerCommonDivisor N = 1 :=
  Choose.gcd_choose_eq_one_of_not_isPrimePow hN h

/-- Prime rows have their row number as common inner gcd. -/
theorem pascalInnerCommonDivisor_eq_self_of_prime {N : ℕ} (h : N.Prime) :
    pascalInnerCommonDivisor N = N := by
  rw [pascalInnerCommonDivisor_eq_minFac h.isPrimePow, h.minFac_eq]

/-- The previously open row-number common-divisibility converse. -/
theorem prime_iff_allInnerChooseDivisible_self {N : ℕ} (hN : 1 < N) :
    N.Prime ↔ AllInnerChooseDivisible N N := by
  constructor
  · exact prime_allInnerChooseDivisible_self
  · intro H
    have hdiv := (dvd_pascalInnerCommonDivisor_iff N N).mpr H
    by_cases hpow : IsPrimePow N
    · rw [pascalInnerCommonDivisor_eq_minFac hpow] at hdiv
      have heq : N.minFac = N := Nat.le_antisymm
        (Nat.minFac_le (by omega)) (Nat.le_of_dvd (Nat.minFac_pos N) hdiv)
      rw [← heq]
      exact Nat.minFac_prime (by omega)
    · rw [pascalInnerCommonDivisor_eq_one hN hpow] at hdiv
      have := Nat.le_of_dvd (by omega : 0 < 1) hdiv
      omega

/-- Above one, equality of the common gcd and row number characterizes primes. -/
theorem pascalInnerCommonDivisor_eq_self_iff {N : ℕ} (hN : 1 < N) :
    pascalInnerCommonDivisor N = N ↔ N.Prime := by
  constructor
  · intro h
    apply (prime_iff_allInnerChooseDivisible_self hN).mpr
    apply (dvd_pascalInnerCommonDivisor_iff _ _).mp
    rw [h]
  · exact pascalInnerCommonDivisor_eq_self_of_prime

/-- Primality is exactly the row-number prebirth alternating phase. -/
theorem prime_iff_prebirthAlternation_self {N : ℕ} (hN : 1 < N) :
    N.Prime ↔ PascalPrebirthAlternationMod (N - 1) N := by
  rw [pascalPrebirthAlternationMod_iff_allInnerChooseDivisible,
    Nat.sub_add_cancel (by omega : 1 ≤ N)]
  exact prime_iff_allInnerChooseDivisible_self hN

/-- Positive powers have their given base prime as common modulus. -/
theorem pascalInnerCommonDivisor_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    pascalInnerCommonDivisor (p ^ a) = p := by
  have hpow : IsPrimePow (p ^ a) := (isPrimePow_nat_iff _).mpr ⟨p, a, hp, ha, rfl⟩
  rw [pascalInnerCommonDivisor_eq_minFac hpow]
  have hmin := Nat.minFac_prime hpow.ne_one
  exact (Nat.prime_dvd_prime_iff_eq hmin hp).mp
    (hmin.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ a)))

end DkMath.NumberTheory
