/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSmallCoefficientPrimeSupport"

namespace DkMath.FLT.Seven

/-- Quotient coprimality and strict size keep the power prime off the divisor side,
even when that prime divides the coefficient. -/
theorem eligible_primitive_divisor_smallCoefficient_prime_not_dvd
    {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) : ¬ p ∣ r := by
  have hdiv := Nat.dvd_of_mem_divisors hmem
  have hprod : r * ((c * p ^ n) / r) = c * p ^ n := Nat.mul_div_cancel' hdiv
  have hcpos : 0 < c := by
    by_contra h
    have hz : c = 0 := by omega
    simp [hz] at hsize
  intro hpdiv
  let t := (c * p ^ n) / r
  have htp : ¬ p ∣ t := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpdiv)
  have htdiv : t ∣ c * p ^ n := ⟨r, hprod.symm.trans (Nat.mul_comm r t)⟩
  have htc : t ∣ c :=
    ((hp.coprime_iff_not_dvd.mpr htp).symm.pow_right n).dvd_mul_right.mp htdiv
  have ht : t ≤ 7 ^ 3 := (Nat.le_of_dvd hcpos htc).trans hc
  have hM : c * p ^ n ≤ 7 ^ 3 * r ^ 7 := by
    calc
      c * p ^ n = r * t := hprod.symm
      _ ≤ r * 7 ^ 3 := Nat.mul_le_mul_left r ht
      _ = 7 ^ 3 * r := Nat.mul_comm _ _
      _ ≤ 7 ^ 3 * r ^ 7 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) r)
  omega

/-- A positive prime power belongs to the actual complement of the same divisor. -/
theorem eligible_smallCoefficient_prime_in_complement
    {c p n r : ℕ} (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) :
    ¬ p ∣ r ∧ p ∣ (c * p ^ n) / r := by
  have hr := eligible_primitive_divisor_smallCoefficient_prime_not_dvd hp hc hmem hcop hsize
  refine ⟨hr, ?_⟩
  have hprod : r * ((c * p ^ n) / r) = c * p ^ n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hmem)
  have hM : p ∣ c * p ^ n :=
    dvd_mul_of_dvd_right (dvd_pow (dvd_refl p) (by omega : n ≠ 0)) c
  rw [← hprod] at hM
  exact (hp.dvd_mul.mp hM).resolve_left hr

/-- Complementary prime13 support excludes every exact eligible allocation
for all small coefficients and positive exponents. -/
theorem sixthPowerSieved_smallCoefficient_thirteen_pow_excluded
    {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * 13 ^ n) := by
  rintro ⟨r, hmem, hcop, hsize, _, _, hbranch⟩
  have hs := eligible_smallCoefficient_prime_in_complement
    (by decide : Nat.Prime 13) hc hn hmem hcop hsize
  apply nestedAllocation_excluded_of_thirteen_support hs.1 hs.2
  exact hbranch.elim (fun h => .inl h.2) (fun h => .inr h.2.2)

end DkMath.FLT.Seven
