/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization

#print "file: DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation"

/-! Exact ideal factorization over its complete finite height-one support.
Power extraction requires the exponent condition on every prime in that support. -/
namespace DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
open scoped BigOperators
open IsDedekindDomain
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The full finite support, including every prime dividing the nonzero ideal. -/
def support (I : Ideal R) (hI : I ≠ 0) : Finset (HeightOneSpectrum R) :=
  (Ideal.finite_factors hI).toFinset

/-- The exact exponent; this uses the same Associates count as the current FLT7 API. -/
def exponent (I : Ideal R) (v : HeightOneSpectrum R) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

@[simp] theorem mem_support (I : Ideal R) (hI : I ≠ 0) (v : HeightOneSpectrum R) :
    v ∈ support I hI ↔ v.asIdeal ∣ I := by simp [support]

theorem factorization (I : Ideal R) (hI : I ≠ 0) :
    I = ∏ v ∈ support I hI, v.asIdeal ^ exponent I v := by
  classical
  calc
    I = ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I :=
      (Ideal.finprod_heightOneSpectrum_factorization hI).symm
    _ = _ := ?_
  apply finprod_eq_finsetProd_of_mulSupport_subset
  intro v hv
  apply (mem_support I hI v).mpr
  apply (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp
  intro hz
  apply hv
  simp [HeightOneSpectrum.maxPowDividing, hz]

/-- Membership and a strict cutoff determine the exact exponent in full support. -/
theorem principal_exponent_eq (a : R) (v : HeightOneSpectrum R)
    (ha : Ideal.span ({a} : Set R) ≠ 0) (n : ℕ)
    (hm : a ∈ v.asIdeal ^ n) (hn : a ∉ v.asIdeal ^ (n + 1)) :
    exponent (Ideal.span {a}) v = n := by
  have he (k : ℕ) : a ∈ v.asIdeal ^ k ↔
      k ≤ exponent (Ideal.span {a}) v := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le]
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha)
      (Associates.irreducible_mk.mpr v.irreducible)
  have hl := (he n).mp hm
  have hu : ¬ n + 1 ≤ exponent (Ideal.span {a}) v := fun h => hn ((he (n + 1)).mpr h)
  omega

/-- The explicit finite ideal root. -/
def powerRoot (I : Ideal R) (hI : I ≠ 0) (n : ℕ) : Ideal R :=
  ∏ v ∈ support I hI, v.asIdeal ^ (exponent I v / n)

theorem eq_powerRoot_pow (I : Ideal R) (hI : I ≠ 0) (n : ℕ)
    (hdiv : ∀ v ∈ support I hI, n ∣ exponent I v) :
    I = powerRoot I hI n ^ n := by
  classical
  calc
    I = ∏ v ∈ support I hI, v.asIdeal ^ exponent I v := factorization I hI
    _ = _ := ?_
  rw [powerRoot, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← pow_mul, Nat.div_mul_cancel (hdiv v hv)]

/-- A finite sub-support yields an exact factor and its complementary factor. -/
theorem partition (I : Ideal R) (hI : I ≠ 0)
    (select : HeightOneSpectrum R → Prop) [DecidablePred select] :
    I = (∏ v ∈ (support I hI).filter select, v.asIdeal ^ exponent I v) *
      ∏ v ∈ (support I hI).filter (fun v => ¬ select v), v.asIdeal ^ exponent I v := by
  classical
  exact (factorization I hI).trans
    (Finset.prod_filter_mul_prod_filter_not (support I hI) select
      (fun v => v.asIdeal ^ exponent I v)).symm

/-- Selected local exponents aggregate to a power, without asserting that
unselected primes have disappeared. -/
theorem selected_power_factor (I : Ideal R) (hI : I ≠ 0) (n : ℕ)
    (select : HeightOneSpectrum R → Prop) [DecidablePred select]
    (hdiv : ∀ v ∈ (support I hI).filter select, n ∣ exponent I v) :
    I = (∏ v ∈ (support I hI).filter select, v.asIdeal ^ (exponent I v / n)) ^ n *
      ∏ v ∈ (support I hI).filter (fun v => ¬ select v), v.asIdeal ^ exponent I v := by
  classical
  calc
    I = (∏ v ∈ (support I hI).filter select, v.asIdeal ^ exponent I v) *
      ∏ v ∈ (support I hI).filter (fun v => ¬ select v), v.asIdeal ^ exponent I v :=
      partition I hI select
    _ = _ := ?_
  rw [← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  rw [← pow_mul, Nat.div_mul_cancel (hdiv v hv)]

end
end DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation
