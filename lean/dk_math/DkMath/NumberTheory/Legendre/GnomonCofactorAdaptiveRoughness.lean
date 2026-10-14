/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorThreePrime
import DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorAdaptiveRoughness"

namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.PrimorialUniverse
open DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- All primes at the independently specified square-root cutoff. -/
def gnomonCofactorAdaptiveBasis (n : ℕ) : Finset ℕ := primeScalesUpTo (Nat.sqrt n)

theorem gnomonCofactorAdaptiveBasis_prime (n : ℕ) :
    IsFinitePrimeBasis (gnomonCofactorAdaptiveBasis n) := by
  intro p hp
  exact (mem_primeScalesUpTo.mp hp).1

theorem gnomonCofactorAdaptiveBasis_cover (n : ℕ) :
    ∀ p, p.Prime → p ≤ Nat.sqrt n → p ∈ gnomonCofactorAdaptiveBasis n := by
  intro p hp hle
  exact mem_primeScalesUpTo.mpr ⟨hp, hle⟩

theorem gnomonCofactorAdaptiveBasis_safe (n : ℕ) :
    ∀ p ∈ gnomonCofactorAdaptiveBasis n, p ≤ 2 * n := by
  intro p hp
  have := (mem_primeScalesUpTo.mp hp).2.trans (Nat.sqrt_le_self n)
  omega

/-- Coverage, rather than merely exclusion of the least factor, controls every divisor. -/
theorem gnomonCofactorSurvivor_prime_gt {n k q c : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hcover : ∀ p, p.Prime → p ≤ c → p ∈ S)
    (hq : q ∈ gnomonCofactorSieveCandidates n k S) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ q) : c < p := by
  by_contra hh
  exact ((mem_gnomonCofactorSieveCandidates_iff hS).mp hq).2.2
    ⟨p, hcover p hp (by omega), hd⟩

/-- Four factors above the cutoff cannot fit below the endpoint, repetitions included. -/
theorem gnomonCofactor_fourFactor_impossible {c B r s t u : ℕ}
    (hB : B < (c + 1) ^ 4) (hr : c < r) (hs : c < s)
    (ht : c < t) (hu : c < u) : ¬ r * s * t * u ≤ B := by
  have h := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_of_lt hr) (Nat.succ_le_of_lt hs))
      (Nat.succ_le_of_lt ht)) (Nat.succ_le_of_lt hu)
  have he : (c + 1) * (c + 1) * (c + 1) * (c + 1) = (c + 1) ^ 4 := by ring
  rw [he] at h
  omega

private theorem triple_mem {n k r s t : ℕ} {S : Finset ℕ}
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hrs : r ≤ s) (hst : s ≤ t)
    (hq : r * s * t ∈ gnomonCofactorSieveCandidates n k S) :
    (r, s, t) ∈ gnomonCofactorThreePrimeTriples n k S := by
  obtain ⟨hI, hC⟩ := Finset.mem_filter.mp hq
  obtain ⟨hA, hB⟩ := Finset.mem_Icc.mp hI
  have hrC := hC.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right r s) t)
  have hsC := hC.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left s r) t)
  have htC := hC.coprime_dvd_left (dvd_mul_left t (r * s))
  have hr3 : r ^ 3 ≤ (n ^ 2 + 2 * n) / k := by
    have : r * r * r ≤ r * s * t :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl r) hrs) (hrs.trans hst)
    have he : r * r * r = r ^ 3 := by ring
    rw [he] at this
    exact this.trans hB
  have hr2 : r ^ 2 ≤ (n ^ 2 + 2 * n) / k := by nlinarith [hr.pos]
  have hs2 : s ^ 2 ≤ ((n ^ 2 + 2 * n) / k) / r := by
    apply (Nat.le_div_iff_mul_le hr.pos).mpr
    have := Nat.mul_le_mul_left r (Nat.mul_le_mul_left s hst)
    nlinarith
  apply Finset.mem_biUnion.mpr
  refine ⟨r, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hr.two_le, Nat.le_sqrt'.mpr hr2⟩, hr, hrC, hr3⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hrs, Nat.le_sqrt'.mpr hs2⟩, hs, hsC⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ht, htC⟩, rfl⟩
  · apply max_le hst
    apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hr.pos hs.pos)).mpr
    rw [Nat.mul_comm t (r * s)]
    omega
  · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hr.pos hs.pos)).mpr
    rwa [Nat.mul_comm t (r * s)]

/-- A covered rough cutoff exhausts composites in the existing two and three factor images. -/
theorem gnomonCofactorRough_exhaustion {n k c : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hcover : ∀ p, p.Prime → p ≤ c → p ∈ S)
    (hfour : (n ^ 2 + 2 * n) / k < (c + 1) ^ 4) :
    gnomonCofactorThreePrimeCombinedWitnesses n k S =
      (gnomonCofactorSieveCandidates n k S).filter (fun q => ¬ q.Prime) := by
  apply Finset.Subset.antisymm (gnomonCofactorThreePrimeCombined_subset_error n k S)
  intro q hqE
  obtain ⟨hq, hc⟩ := Finset.mem_filter.mp hqE
  obtain ⟨hr, he, hrm, _, _, hmC, _, _, hleast⟩ :=
    gnomonCofactorSieveComposite_normalForm hq hc
  let r := q.minFac
  let m := q / r
  change q = r * m at he
  change r.Prime at hr
  change r ≤ m at hrm
  by_cases hm : m.Prime
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨(r, m), Finset.mem_filter.mpr
      ⟨gnomonCofactorSieveComposite_mem_factorPairs hq hc, hm⟩, he.symm⟩
  · have hm2 : 2 ≤ m := hr.two_le.trans hrm
    let s := m.minFac
    let t := m / s
    have hs : s.Prime := Nat.minFac_prime (by omega)
    have hem : m = s * t := (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm
    have hst : s ≤ t := Nat.minFac_le_div (by omega) hm
    have hrs : r ≤ s := hleast s hs (Nat.minFac_dvd m)
    have htP : t.Prime := by
      by_contra ht
      have ht2 : 2 ≤ t := hs.two_le.trans hst
      let u := t.minFac
      let v := t / u
      have hu : u.Prime := Nat.minFac_prime (by omega)
      have huv : u ≤ v := Nat.minFac_le_div (by omega) ht
      have het : t = u * v := (Nat.mul_div_cancel' (Nat.minFac_dvd t)).symm
      have heq : q = r * s * u * v := by rw [he, hem, het]; ring
      have hdR : r ∣ q := he ▸ dvd_mul_right r m
      have hdS : s ∣ q := heq ▸ dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_left s r) u) v
      have hdU : u ∣ q := heq ▸ dvd_mul_of_dvd_left (dvd_mul_left u (r * s)) v
      have hrgt := gnomonCofactorSurvivor_prime_gt hS hcover hq hr hdR
      have hsgt := gnomonCofactorSurvivor_prime_gt hS hcover hq hs hdS
      have hugt := gnomonCofactorSurvivor_prime_gt hS hcover hq hu hdU
      have hqB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
      rw [heq] at hqB
      exact gnomonCofactor_fourFactor_impossible hfour hrgt hsgt hugt
        (lt_of_lt_of_le hugt huv) hqB
    have heq : q = r * s * t := by rw [he, hem]; ring
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(r, s, t), triple_mem hr hs htP hrs hst (heq ▸ hq), heq.symm⟩

/-- The square-root basis closes the residual for every quotient window. -/
theorem gnomonCofactorAdaptive_exhaustion (n k : ℕ) :
    gnomonCofactorThreePrimeCombinedWitnesses n k (gnomonCofactorAdaptiveBasis n) =
      (gnomonCofactorSieveCandidates n k (gnomonCofactorAdaptiveBasis n)).filter
        (fun q => ¬ q.Prime) := by
  apply gnomonCofactorRough_exhaustion (gnomonCofactorAdaptiveBasis_prime n)
    (gnomonCofactorAdaptiveBasis_cover n)
  exact (Nat.div_le_self _ _).trans_lt (sqrtCutoff_power_four_gt n)

theorem gnomonCofactorAdaptive_mass_eq_error (n : ℕ) :
    gnomonCofactorThreePrimeCombinedMass n (gnomonCofactorAdaptiveBasis n) =
      gnomonCofactorSieveCompositeError n (gnomonCofactorAdaptiveBasis n) := by
  unfold gnomonCofactorThreePrimeCombinedMass gnomonCofactorSieveCompositeError
  apply Finset.sum_congr rfl
  intro k _
  rw [gnomonCofactorAdaptive_exhaustion]

/-- Exact singleton closure recovers Q; it does not assert a strict ledger inequality. -/
theorem gnomonCofactorAdaptive_budget_eq {n : ℕ} (hn : 3 ≤ n) :
    gnomonCofactorThreePrimeBudget n (gnomonCofactorAdaptiveBasis n) =
      gnomonCofactorWindowMass n := by
  apply le_antisymm
  · unfold gnomonCofactorThreePrimeBudget
    apply (min_le_right _ _).trans
    rw [gnomonCofactorAdaptive_mass_eq_error,
      gnomonCofactorSieveMass_eq_window_add_error (gnomonCofactorAdaptiveBasis_prime n)
        (gnomonCofactorAdaptiveBasis_safe n)]
    simp
  · exact gnomonCofactorWindowMass_le_threePrimeBudget hn
      (gnomonCofactorAdaptiveBasis_prime n) (gnomonCofactorAdaptiveBasis_safe n)

theorem gnomonPascalOldLogBudget_adaptive_eq {n : ℕ} (hn : 3 ≤ n) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorThreePrimeBudget n (gnomonCofactorAdaptiveBasis n) +
      gnomonPascalShellHigherPrimePowerMass n = gnomonPascalOldLogBudget n := by
  rw [gnomonPascalOldLogBudget_threePrime_excess hn,
    gnomonCofactorAdaptive_budget_eq hn]
  ring

end DkMath.NumberTheory.Legendre
