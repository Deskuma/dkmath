/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorSieve

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorLeastFactor"

/-! Least-factor routing and an independent factor-pair upper bound for sieve error.
An upper bound for the error gives a lower bound for the prime mass, not a smaller
upper envelope. The exact ledger orientation is retained explicitly. -/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Endpoint factor pairs: the complement need not have r as its least factor. -/
def gnomonCofactorFactorPairs (n k : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 (Nat.sqrt ((n ^ 2 + 2 * n) / k))).filter
    (fun r => r.Prime ∧ Nat.Coprime r (finitePrimeBasisProduct S))).biUnion
    (fun r => (((Finset.Icc (max r (max (n ^ 2 / k) (2 * n) / r + 1))
      (((n ^ 2 + 2 * n) / k) / r)).filter
        (fun m => Nat.Coprime m (finitePrimeBasisProduct S))).image (fun m => (r, m))))

/-- Canonical normal form, with every prime divisor of the complement at least r. -/
theorem gnomonCofactorSieveComposite_normalForm {n k q : ℕ} {S : Finset ℕ}
    (hq : q ∈ gnomonCofactorSieveCandidates n k S) (hc : ¬ q.Prime) :
    let r := q.minFac
    let m := q / r
    r.Prime ∧ q = r * m ∧ r ≤ m ∧ r ^ 2 ≤ (n ^ 2 + 2 * n) / k ∧
      Nat.Coprime r (finitePrimeBasisProduct S) ∧
      Nat.Coprime m (finitePrimeBasisProduct S) ∧
      max (n ^ 2 / k) (2 * n) / r < m ∧ m ≤ ((n ^ 2 + 2 * n) / k) / r ∧
      (∀ p, p.Prime → p ∣ m → r ≤ p) := by
  obtain ⟨hqI, hcop⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hqI
  have hpos : 0 < q := by omega
  have hne : q ≠ 1 := by
    by_contra hh
    subst q
    have hw := le_max_right (n ^ 2 / k) (2 * n)
    have : n = 0 := by omega
    subst n
    simp at hhi
  have hr := Nat.minFac_prime hne
  have he : q = q.minFac * (q / q.minFac) :=
    (Nat.mul_div_cancel' (Nat.minFac_dvd q)).symm
  have hmD : q / q.minFac ∣ q := ⟨q.minFac, by simpa only [Nat.mul_comm] using he⟩
  dsimp only
  refine ⟨hr, he, Nat.minFac_le_div hpos hc,
    (Nat.minFac_sq_le_self hpos hc).trans hhi,
    hcop.coprime_dvd_left (Nat.minFac_dvd q), hcop.coprime_dvd_left hmD, ?_, ?_, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul hr.pos).mpr
    rw [Nat.mul_comm (q / q.minFac) q.minFac, ← he]
    omega
  · apply (Nat.le_div_iff_mul_le hr.pos).mpr
    rwa [Nat.mul_comm (q / q.minFac) q.minFac, ← he]
  · intro p hp hd
    exact Nat.minFac_le_of_dvd hp.two_le (hd.trans hmD)

/-- Avoiding a basis excludes its primes, not all integers below its maximum. -/
theorem gnomonCofactorSieveComposite_minFac_not_mem {n k q : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hq : q ∈ gnomonCofactorSieveCandidates n k S)
    (_hc : ¬ q.Prime) : q.minFac ∉ S := by
  intro hm
  have hnot := (mem_gnomonCofactorSieveCandidates_iff hS).mp hq
  exact hnot.2.2 ⟨q.minFac, hm, Nat.minFac_dvd q⟩

/-- A covered prime cutoff forces a strictly larger least factor. -/
theorem gnomonCofactorSieveComposite_minFac_gt {n k q c : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hcover : ∀ p, p.Prime → p ≤ c → p ∈ S)
    (hq : q ∈ gnomonCofactorSieveCandidates n k S) (hc : ¬ q.Prime) :
    c < q.minFac := by
  have h := gnomonCofactorSieveComposite_normalForm hq hc
  dsimp only at h
  by_contra hh
  exact gnomonCofactorSieveComposite_minFac_not_mem hS hq hc
    (hcover _ h.1 (by omega))

/-- Product reconstructs q, making the canonical pair index injective. -/
theorem gnomonCofactorLeastFactorPair_injective {n k : ℕ} {S : Finset ℕ} :
    Set.InjOn (fun q : ℕ => (q.minFac, q / q.minFac))
      {q | q ∈ gnomonCofactorSieveCandidates n k S ∧ ¬ q.Prime} := by
  intro a ha b hb hab
  have hea := (gnomonCofactorSieveComposite_normalForm ha.1 ha.2).2.1
  have heb := (gnomonCofactorSieveComposite_normalForm hb.1 hb.2).2.1
  have hprod := congrArg (fun p : ℕ × ℕ => p.1 * p.2) hab
  dsimp only at hprod
  rw [← hea, ← heb] at hprod
  exact hprod

/-- The canonical least-factor pair lies in the endpoint-only pair cover. -/
theorem gnomonCofactorSieveComposite_mem_factorPairs {n k q : ℕ} {S : Finset ℕ}
    (hq : q ∈ gnomonCofactorSieveCandidates n k S) (hc : ¬ q.Prime) :
    (q.minFac, q / q.minFac) ∈ gnomonCofactorFactorPairs n k S := by
  obtain ⟨hr, _, hrm, hrsq, hrC, hmC, hlo, hhi, _⟩ :=
    gnomonCofactorSieveComposite_normalForm hq hc
  apply Finset.mem_biUnion.mpr
  refine ⟨q.minFac, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hr.two_le, Nat.le_sqrt'.mpr hrsq⟩, hr, hrC⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨q / q.minFac, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨?_, hhi⟩, hmC⟩, rfl⟩
  exact max_le hrm (by omega)

/-- Independent cover weight; no composite, minFac or carry predicate is used. -/
noncomputable def gnomonCofactorFactorPairBudget (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1), ∑ p ∈ gnomonCofactorFactorPairs n k S,
    Real.log ((p.1 * p.2 : ℕ) : ℝ)

/-- All factor pairs have nonnegative log weight, including extra representations. -/
theorem gnomonCofactorFactorPair_weight_nonneg {n k : ℕ} {S : Finset ℕ}
    {p : ℕ × ℕ} (hp : p ∈ gnomonCofactorFactorPairs n k S) :
    0 ≤ Real.log ((p.1 * p.2 : ℕ) : ℝ) := by
  obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨m, hmI, he⟩ := Finset.mem_image.mp hm
  subst p
  have hr2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  have hmR := (le_max_left r (max (n ^ 2 / k) (2 * n) / r + 1)).trans
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hmI).1).1
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ r * m by nlinarith))

/-- Genuine overcover bound, retaining all cofactor-window multiplicities. -/
theorem gnomonCofactorSieveCompositeError_le_factorPairBudget (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSieveCompositeError n S ≤ gnomonCofactorFactorPairBudget n S := by
  classical
  apply Finset.sum_le_sum
  intro k _
  let C := (gnomonCofactorSieveCandidates n k S).filter (fun q => ¬ q.Prime)
  let f := fun q : ℕ => (q.minFac, q / q.minFac)
  have hinj : Set.InjOn f (↑C) := by
    intro a ha b hb he
    exact gnomonCofactorLeastFactorPair_injective
      (Finset.mem_filter.mp ha) (Finset.mem_filter.mp hb) he
  have hsub : C.image f ⊆ gnomonCofactorFactorPairs n k S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact gnomonCofactorSieveComposite_mem_factorPairs
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
  calc
    _ = ∑ q ∈ C, Real.log (( (f q).1 * (f q).2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have he := (gnomonCofactorSieveComposite_normalForm
        (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2.1
      dsimp only [f]
      rw [← he]
    _ = ∑ p ∈ C.image f, Real.log ((p.1 * p.2 : ℕ) : ℝ) :=
      by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => gnomonCofactorFactorPair_weight_nonneg hp)

/-- Error upper bounds have this orientation; they cannot be subtracted from V
    to produce a prime-mass upper bound. -/
theorem gnomonCofactorFactorPairBudget_prime_lower {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorSieveMass n S - gnomonCofactorFactorPairBudget n S ≤
      gnomonCofactorWindowMass n := by
  have he := gnomonCofactorSieveMass_eq_window_add_error hS hbound
  have hf := gnomonCofactorSieveCompositeError_le_factorPairBudget n S
  linarith

/-- Every covering pair represents a surviving composite; extra pairs can share a product. -/
theorem gnomonCofactorFactorPairs_product_mem {n k : ℕ} {S : Finset ℕ}
    {p : ℕ × ℕ} (hp : p ∈ gnomonCofactorFactorPairs n k S) :
    p.1 * p.2 ∈ gnomonCofactorSieveCandidates n k S ∧ ¬ (p.1 * p.2).Prime := by
  obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨m, hmI, he⟩ := Finset.mem_image.mp hm
  subst p
  obtain ⟨hrI, hrP, hrC⟩ := Finset.mem_filter.mp hr
  obtain ⟨hmI, hmC⟩ := Finset.mem_filter.mp hmI
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmI
  have hmR : r ≤ m := (le_max_left _ _).trans hlo
  have hmA : max (n ^ 2 / k) (2 * n) / r < m := by
    have := (le_max_right _ _).trans hlo
    omega
  have hA := (Nat.div_lt_iff_lt_mul hrP.pos).mp hmA
  have hB := (Nat.le_div_iff_mul_le hrP.pos).mp hhi
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
    hrC.mul_left hmC⟩, Nat.not_prime_mul hrP.ne_one (by have := hrP.two_le; omega)⟩
  · dsimp only
    rw [Nat.mul_comm m r] at hA
    omega
  · dsimp only
    simpa only [Nat.mul_comm m r] using hB

/-- Diagonal pair products are a sparse independent, certainly-composite subcarrier. -/
def gnomonCofactorSquareWitnesses (n k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((gnomonCofactorFactorPairs n k S).filter (fun p => p.1 = p.2)).image
    (fun p => p.1 * p.2)

/-- Lower error witness; distinct products are counted once in each window. -/
noncomputable def gnomonCofactorSquareWitnessMass (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1), ∑ q ∈ gnomonCofactorSquareWitnesses n k S,
    Real.log (q : ℝ)

/-- Certified composite mass has the direction needed for deletion from V. -/
theorem gnomonCofactorSquareWitnessMass_le_error (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorSquareWitnessMass n S ≤ gnomonCofactorSieveCompositeError n S := by
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc, hn⟩ := gnomonCofactorFactorPairs_product_mem (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hc, hn⟩
  · intro q hq _
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))

/-- One corrected singleton envelope, using a lower error witness rather than an upper bound. -/
noncomputable def gnomonCofactorLeastFactorBudget (n : ℕ) (S : Finset ℕ) : ℝ :=
  min (gnomonCofactorSieveBudget n S)
    (gnomonCofactorSieveMass n S - gnomonCofactorSquareWitnessMass n S)

theorem gnomonCofactorWindowMass_le_leastFactorBudget {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorLeastFactorBudget n S := by
  apply le_min (gnomonCofactorWindowMass_le_sieveBudget hn hS hbound)
  have he := gnomonCofactorSieveMass_eq_window_add_error hS hbound
  have hl := gnomonCofactorSquareWitnessMass_le_error n S
  linarith

theorem gnomonCofactorLeastFactorBudget_le_sieveBudget (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorLeastFactorBudget n S ≤ gnomonCofactorSieveBudget n S := min_le_left _ _

/-- Exact residual: only certified square mass is deleted; the upper F is not subtracted. -/
theorem gnomonCofactorLeastFactorBudget_excess {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorLeastFactorBudget n S - gnomonCofactorWindowMass n =
      min (gnomonCofactorSieveBudget n S - gnomonCofactorWindowMass n)
        (gnomonCofactorSieveCompositeError n S - gnomonCofactorSquareWitnessMass n S) := by
  unfold gnomonCofactorLeastFactorBudget
  rw [gnomonCofactorSieveMass_eq_window_add_error hS hbound, ← min_sub_sub_right]
  congr 1
  ring

theorem gnomonPascalOldLogBudget_leastFactor_excess {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorLeastFactorBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    gnomonPascalOldLogBudget n +
      (gnomonCofactorLeastFactorBudget n S - gnomonCofactorWindowMass n) := by
  have h := gnomonPascalOldLogBudget_cofactor_excess hn
  linarith

/-- Strict consumer for the independently corrected singleton envelope. -/
theorem exists_prime_squareCell_of_leastFactorBudget_lt {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorLeastFactorBudget n S + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ)) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  have hbound' := gnomonCofactorWindowMass_le_leastFactorBudget hn hS hbound
  rw [gnomonPascalOldLogBudget_leastFactor_excess hn S] at hstrict
  linarith

end DkMath.NumberTheory.Legendre
