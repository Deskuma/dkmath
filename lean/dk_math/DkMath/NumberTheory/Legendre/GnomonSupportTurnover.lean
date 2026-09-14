/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Legendre.GnomonSuccessor

#print "file: DkMath.NumberTheory.Legendre.GnomonSupportTurnover"

/-!
# Exact support turnover across the successor reindex

For the canonical threshold-skipping reindex, a prime in both the old and
successor supports is exactly an old prime divisor of the point displacement.
The lower displacement is the unit gnomon and the upper displacement is twice
the fresh threshold.  This is a finite support identity only; it does not
assert a full-cover failure or a prime in every square cell.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive

/-! ## Exact adjacent-shell intersections -/

theorem mem_reindexed_primeSupport_inter_lower_iff
    {n r q : ℕ}
    (_hr : SquareOffset n r)
    (hlow : r < n + 1) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧
        q ∣ DkMath.Gnomon.oddGnomon n := by
  constructor
  · intro hcommon
    have hold : q ∈ squareOffsetPrimeSupport n r :=
      (Finset.mem_inter.mp hcommon).1
    have hnew : q ∈ squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r) :=
      (Finset.mem_inter.mp hcommon).2
    exact ⟨hold, dvd_oddGnomon_of_dvd_reindexed_lower_common hlow
      (mem_squareOffsetPrimeSupport.mp hold).2.2
      (mem_squareOffsetPrimeSupport.mp hnew).2.2⟩
  · rintro ⟨hold, hgnomon⟩
    have hold' := mem_squareOffsetPrimeSupport.mp hold
    have hnewdiv : q ∣ (n + 1) ^ 2 + successorThresholdInsert n r := by
      rw [successorThresholdInsert_lower_additive_displacement hlow]
      exact dvd_add hold'.2.2 hgnomon
    have hnew : q ∈ squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r) := by
      apply mem_squareOffsetPrimeSupport.mpr
      exact ⟨hold'.1, le_trans hold'.2.1 (Nat.le_succ n), hnewdiv⟩
    exact Finset.mem_inter.mpr ⟨hold, hnew⟩

theorem reindexed_primeSupport_inter_lower_eq_filter
    {n r : ℕ}
    (hr : SquareOffset n r)
    (hlow : r < n + 1) :
    squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) =
      (squareOffsetPrimeSupport n r).filter
        (fun q => q ∣ DkMath.Gnomon.oddGnomon n) := by
  ext q
  simpa only [Finset.mem_inter, Finset.mem_filter] using
    (mem_reindexed_primeSupport_inter_lower_iff hr hlow (q := q))

theorem mem_reindexed_primeSupport_inter_upper_iff
    {n r q : ℕ}
    (_hr : SquareOffset n r)
    (hupp : n + 1 ≤ r) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧
        q ∣ 2 * (n + 1) := by
  constructor
  · intro hcommon
    have hold : q ∈ squareOffsetPrimeSupport n r :=
      (Finset.mem_inter.mp hcommon).1
    have hnew : q ∈ squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r) :=
      (Finset.mem_inter.mp hcommon).2
    exact ⟨hold, dvd_two_mul_succ_of_dvd_reindexed_upper_common hupp
      (mem_squareOffsetPrimeSupport.mp hold).2.2
      (mem_squareOffsetPrimeSupport.mp hnew).2.2⟩
  · rintro ⟨hold, hshift⟩
    have hold' := mem_squareOffsetPrimeSupport.mp hold
    have hnewdiv : q ∣ (n + 1) ^ 2 + successorThresholdInsert n r := by
      rw [successorThresholdInsert_upper_additive_displacement hupp]
      exact dvd_add hold'.2.2 hshift
    have hnew : q ∈ squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r) := by
      apply mem_squareOffsetPrimeSupport.mpr
      exact ⟨hold'.1, le_trans hold'.2.1 (Nat.le_succ n), hnewdiv⟩
    exact Finset.mem_inter.mpr ⟨hold, hnew⟩

theorem reindexed_primeSupport_inter_upper_eq_filter
    {n r : ℕ}
    (hr : SquareOffset n r)
    (hupp : n + 1 ≤ r) :
    squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) =
      (squareOffsetPrimeSupport n r).filter
        (fun q => q ∣ 2 * (n + 1)) := by
  ext q
  simpa only [Finset.mem_inter, Finset.mem_filter] using
    (mem_reindexed_primeSupport_inter_upper_iff hr hupp (q := q))

/-! ## The upper prime-threshold channel -/

theorem oldPrime_dvd_two_mul_succ_imp_eq_two
    {n q : ℕ}
    (hsucc : Nat.Prime (n + 1))
    (hq : Nat.Prime q)
    (hqle : q ≤ n)
    (hdiv : q ∣ 2 * (n + 1)) :
    q = 2 := by
  rcases hq.dvd_mul.mp hdiv with hqtwo | hqnext
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hqtwo with
      hqone | hqeq
    · exact False.elim (hq.ne_one hqone)
    · exact hqeq
  · rcases (Nat.dvd_prime hsucc).mp hqnext with hqone | hqeq
    · exact False.elim (hq.ne_one hqone)
    · omega

theorem oldPrime_dvd_two_mul_succ_iff_eq_two
    {n q : ℕ}
    (hsucc : Nat.Prime (n + 1))
    (hq : Nat.Prime q)
    (hqle : q ≤ n) :
    q ∣ 2 * (n + 1) ↔ q = 2 := by
  constructor
  · exact oldPrime_dvd_two_mul_succ_imp_eq_two hsucc hq hqle
  · intro hqeq
    rw [hqeq]
    exact dvd_mul_right 2 (n + 1)

theorem mem_reindexed_primeSupport_inter_upper_imp_eq_two
    {n r q : ℕ}
    (hr : SquareOffset n r)
    (hupp : n + 1 ≤ r)
    (hsucc : Nat.Prime (n + 1))
    (hcommon : q ∈ squareOffsetPrimeSupport n r ∩
      squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r)) :
    q = 2 := by
  have hold := (Finset.mem_inter.mp hcommon).1
  have hold' := mem_squareOffsetPrimeSupport.mp hold
  exact oldPrime_dvd_two_mul_succ_imp_eq_two hsucc hold'.1 hold'.2.1
    ((mem_reindexed_primeSupport_inter_upper_iff hr hupp).mp hcommon).2

theorem reindexed_primeSupport_inter_upper_eq_filter_eq_two
    {n r : ℕ}
    (hr : SquareOffset n r)
    (hupp : n + 1 ≤ r)
    (hsucc : Nat.Prime (n + 1)) :
    squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) =
      (squareOffsetPrimeSupport n r).filter (fun q => q = 2) := by
  ext q
  constructor
  · intro hcommon
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hcommon).1,
      mem_reindexed_primeSupport_inter_upper_imp_eq_two hr hupp hsucc hcommon⟩
  · intro hfilter
    have hfilter' := Finset.mem_filter.mp hfilter
    apply (mem_reindexed_primeSupport_inter_upper_iff hr hupp).mpr
    refine ⟨hfilter'.1, ?_⟩
    rw [hfilter'.2]
    exact dvd_mul_right 2 (n + 1)

/-! ## Disjointness corollaries -/

theorem disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon
    {n r : ℕ}
    (hr : SquareOffset n r)
    (hlow : r < n + 1)
    (hgnomon : Nat.Prime (DkMath.Gnomon.oddGnomon n)) :
    Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r)) := by
  rw [Finset.disjoint_left]
  intro q hold hnew
  have hold' := mem_squareOffsetPrimeSupport.mp hold
  have hdiv := (mem_reindexed_primeSupport_inter_lower_iff hr hlow).mp
    (Finset.mem_inter.mpr ⟨hold, hnew⟩)
  rcases (Nat.dvd_prime hgnomon).mp hdiv.2 with hqone | hqgnomon
  · exact hold'.1.ne_one hqone
  · have hgt : n < DkMath.Gnomon.oddGnomon n := by
      simp [DkMath.Gnomon.oddGnomon]
      omega
    omega

theorem disjoint_reindexed_primeSupport_upper_of_prime_succ_of_not_dvd_two
    {n r : ℕ}
    (hr : SquareOffset n r)
    (hupp : n + 1 ≤ r)
    (hsucc : Nat.Prime (n + 1))
    (hnot : ¬ 2 ∣ n ^ 2 + r) :
    Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r)) := by
  rw [Finset.disjoint_left]
  intro q hold hnew
  have hqeq := mem_reindexed_primeSupport_inter_upper_imp_eq_two hr hupp
    hsucc (Finset.mem_inter.mpr ⟨hold, hnew⟩)
  have holddiv := (mem_squareOffsetPrimeSupport.mp hold).2.2
  apply hnot
  simpa only [hqeq] using holddiv

/-! ## Required `30 -> 31` regressions -/

theorem disjoint_reindexed_primeSupport_lower_30
    {r : ℕ} (hr : SquareOffset 30 r) (hlow : r < 31) :
    Disjoint (squareOffsetPrimeSupport 30 r)
      (squareOffsetPrimeSupport 31 (successorThresholdInsert 30 r)) := by
  apply disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon hr hlow
  norm_num [DkMath.Gnomon.oddGnomon]

theorem mem_reindexed_primeSupport_inter_upper_30_imp_eq_two
    {r q : ℕ} (hr : SquareOffset 30 r) (hupp : 31 ≤ r)
    (hcommon : q ∈ squareOffsetPrimeSupport 30 r ∩
      squareOffsetPrimeSupport 31 (successorThresholdInsert 30 r)) :
    q = 2 := by
  exact mem_reindexed_primeSupport_inter_upper_imp_eq_two hr hupp
    (by norm_num) hcommon

end DkMath.NumberTheory.Legendre
