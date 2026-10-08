/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughStrata"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The four filters share the existing rough carrier and its actual active support. -/
noncomputable def roughZeroSeats (n : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n (Nat.sqrt n)).filter (fun r => (paritySafeActiveSupport n r).card = 0)

noncomputable def roughSingletonSeats (n : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n (Nat.sqrt n)).filter (fun r => (paritySafeActiveSupport n r).card = 1)

noncomputable def roughDoubleSeats (n : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n (Nat.sqrt n)).filter (fun r => (paritySafeActiveSupport n r).card = 2)

noncomputable def roughTripleSeats (n : ℕ) : Finset ℕ :=
  (canonicalRoughCandidates n (Nat.sqrt n)).filter (fun r => (paritySafeActiveSupport n r).card = 3)

theorem roughZeroSeats_eq_uncovered (n : ℕ) : roughZeroSeats n = paritySafeUncoveredCandidates n :=
  rough_empty_eq_uncovered n (Nat.sqrt n)

theorem rough_strata_pairwise_disjoint (n : ℕ) :
    Disjoint (roughZeroSeats n) (roughSingletonSeats n) ∧
    Disjoint (roughZeroSeats n) (roughDoubleSeats n) ∧
    Disjoint (roughZeroSeats n) (roughTripleSeats n) ∧
    Disjoint (roughSingletonSeats n) (roughDoubleSeats n) ∧
    Disjoint (roughSingletonSeats n) (roughTripleSeats n) ∧
    Disjoint (roughDoubleSeats n) (roughTripleSeats n) := by
  classical
  have hd (i j : ℕ) (hij : i ≠ j) :
      Disjoint ((canonicalRoughCandidates n (Nat.sqrt n)).filter
        (fun r => (paritySafeActiveSupport n r).card = i))
        ((canonicalRoughCandidates n (Nat.sqrt n)).filter
          (fun r => (paritySafeActiveSupport n r).card = j)) := by
    apply Finset.disjoint_left.mpr
    intro r hi hj
    exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  exact ⟨hd 0 1 (by decide), hd 0 2 (by decide), hd 0 3 (by decide),
    hd 1 2 (by decide), hd 1 3 (by decide), hd 2 3 (by decide)⟩

theorem rough_strata_union (n : ℕ) :
    roughZeroSeats n ∪ roughSingletonSeats n ∪ roughDoubleSeats n ∪ roughTripleSeats n =
      canonicalRoughCandidates n (Nat.sqrt n) := by
  classical
  ext r
  simp only [roughZeroSeats, roughSingletonSeats, roughDoubleSeats, roughTripleSeats,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · tauto
  · intro hr
    have hb := sqrtCutoff_support_card_le_three hr
    have hk : (paritySafeActiveSupport n r).card = 0 ∨ (paritySafeActiveSupport n r).card = 1 ∨
        (paritySafeActiveSupport n r).card = 2 ∨ (paritySafeActiveSupport n r).card = 3 := by omega
    rcases hk with hk | hk | hk | hk <;> simp only [hk, hr] <;> tauto

/-- Weighted finite census of the four actual support-cardinality filters. -/
theorem rough_stratum_sum (n : ℕ) (f : ℕ → ℕ) :
    (∑ r ∈ canonicalRoughCandidates n (Nat.sqrt n), f (paritySafeActiveSupport n r).card) =
      (roughZeroSeats n).card * f 0 + (roughSingletonSeats n).card * f 1 +
        (roughDoubleSeats n).card * f 2 + (roughTripleSeats n).card * f 3 := by
  classical
  have he : ∀ r ∈ canonicalRoughCandidates n (Nat.sqrt n),
      f (paritySafeActiveSupport n r).card =
        (if (paritySafeActiveSupport n r).card = 0 then f 0 else 0) +
        (if (paritySafeActiveSupport n r).card = 1 then f 1 else 0) +
        (if (paritySafeActiveSupport n r).card = 2 then f 2 else 0) +
        (if (paritySafeActiveSupport n r).card = 3 then f 3 else 0) := by
    intro r hr
    have hb := sqrtCutoff_support_card_le_three hr
    generalize (paritySafeActiveSupport n r).card = k at hb ⊢
    interval_cases k <;> simp
  simpa only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    Finset.sum_const, smul_eq_mul, roughZeroSeats, roughSingletonSeats,
    roughDoubleSeats, roughTripleSeats, Nat.add_zero] using Finset.sum_congr rfl he

theorem rough_strata_card (n : ℕ) :
    (canonicalRoughCandidates n (Nat.sqrt n)).card =
      (roughZeroSeats n).card + (roughSingletonSeats n).card +
        (roughDoubleSeats n).card + (roughTripleSeats n).card := by
  simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_one] using rough_stratum_sum n (fun _ => 1)

theorem rough_incidence_eq_strata (n : ℕ) :
    (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) =
      (roughSingletonSeats n).card + 2 * (roughDoubleSeats n).card + 3 * (roughTripleSeats n).card := by
  rw [roughWave_sum_eq_support_sum]
  simpa only [id_eq, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul,
    Nat.mul_comm] using rough_stratum_sum n id

theorem rough_pairMoment_eq_strata (n : ℕ) :
    roughPairMoment n (Nat.sqrt n) = (roughDoubleSeats n).card + 3 * (roughTripleSeats n).card := by
  have h := rough_stratum_sum n (fun k => Nat.choose k 2)
  simpa only [roughPairMoment, show Nat.choose 0 2 = 0 by decide,
    show Nat.choose 1 2 = 0 by decide, show Nat.choose 2 2 = 1 by decide,
    show Nat.choose 3 2 = 3 by decide, Nat.mul_zero, Nat.zero_mul, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, Nat.mul_comm] using h

theorem rough_tripleMoment_eq_strata (n : ℕ) :
    roughTripleMoment n (Nat.sqrt n) = (roughTripleSeats n).card := by
  have h := rough_stratum_sum n (fun k => Nat.choose k 3)
  simpa only [roughTripleMoment, show Nat.choose 0 3 = 0 by decide,
    show Nat.choose 1 3 = 0 by decide, show Nat.choose 2 3 = 0 by decide,
    show Nat.choose 3 3 = 1 by decide, Nat.mul_zero, Nat.zero_add, Nat.mul_one] using h

theorem rough_covered_eq_strata (n : ℕ) :
    ((canonicalRoughCandidates n (Nat.sqrt n)).filter
      (fun r => (paritySafeActiveSupport n r).Nonempty)).card =
        (roughSingletonSeats n).card + (roughDoubleSeats n).card + (roughTripleSeats n).card := by
  classical
  have hp := Finset.card_filter_add_card_filter_not
    (s := canonicalRoughCandidates n (Nat.sqrt n))
    (fun r => (paritySafeActiveSupport n r).Nonempty)
  have hz : (canonicalRoughCandidates n (Nat.sqrt n)).filter
      (fun r => ¬ (paritySafeActiveSupport n r).Nonempty) = roughZeroSeats n := by
    apply Finset.filter_congr
    intro r _
    rw [Finset.not_nonempty_iff_eq_empty, Finset.card_eq_zero]
  rw [hz] at hp
  have hs := rough_strata_card n
  omega

theorem rough_covered_add_two_triple_eq_singleton_pair (n : ℕ) :
    ((canonicalRoughCandidates n (Nat.sqrt n)).filter
      (fun r => (paritySafeActiveSupport n r).Nonempty)).card + 2 * roughTripleMoment n (Nat.sqrt n) =
        (roughSingletonSeats n).card + roughPairMoment n (Nat.sqrt n) := by
  rw [rough_covered_eq_strata, rough_tripleMoment_eq_strata, rough_pairMoment_eq_strata]
  omega

theorem rough_zero_pos_iff_singleton_moment (n : ℕ) :
    0 < (roughZeroSeats n).card ↔
      (roughSingletonSeats n).card + roughPairMoment n (Nat.sqrt n) <
        (canonicalRoughCandidates n (Nat.sqrt n)).card + 2 * roughTripleMoment n (Nat.sqrt n) := by
  rw [rough_pairMoment_eq_strata, rough_tripleMoment_eq_strata, rough_strata_card]
  omega

/-- The singleton label is extracted from actual Finset card-one membership. -/
theorem roughSingleton_label_packet {n r : ℕ} (hr : r ∈ roughSingletonSeats n) :
    ∃ p, p.Prime ∧ Nat.sqrt n < p ∧ p ≤ n ∧ p ∣ n ^ 2 + r ∧
      paritySafeActiveSupport n r = {p} := by
  obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hpS : p ∈ paritySafeActiveSupport n r := by rw [hp]; exact Finset.mem_singleton_self p
  have hpL := rough_support_subset_labels hr hpS
  obtain ⟨hpA, hpgt⟩ := Finset.mem_filter.mp hpL
  have hpP := mem_squareAnchorOddActivePrimes.mp hpA
  exact ⟨p, hpP.1, hpgt, hpP.2.1, (mem_paritySafeActiveSupport_iff_dvd.mp hpS).2, hp⟩

end DkMath.NumberTheory.Legendre
