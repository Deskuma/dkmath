/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
import DkMath.NumberTheory.Legendre.Internal.RoughMomentCombinatorics

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughMoments"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- The zero class is the existing uncovered carrier, for every cutoff. -/
theorem rough_empty_eq_uncovered (n P : ℕ) :
    (canonicalRoughCandidates n P).filter (fun r => (paritySafeActiveSupport n r).card = 0) = paritySafeUncoveredCandidates n := by
  classical
  ext r
  rw [Finset.mem_filter, mem_uncovered_iff_no_activeSupport]
  constructor
  · rintro ⟨hr, hzero⟩
    exact ⟨(Finset.mem_filter.mp hr).1, by simpa only [Finset.card_pos] using (by omega : ¬0 < (paritySafeActiveSupport n r).card)⟩
  · rintro ⟨hr, hempty⟩
    have hzero : (paritySafeActiveSupport n r).card = 0 := by
      have := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [this]
    refine ⟨Finset.mem_filter.mpr ⟨hr, ?_⟩, hzero⟩
    intro a ha hP hd
    exact hempty ⟨a, mem_paritySafeActiveSupport_iff_dvd.mpr ⟨ha, hd⟩⟩

/-- Pair moments use actual active supports on the existing rough carrier. -/
noncomputable def roughPairMoment (n P : ℕ) : ℕ :=
  ∑ r ∈ canonicalRoughCandidates n P, Nat.choose (paritySafeActiveSupport n r).card 2

noncomputable def roughTripleMoment (n P : ℕ) : ℕ :=
  ∑ r ∈ canonicalRoughCandidates n P, Nat.choose (paritySafeActiveSupport n r).card 3

/-- A generic bounded-support form, useful before specializing the independent cutoff. -/
theorem rough_moment_balance {n P : ℕ}
    (hbound : ∀ r ∈ canonicalRoughCandidates n P, (paritySafeActiveSupport n r).card ≤ 3) :
    (paritySafeUncoveredCandidates n).card + (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n P q).card) + roughTripleMoment n P = (canonicalRoughCandidates n P).card + roughPairMoment n P := by
  classical
  rw [← rough_empty_eq_uncovered n P, Finset.card_filter, roughWave_sum_eq_support_sum]
  unfold roughPairMoment roughTripleMoment
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ r ∈ canonicalRoughCandidates n P, (1 + Nat.choose (paritySafeActiveSupport n r).card 2) :=
      Finset.sum_congr rfl (fun r hr => zero_pair_triple_balance (hbound r hr))
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]

theorem rough_tail_moment_balance {n P : ℕ}
    (hbound : ∀ r ∈ canonicalRoughCandidates n P, (paritySafeActiveSupport n r).card ≤ 3) :
    (canonicalRootTail n P).card + roughTripleMoment n P = roughPairMoment n P := by
  rw [canonicalRootTail_card_eq_rough_support_sum]
  unfold roughPairMoment roughTripleMoment
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r hr => excess_pair_triple_balance (hbound r hr))

theorem sqrt_rough_moment_balance (n : ℕ) :
    (paritySafeUncoveredCandidates n).card + (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) = (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n) :=
  rough_moment_balance (fun _ hr => sqrtCutoff_support_card_le_three hr)

theorem sqrt_tail_moment_balance (n : ℕ) :
    (canonicalRootTail n (Nat.sqrt n)).card + roughTripleMoment n (Nat.sqrt n) = roughPairMoment n (Nat.sqrt n) :=
  rough_tail_moment_balance (fun _ hr => sqrtCutoff_support_card_le_three hr)

theorem sqrt_uncovered_card_pos_iff_moment (n : ℕ) :
    0 < (paritySafeUncoveredCandidates n).card ↔
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) <
          (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n) := by
  have := sqrt_rough_moment_balance n
  omega

theorem sqrt_uncovered_nonempty_iff_moment (n : ℕ) :
    (paritySafeUncoveredCandidates n).Nonempty ↔
      (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) <
          (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n) := by
  rw [← Finset.card_pos, sqrt_uncovered_card_pos_iff_moment]

theorem sqrt_uncovered_card_eq_moment_margin (n : ℕ) :
    (paritySafeUncoveredCandidates n).card = (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n) -
        ((∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n)) := by
  have := sqrt_rough_moment_balance n
  omega

theorem uncovered_nonempty_of_sqrt_moment {n : ℕ}
    (h : (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) <
        (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n)) :
    (paritySafeUncoveredCandidates n).Nonempty :=
  (sqrt_uncovered_nonempty_iff_moment n).mpr h

theorem prime_squareCell_of_sqrt_moment {n : ℕ} (hn : 0 < n)
    (h : (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) <
        (canonicalRoughCandidates n (Nat.sqrt n)).card + roughPairMoment n (Nat.sqrt n)) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (uncovered_nonempty_of_sqrt_moment h)

theorem sqrt_covered_moment_balance (n : ℕ) :
    ((canonicalRoughCandidates n (Nat.sqrt n)).filter
      (fun r => (paritySafeActiveSupport n r).Nonempty)).card + roughPairMoment n (Nat.sqrt n) = (∑ q ∈ squareAnchorOddActivePrimes n, (canonicalRoughWave n (Nat.sqrt n) q).card) + roughTripleMoment n (Nat.sqrt n) := by
  have ht := sqrt_tail_moment_balance n
  have hi := roughWave_sum_eq_covered_add_tail n (Nat.sqrt n)
  omega

end DkMath.NumberTheory.Legendre
