/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootSieve
import DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge"

/-! Exact floor counts retain both parity and prime-anchor endpoint exclusion.
The three small-root charges are computed from waves, never from whole excess. -/

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Shift offset waves to the shell-point interval and reuse its odd-multiple count. -/
theorem card_odd_squareWave_eq_delta {n m : ℕ} (hm : Odd m) :
    ((squareWaveOffsets n m).filter (fun r => Odd (n ^ 2 + r))).card =
      paritySafeOddMultipleFloorDelta (n ^ 2) (n ^ 2 + 2 * n) m := by
  classical
  rw [← card_filter_odd_dvd_Ioc_eq_paritySafeDelta hm (by omega)]
  apply Finset.card_bij (fun r _ => n ^ 2 + r)
  · intro r hr
    have hh := Finset.mem_filter.mp hr
    have hs := mem_squareWaveOffsets.mp hh.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr (by unfold SquareOffset at hs; omega), hh.2, hs.2⟩
  · intro a ha b hb he
    omega
  · intro x hx
    have hh := Finset.mem_filter.mp hx
    have hs := Finset.mem_Ioc.mp hh.1
    refine ⟨x - n ^ 2, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    have he : n ^ 2 + (x - n ^ 2) = x := by omega
    rw [he]
    refine ⟨mem_squareWaveOffsets.mpr ⟨?_, ?_⟩, ?_⟩
    · unfold SquareOffset
      omega
    · simpa only [he] using hh.2.2
    · exact hh.2.1

/-- Exact candidate product-wave count at an odd prime anchor. -/
def primeAnchorProductWaveCount (n m : ℕ) : ℕ :=
  paritySafeOddMultipleFloorDelta (n ^ 2) (n ^ 2 + 2 * n) m -
    paritySafeOddMultipleFloorDelta (n ^ 2) (n ^ 2 + 2 * n) (n * m)

/-- Odd raw waves must additionally exclude anchor-divisible shell points. -/
theorem paritySafeProductWave_card_eq_count {n m : ℕ}
    (hn : n.Prime) (hnOdd : Odd n) (hm : Odd m) (hcop : Nat.Coprime n m) :
    (paritySafeProductWaveOffsets n m).card = primeAnchorProductWaveCount n m := by
  classical
  let S := (squareWaveOffsets n m).filter (fun r => Odd (n ^ 2 + r))
  let T := (squareWaveOffsets n (n * m)).filter (fun r => Odd (n ^ 2 + r))
  have he : paritySafeProductWaveOffsets n m = S \ T := by
    ext r
    simp only [paritySafeProductWaveOffsets, Finset.mem_filter, Finset.mem_sdiff,
      S, T, mem_squareWaveOffsets, mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue,
      coprime_two_mul_iff_coprime_and_odd, hn.coprime_iff_not_dvd]
    constructor
    · rintro ⟨⟨hs, hnot, hodd⟩, hd⟩
      exact ⟨⟨⟨hs, hd⟩, hodd⟩, by
        rintro ⟨⟨_, hnm⟩, _⟩
        exact hnot (dvd_trans (dvd_mul_right n m) hnm)⟩
    · rintro ⟨⟨⟨hs, hd⟩, hodd⟩, hnot⟩
      refine ⟨⟨hs, ?_, hodd⟩, hd⟩
      intro hnDiv
      exact hnot ⟨⟨hs, hcop.mul_dvd_of_dvd_of_dvd hnDiv hd⟩, hodd⟩
  have hsub : T ⊆ S := by
    intro r hr
    have hh := Finset.mem_filter.mp hr
    have hs := mem_squareWaveOffsets.mp hh.1
    exact Finset.mem_filter.mpr ⟨mem_squareWaveOffsets.mpr
      ⟨hs.1, dvd_trans (dvd_mul_left m n) hs.2⟩, hh.2⟩
  rw [he, Finset.card_sdiff_of_subset hsub]
  change S.card - T.card = _
  rw [card_odd_squareWave_eq_delta hm, card_odd_squareWave_eq_delta (hnOdd.mul hm)]
  rfl

/-- The numerical root-3 product-wave sum uses all active secondary primes. -/
noncomputable def canonicalRootCharge3 (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 3 < q),
    primeAnchorProductWaveCount n (3 * q)

/-- Exact one-exclusion charge. -/
noncomputable def canonicalRootCharge5 (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 5 < q),
    (primeAnchorProductWaveCount n (5 * q) - primeAnchorProductWaveCount n (15 * q))

/-- Exact two-exclusion charge, with credit before Nat subtraction. -/
noncomputable def canonicalRootCharge7 (n : ℕ) : ℕ :=
  ∑ q ∈ (squareAnchorOddActivePrimes n).filter (fun q => 7 < q),
    (primeAnchorProductWaveCount n (7 * q) + primeAnchorProductWaveCount n (105 * q) -
      (primeAnchorProductWaveCount n (21 * q) + primeAnchorProductWaveCount n (35 * q)))

private theorem count_at_active_multiple {n q k : ℕ} (hn : n.Prime) (hlarge : 7 < n)
    (hq : q ∈ squareAnchorOddActivePrimes n) (hk : Odd k) (hkn : Nat.Coprime n k) :
    (paritySafeProductWaveOffsets n (k * q)).card = primeAnchorProductWaveCount n (k * q) := by
  have hh := mem_squareAnchorOddActivePrimes.mp hq
  apply paritySafeProductWave_card_eq_count hn (hn.odd_of_ne_two (by omega))
    (hk.mul (hh.1.odd_of_ne_two hh.2.2.2))
  exact hkn.mul_right (hh.1.coprime_iff_not_dvd.mpr hh.2.2.1).symm

/-- All three numerical charges equal the corresponding existing root fibers. -/
theorem canonicalSmallRootCharges_eq_fibers {n : ℕ} (hn : n.Prime) (hlarge : 7 < n) :
    canonicalRootCharge3 n = (canonicalRootFiber n 3).card ∧
    canonicalRootCharge5 n = (canonicalRootFiber n 5).card ∧
    canonicalRootCharge7 n = (canonicalRootFiber n 7).card := by
  classical
  obtain ⟨h3, h5, h7⟩ := primeAnchor_small_roots hn hlarge
  have hc3 : Nat.Coprime n 3 := ((mem_squareAnchorOddActivePrimes.mp h3).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h3).2.2.1).symm
  have hc5 : Nat.Coprime n 5 := ((mem_squareAnchorOddActivePrimes.mp h5).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h5).2.2.1).symm
  have hc7 : Nat.Coprime n 7 := ((mem_squareAnchorOddActivePrimes.mp h7).1.coprime_iff_not_dvd.mpr
    (mem_squareAnchorOddActivePrimes.mp h7).2.2.1).symm
  have H : ∀ k ∈ ({3,5,7,15,21,35,105} : Finset ℕ), ∀ q ∈ squareAnchorOddActivePrimes n,
      (paritySafeProductWaveOffsets n (k * q)).card = primeAnchorProductWaveCount n (k * q) := by
    intro k hk q hq
    have ho : Odd k := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hk :
        k = 3 ∨ k = 5 ∨ k = 7 ∨ k = 15 ∨ k = 21 ∨ k = 35 ∨ k = 105) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    apply count_at_active_multiple hn hlarge hq ho
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hk :
      k = 3 ∨ k = 5 ∨ k = 7 ∨ k = 15 ∨ k = 21 ∨ k = 35 ∨ k = 105) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc3
    · exact hc5
    · exact hc7
    · exact hc3.mul_right hc5
    · exact hc3.mul_right hc7
    · exact hc5.mul_right hc7
    · exact (hc3.mul_right hc5).mul_right hc7
  refine ⟨?_, ?_, ?_⟩
  · rw [canonicalRootFiber_card_eq_sum_pairs h3]
    unfold canonicalRootCharge3
    apply Finset.sum_congr rfl
    intro q hq
    rw [canonicalRoot3Pair_eq, H 3 (by simp) q (Finset.mem_filter.mp hq).1]
  · rw [canonicalRootFiber_card_eq_sum_pairs h5]
    unfold canonicalRootCharge5
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqa, hgt⟩ := Finset.mem_filter.mp hq
    rw [canonicalRoot5Pair_card h3 h5 hqa hgt, H 5 (by simp) q hqa, H 15 (by simp) q hqa]
  · rw [canonicalRootFiber_card_eq_sum_pairs h7]
    unfold canonicalRootCharge7
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqa, hgt⟩ := Finset.mem_filter.mp hq
    rw [canonicalRoot7Pair_card h3 h5 h7 hqa hgt, H 7 (by simp) q hqa,
      H 105 (by simp) q hqa, H 21 (by simp) q hqa, H 35 (by simp) q hqa]

/-- Nested small-root selections provide disjoint lower charges for excess. -/
theorem canonicalSmallRootCharges_le_excess {n : ℕ} (hn : n.Prime) (hlarge : 7 < n) :
    canonicalRootCharge3 n ≤ paritySafeSupportExcess n ∧
    canonicalRootCharge3 n + canonicalRootCharge5 n ≤ paritySafeSupportExcess n ∧
    canonicalRootCharge3 n + canonicalRootCharge5 n + canonicalRootCharge7 n ≤
      paritySafeSupportExcess n := by
  classical
  obtain ⟨he3, he5, he7⟩ := canonicalSmallRootCharges_eq_fibers hn hlarge
  rw [he3, he5, he7]
  refine ⟨?_, ?_, ?_⟩
  · simpa using sum_canonicalRootFiber_le_excess n {3}
  · simpa [Finset.sum_insert, Nat.add_comm] using sum_canonicalRootFiber_le_excess n {3, 5}
  · simpa [Finset.sum_insert, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using sum_canonicalRootFiber_le_excess n {3, 5, 7}

/-- The reusable demand consumer for any finite canonical root cutoff. -/
theorem uncoveredCandidates_nonempty_of_canonicalRoots {n : ℕ} (R : Finset ℕ)
    (hgap : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + ∑ p ∈ R, (canonicalRootFiber n p).card) :
    (paritySafeUncoveredCandidates n).Nonempty :=
  paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (sum_canonicalRootFiber_le_excess n R) hgap

/-- The square-cell endpoint for the same explicit finite root provider. -/
theorem prime_squareCell_of_canonicalRoots {n : ℕ} (hn : 0 < n) (R : Finset ℕ)
    (hgap : paritySafeTwoPrimeIncidenceUpper n <
      (squareAnchorOddPointCoprimeOffsets n).card + ∑ p ∈ R, (canonicalRootFiber n p).card) :
    ∃ p, p.Prime ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (uncoveredCandidates_nonempty_of_canonicalRoots R hgap)

end DkMath.NumberTheory.Legendre
