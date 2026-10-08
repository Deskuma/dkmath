/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreCanonicalRootCharge

#print "file: DkMathTest.NumberTheory.LegendreCanonicalRootRegression"

namespace DkMathTest.LegendreCanonicalRootRegression
open DkMath.NumberTheory.Legendre
open DkMathTest.LegendreBlockLocalization

/-- The first prime-anchor raw odd product hit lost to anchor coprimality. -/
theorem raw_odd_candidate_counterexample :
    (26 : ℕ) ∈ squareWaveOffsets 13 (3 * 5) ∧ Odd (13 ^ 2 + 26) ∧
    (26 : ℕ) ∉ squareAnchorOddPointCoprimeOffsets 13 ∧
    primeAnchorProductWaveCount 13 (3 * 5) = 0 := by
  rw [candidate_eq_filter_Icc]
  simp only [mem_squareWaveOffsets, SquareOffset, Finset.mem_filter, Finset.mem_Icc]
  decide +kernel

/-- The first root7 common-exclusion example, with an actual candidate shell point. -/
theorem common_exclusion_credit_counterexample :
    (26 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 67 ∧
    105 * 43 ∣ 67 ^ 2 + 26 ∧
    primeAnchorProductWaveCount 67 (7 * 43) = 1 ∧
    primeAnchorProductWaveCount 67 (21 * 43) = 1 ∧
    primeAnchorProductWaveCount 67 (35 * 43) = 1 ∧
    primeAnchorProductWaveCount 67 (105 * 43) = 1 ∧
    (1 : ℕ) + 1 - (1 + 1) = 0 ∧ (1 : ℕ) - 1 - 1 + 1 = 1 := by
  rw [candidate_eq_filter_Icc]
  decide +kernel

/-- Common exclusions have canonical root3, hence contribute no root7 edge. -/
theorem common_exclusion_root7_empty : (canonicalRootPairOffsets 67 7 43).card = 0 := by
  have H : 3 ∈ squareAnchorOddActivePrimes 67 ∧
      5 ∈ squareAnchorOddActivePrimes 67 ∧ 7 ∈ squareAnchorOddActivePrimes 67 :=
    primeAnchor_small_roots (by decide) (by decide)
  have hq : 43 ∈ squareAnchorOddActivePrimes 67 := by
    rw [mem_squareAnchorOddActivePrimes]
    decide
  rw [canonicalRoot7Pair_card H.1 H.2.1 H.2.2 hq (by decide)]
  have count : ∀ m ∈ ({7*43,21*43,35*43,105*43} : Finset ℕ),
      (paritySafeProductWaveOffsets 67 m).card = primeAnchorProductWaveCount 67 m := by
    intro m hm
    have hodd : Odd m := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
        m = 7*43 ∨ m = 21*43 ∨ m = 35*43 ∨ m = 105*43) with rfl | rfl | rfl | rfl <;> decide
    have hcop : Nat.Coprime 67 m := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
        m = 7*43 ∨ m = 21*43 ∨ m = 35*43 ∨ m = 105*43) with rfl | rfl | rfl | rfl <;> decide
    exact paritySafeProductWave_card_eq_count (by decide) (by decide) hodd hcop
  rw [count (7*43) (by simp), count (105*43) (by simp),
    count (21*43) (by simp), count (35*43) (by simp)]
  decide +kernel

/-- Three supported labels allow a star of two edges, but all three pairs form a cycle. -/
theorem triangle_is_not_local_excess :
    (26 : ℕ) ∈ squareAnchorOddPointCoprimeOffsets 17 ∧
    paritySafeActiveSupport 17 26 = {3,5,7} ∧
    (({3,5,7} : Finset ℕ).card - 1) = 2 ∧
    ({(3,5),(3,7),(5,7)} : Finset (ℕ × ℕ)).card = 3 := by
  rw [candidate_eq_filter_Icc]
  have hs : paritySafeActiveSupport 17 26 = {3,5,7} := by
    have he : (Finset.range 18).filter (fun q => q.Prime ∧ ¬q ∣ 17 ∧ q ≠ 2 ∧
        q ∣ 17 ^ 2 + 26) = {3,5,7} := by decide +kernel
    rw [← he]
    ext q
    simp only [mem_paritySafeActiveSupport_iff_dvd, mem_squareAnchorOddActivePrimes,
      Finset.mem_filter, Finset.mem_range]
    have hb : q ≤ 17 ↔ q < 18 := by omega
    rw [hb]
    tauto
  rw [hs]
  decide +kernel

end DkMathTest.LegendreCanonicalRootRegression
