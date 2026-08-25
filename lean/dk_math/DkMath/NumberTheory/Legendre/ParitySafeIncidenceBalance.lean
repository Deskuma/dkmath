/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeWavePruning

#print "file: DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance"

/-!
## ParitySafeIncidenceBalance

This module transposes the finite parity-safe incidence matrix.  It separates
nonempty and silent active waves, covered and uncovered candidate seats, and
records the exact conservation law between duplicate hits and support excess.

The result is an exact finite ledger.  It introduces no new provider, prime
counting estimate, graph abstraction, or proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ### PRIM-L036.1: active-support incidence -/

/-- The active support of a parity-safe candidate seat. -/
noncomputable def paritySafeActiveSupport (n r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorOddActivePrimes n).filter
    (fun q => SquareOffsetForbiddenBy n q r)

/-- On a parity-safe candidate, the old nondivisor support is exactly active support. -/
theorem squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
    {n r : ℕ} (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    squareOffsetAnchorNondivisorSupport n r = paritySafeActiveSupport n r := by
  classical
  ext q
  constructor
  · intro hq
    have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
    have hodd := (mem_squareAnchorOddPointCoprimeOffsets.mp hr).2
    have hqne : q ≠ 2 := by
      intro hq2
      subst q
      exact not_mem_squareOffsetAnchorNondivisorSupport_of_odd_point hodd hq
    apply Finset.mem_filter.mpr
    exact ⟨mem_squareAnchorOddActivePrimes.mpr
      ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqne⟩, hq'.2.2.2⟩
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    have hactive := mem_squareAnchorOddActivePrimes.mp hq'.1
    exact mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hactive.1, hactive.2.1, hactive.2.2.1, hq'.2⟩

/-- The exact finite incidence count, summed from the active-wave side. -/
noncomputable def paritySafeIncidenceCount (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n,
    (paritySafeActiveWaveOffsets n q).card

/-- The wave-side count equals the candidate-side active-support count. -/
theorem paritySafeIncidenceCount_eq_candidate_support_sum
    (n : ℕ) :
    paritySafeIncidenceCount n =
      ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        (paritySafeActiveSupport n r).card := by
  classical
  unfold paritySafeIncidenceCount
  calc
    (∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeActiveWaveOffsets n q).card) =
        ∑ q ∈ squareAnchorOddActivePrimes n,
          ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [paritySafeActiveWaveOffsets]
    _ = ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ∑ q ∈ squareAnchorOddActivePrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          (paritySafeActiveSupport n r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [paritySafeActiveSupport, Finset.card_filter]

/-! ### PRIM-L036.2: nonempty/silent active waves -/

/-- Active waves with at least one parity-safe candidate hit. -/
noncomputable def paritySafeNonemptyActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun q => (paritySafeActiveWaveOffsets n q).Nonempty)

/-- Active waves with no parity-safe candidate hit. -/
noncomputable def paritySafeSilentActivePrimes (n : ℕ) : Finset ℕ :=
  squareAnchorOddActivePrimes n \ paritySafeNonemptyActivePrimes n

@[simp] theorem mem_paritySafeNonemptyActivePrimes
    {n q : ℕ} :
    q ∈ paritySafeNonemptyActivePrimes n ↔
      q ∈ squareAnchorOddActivePrimes n ∧
        (paritySafeActiveWaveOffsets n q).Nonempty := by
  simp [paritySafeNonemptyActivePrimes]

@[simp] theorem mem_paritySafeSilentActivePrimes
    {n q : ℕ} :
    q ∈ paritySafeSilentActivePrimes n ↔
      q ∈ squareAnchorOddActivePrimes n ∧
        ¬ (paritySafeActiveWaveOffsets n q).Nonempty := by
  rw [paritySafeSilentActivePrimes, paritySafeNonemptyActivePrimes]
  constructor
  · intro hq
    have hq' := Finset.mem_sdiff.mp hq
    refine ⟨hq'.1, ?_⟩
    intro hnonempty
    apply hq'.2
    exact Finset.mem_filter.mpr ⟨hq'.1, hnonempty⟩
  · rintro ⟨hq, hnonempty⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hq, ?_⟩
    intro hmem
    exact hnonempty (Finset.mem_filter.mp hmem).2

/-- Nonempty and silent active waves partition the active world. -/
theorem paritySafeNonemptyActivePrimes_card_add_silent_card_eq_active_card
    (n : ℕ) :
    (paritySafeNonemptyActivePrimes n).card +
        (paritySafeSilentActivePrimes n).card =
      (squareAnchorOddActivePrimes n).card := by
  have hsub : paritySafeNonemptyActivePrimes n ⊆
      squareAnchorOddActivePrimes n := by
    intro q hq
    exact (mem_paritySafeNonemptyActivePrimes.mp hq).1
  have hunion : squareAnchorOddActivePrimes n ∪
      paritySafeNonemptyActivePrimes n = squareAnchorOddActivePrimes n :=
    Finset.union_eq_left.mpr hsub
  calc
    (paritySafeNonemptyActivePrimes n).card +
        (paritySafeSilentActivePrimes n).card =
      (paritySafeSilentActivePrimes n).card +
        (paritySafeNonemptyActivePrimes n).card := Nat.add_comm _ _
    _ = (squareAnchorOddActivePrimes n ∪
        paritySafeNonemptyActivePrimes n).card := by
      unfold paritySafeSilentActivePrimes
      exact Finset.card_sdiff_add_card _ _
    _ = (squareAnchorOddActivePrimes n).card := by rw [hunion]

/-! ### PRIM-L036.3: covered and uncovered candidates -/

/-- Candidate seats with nonempty active support. -/
noncomputable def paritySafeCoveredCandidates (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorOddPointCoprimeOffsets n).filter
    (fun r => (paritySafeActiveSupport n r).Nonempty)

/-- Candidate seats with empty active support. -/
noncomputable def paritySafeUncoveredCandidates (n : ℕ) : Finset ℕ :=
  squareAnchorOddPointCoprimeOffsets n \ paritySafeCoveredCandidates n

theorem squareOffsetAnchorNondivisorSupport_nonempty_iff_covered_of_candidate
    {n r : ℕ} (hn : 0 < n)
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    (squareOffsetAnchorNondivisorSupport n r).Nonempty ↔
      SquareOffsetCovered n r := by
  rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn
    (coprime_of_mem_squareAnchorOddPointCoprimeOffsets hr)]
  exact squareOffsetCovered_iff_primeSupport_nonempty.symm

@[simp] theorem mem_paritySafeCoveredCandidates
    {n r : ℕ} :
    r ∈ paritySafeCoveredCandidates n ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧
        (paritySafeActiveSupport n r).Nonempty := by
  simp [paritySafeCoveredCandidates]

theorem mem_paritySafeUncoveredCandidates_iff
    {n r : ℕ} (hn : 0 < n) :
    r ∈ paritySafeUncoveredCandidates n ↔
      r ∈ squareAnchorOddPointCoprimeOffsets n ∧
        ¬ SquareOffsetCovered n r := by
  constructor
  · intro hr
    have hr' := Finset.mem_sdiff.mp hr
    refine ⟨hr'.1, ?_⟩
    intro hcovered
    apply hr'.2
    have hnondiv :=
      (squareOffsetAnchorNondivisorSupport_nonempty_iff_covered_of_candidate hn hr'.1).mpr
        hcovered
    rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr'.1]
      at hnondiv
    exact mem_paritySafeCoveredCandidates.mpr ⟨hr'.1, hnondiv⟩
  · rintro ⟨hr, hnotcovered⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hr, ?_⟩
    intro hcovered
    have hsupport := (mem_paritySafeCoveredCandidates.mp hcovered).2
    have hsupport' : (squareOffsetAnchorNondivisorSupport n r).Nonempty := by
      rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr]
      exact hsupport
    have hcovered' :=
      (squareOffsetAnchorNondivisorSupport_nonempty_iff_covered_of_candidate hn hr).mp
        hsupport'
    exact hnotcovered hcovered'

/-- An uncovered parity-safe candidate yields a square-cell prime. -/
theorem exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty
    {n : ℕ} (hn : 0 < n)
    (huncovered : (paritySafeUncoveredCandidates n).Nonempty) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  obtain ⟨r, hr⟩ := huncovered
  have hmem := (mem_paritySafeUncoveredCandidates_iff hn).mp hr
  have hesc : r ∈ escapingSquareOffsets n :=
    mem_escapingSquareOffsets.mpr ⟨
      (mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorOddPointCoprimeOffsets.mp hmem.1).1).1, hmem.2⟩
  have hesc' := mem_escapingSquareOffsets.mp hesc
  have hdisj :
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) :=
    supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hesc'.2
  refine ⟨n ^ 2 + r,
    prime_of_squareAnchoredSupportEscape hn hesc'.1 hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
    ⟨r, hesc'.1, rfl⟩

/-! ### PRIM-L036.4: exact local and global ledgers -/

/-- Each wave's extra cardinal is exactly its cardinal minus one. -/
theorem paritySafeActiveWaveExtraOffsets_card_eq
    (n q : ℕ) :
    (paritySafeActiveWaveExtraOffsets n q).card =
      (paritySafeActiveWaveOffsets n q).card - 1 := by
  classical
  by_cases hq : (paritySafeActiveWaveOffsets n q).Nonempty
  · rw [paritySafeActiveWaveExtraOffsets, dif_pos hq]
    exact Finset.card_erase_of_mem (Finset.min'_mem _ hq)
  · have hempty : paritySafeActiveWaveOffsets n q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hq
    simp [paritySafeActiveWaveExtraOffsets, hempty]

/-- The additive duplicate budget. -/
noncomputable def paritySafeWaveDuplicateBudgetExact (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorOddActivePrimes n,
    ((paritySafeActiveWaveOffsets n q).card - 1)

theorem paritySafeNonemptyActivePrimes_card_add_duplicateBudgetExact_eq_incidence
    (n : ℕ) :
    (paritySafeNonemptyActivePrimes n).card +
        paritySafeWaveDuplicateBudgetExact n =
      paritySafeIncidenceCount n := by
  classical
  have hterm : ∀ q ∈ squareAnchorOddActivePrimes n,
      (if (paritySafeActiveWaveOffsets n q).Nonempty then 1 else 0) +
          ((paritySafeActiveWaveOffsets n q).card - 1) =
        (paritySafeActiveWaveOffsets n q).card := by
    intro q hq
    by_cases hnonempty : (paritySafeActiveWaveOffsets n q).Nonempty
    · have hpos : 0 < (paritySafeActiveWaveOffsets n q).card :=
        Finset.card_pos.mpr hnonempty
      simp [hnonempty]
    · have hempty : paritySafeActiveWaveOffsets n q = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hempty]
  unfold paritySafeWaveDuplicateBudgetExact paritySafeIncidenceCount
  calc
    (paritySafeNonemptyActivePrimes n).card +
        ∑ q ∈ squareAnchorOddActivePrimes n,
          ((paritySafeActiveWaveOffsets n q).card - 1) =
      ∑ q ∈ squareAnchorOddActivePrimes n,
        (if (paritySafeActiveWaveOffsets n q).Nonempty then 1 else 0) +
      ∑ q ∈ squareAnchorOddActivePrimes n,
            ((paritySafeActiveWaveOffsets n q).card - 1) := by
          rw [paritySafeNonemptyActivePrimes, Finset.card_filter]
    _ = ∑ q ∈ squareAnchorOddActivePrimes n,
        ((if (paritySafeActiveWaveOffsets n q).Nonempty then 1 else 0) +
          ((paritySafeActiveWaveOffsets n q).card - 1)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeActiveWaveOffsets n q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q hq

/-! ### PRIM-L036.5: candidate-side excess and conservation -/

/-- Candidate-side support multiplicity beyond the first hit. -/
noncomputable def paritySafeSupportExcess (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
    ((paritySafeActiveSupport n r).card - 1)

theorem paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence
    (n : ℕ) :
    (paritySafeCoveredCandidates n).card + paritySafeSupportExcess n =
      paritySafeIncidenceCount n := by
  classical
  have hterm : ∀ r ∈ squareAnchorOddPointCoprimeOffsets n,
      (if (paritySafeActiveSupport n r).Nonempty then 1 else 0) +
          ((paritySafeActiveSupport n r).card - 1) =
        (paritySafeActiveSupport n r).card := by
    intro r hr
    by_cases hsupport : (paritySafeActiveSupport n r).Nonempty
    · have hpos : 0 < (paritySafeActiveSupport n r).card :=
        Finset.card_pos.mpr hsupport
      simp [hsupport]
    · have hempty : paritySafeActiveSupport n r = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hsupport
      simp [hempty]
  unfold paritySafeSupportExcess
  calc
    (paritySafeCoveredCandidates n).card +
        ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ((paritySafeActiveSupport n r).card - 1) =
      ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        (if (paritySafeActiveSupport n r).Nonempty then 1 else 0) +
          ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
            ((paritySafeActiveSupport n r).card - 1) := by
      rw [paritySafeCoveredCandidates, Finset.card_filter]
    _ = ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        ((if (paritySafeActiveSupport n r).Nonempty then 1 else 0) +
          ((paritySafeActiveSupport n r).card - 1)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        (paritySafeActiveSupport n r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hterm r hr
    _ = paritySafeIncidenceCount n :=
      (paritySafeIncidenceCount_eq_candidate_support_sum n).symm

theorem paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card
    (n : ℕ) :
    (paritySafeCoveredCandidates n).card +
        (paritySafeUncoveredCandidates n).card =
      (squareAnchorOddPointCoprimeOffsets n).card := by
  have hsub : paritySafeCoveredCandidates n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
    intro r hr
    exact (mem_paritySafeCoveredCandidates.mp hr).1
  calc
    (paritySafeCoveredCandidates n).card +
        (paritySafeUncoveredCandidates n).card =
      (paritySafeUncoveredCandidates n).card +
        (paritySafeCoveredCandidates n).card := Nat.add_comm _ _
    _ = (squareAnchorOddPointCoprimeOffsets n ∪
        paritySafeCoveredCandidates n).card := by
      unfold paritySafeUncoveredCandidates
      exact Finset.card_sdiff_add_card _ _
    _ = (squareAnchorOddPointCoprimeOffsets n).card := by
      rw [Finset.union_eq_left.mpr hsub]

/-- Prime-side and candidate-side ledgers satisfy exact incidence conservation.

With `H` nonempty waves, `B` duplicate budget, `U` uncovered candidates,
`C` all candidates, and `X` support excess, this is `H+B+U=C+X`. -/
theorem paritySafeIncidenceConservation
    (n : ℕ) :
    (paritySafeNonemptyActivePrimes n).card +
        paritySafeWaveDuplicateBudgetExact n +
        (paritySafeUncoveredCandidates n).card =
      (squareAnchorOddPointCoprimeOffsets n).card +
        paritySafeSupportExcess n := by
  have hprime :=
    paritySafeNonemptyActivePrimes_card_add_duplicateBudgetExact_eq_incidence n
  have hcandidate := paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence n
  have hsplit := paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card n
  omega

/-! ### PRIM-L036.6: corrected residual criterion and consumer -/

/-- Active waves split into nonempty and silent waves. -/
theorem paritySafeActive_card_eq_nonempty_add_silent
    (n : ℕ) :
    (squareAnchorOddActivePrimes n).card =
      (paritySafeNonemptyActivePrimes n).card +
        (paritySafeSilentActivePrimes n).card := by
  exact (paritySafeNonemptyActivePrimes_card_add_silent_card_eq_active_card n).symm

/-- The corrected deletion criterion is exactly the silent/uncovered balance. -/
theorem paritySafeResidualCriterion_iff_silent_lt_uncovered
    (n : ℕ) :
    (squareAnchorOddActivePrimes n).card +
          paritySafeWaveDuplicateBudgetExact n <
        (squareAnchorOddPointCoprimeOffsets n).card +
          paritySafeSupportExcess n ↔
      (paritySafeSilentActivePrimes n).card <
        (paritySafeUncoveredCandidates n).card := by
  have hconservation := paritySafeIncidenceConservation n
  have hactive := paritySafeActive_card_eq_nonempty_add_silent n
  constructor <;> intro h <;> omega

/-- A silent/uncovered surplus reaches the existing square-cell frontier. -/
theorem exists_prime_squareCell_of_silent_lt_uncovered
    {n : ℕ} (hn : 0 < n)
    (hbalance :
      (paritySafeSilentActivePrimes n).card <
        (paritySafeUncoveredCandidates n).card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hpos : 0 < (paritySafeUncoveredCandidates n).card := by
    have hnonneg : 0 ≤ (paritySafeSilentActivePrimes n).card := Nat.zero_le _
    omega
  exact exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (Finset.card_pos.mp hpos)

/-! ### PRIM-L036.7: supplied false-beam correction -/

/-- The suggested `(n,q)=(12,11)` beam is silent, but seat `11` is covered
by active prime `5`; hence `q ↦ q` is not a silent-to-uncovered injection. -/
theorem instruction051_n12_prime_eleven_silent_false_injection :
    11 ∈ squareAnchorOddActivePrimes 12 ∧
      paritySafeActiveWaveOffsets 12 11 = ∅ ∧
      11 ∈ squareAnchorOddPointCoprimeOffsets 12 ∧
      5 ∈ squareOffsetAnchorNondivisorSupport 12 11 ∧
      11 ∉ paritySafeUncoveredCandidates 12 := by
  have hq : 11 ∈ squareAnchorOddActivePrimes 12 := by
    apply mem_squareAnchorOddActivePrimes.mpr
    norm_num
  have hwave : paritySafeActiveWaveOffsets 12 11 = ∅ := by
    ext r
    constructor
    · intro hr
      have hr' := mem_paritySafeActiveWaveOffsets.mp hr
      have hseat := mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorOddPointCoprimeOffsets.mp hr'.1).1
      have hbound := hseat.1
      dsimp [SquareOffset] at hbound
      have hlow := hbound.1
      have hupp := hbound.2
      have hdiv := hr'.2
      interval_cases r <;>
        norm_num [SquareOffsetForbiddenBy, Nat.Coprime, Odd] at *
    · simp
  have hr : 11 ∈ squareAnchorOddPointCoprimeOffsets 12 := by
    norm_num [squareAnchorOddPointCoprimeOffsets, squareAnchorCoprimeOffsets,
      squareOffsets, SquareOffset, Nat.Coprime, Odd]
  have h5 : 5 ∈ squareOffsetAnchorNondivisorSupport 12 11 := by
    apply mem_squareOffsetAnchorNondivisorSupport.mpr
    norm_num [SquareOffsetForbiddenBy]
  have huncovered : 11 ∉ paritySafeUncoveredCandidates 12 := by
    intro h
    have hmem := (mem_paritySafeUncoveredCandidates_iff (by norm_num : 0 < 12)).mp h
    have hcovered : SquareOffsetCovered 12 11 := by
      apply squareOffsetCovered_iff_exists_prime_dvd.mpr
      exact ⟨5, by norm_num, by norm_num,
        (mem_squareOffsetAnchorNondivisorSupport.mp h5).2.2.2⟩
    exact hmem.2 hcovered
  exact ⟨hq, hwave, hr, h5, huncovered⟩

end DkMath.NumberTheory.Legendre
