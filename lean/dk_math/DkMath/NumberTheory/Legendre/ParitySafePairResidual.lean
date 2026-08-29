/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
import DkMath.NumberTheory.Legendre.LocalizedObstruction

#print "file: DkMath.NumberTheory.Legendre.ParitySafePairResidual"

/-!
## ParitySafePairResidual

This module records the next finite layer after the parity-safe support-excess
ledger.  Every covered candidate contributes its unordered active-prime pairs;
the canonical selected prime splits those pairs into a star and a residual
pair ledger.  The residual pairs lift to a finite triple-direction incidence
set in the erased quotient support.

All statements here are exact finite-support or divisibility packets.  The
module does not add a hypergraph theory, an asymptotic estimate, a sieve, a
descent, or a proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-! ### PRIM-L041.1: star and residual pair ledgers -/

/-- The parity-safe unordered active-prime pair ledger. -/
noncomputable def paritySafePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
    Nat.choose (paritySafeActiveSupport n r).card 2

/-- The unordered pairs left after removing the canonical star edge. -/
noncomputable def paritySafeResidualPairMass (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2

/-- The pair ledger is bounded by the localized coprime pair ledger. -/
theorem paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount
    (n : ℕ) :
    paritySafePrimePairOverlapCount n ≤
      squareAnchorCoprimePrimePairOverlapCount n := by
  classical
  unfold paritySafePrimePairOverlapCount
  calc
    (∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        Nat.choose (paritySafeActiveSupport n r).card 2) =
      ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
        hr]
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact (mem_squareAnchorOddPointCoprimeOffsets.mp hr).1
      · intro r _ _
        exact Nat.zero_le _
    _ = squareAnchorCoprimePrimePairOverlapCount n :=
      (squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support n).symm

private theorem choose_two_eq_sub_one_add_choose_sub_one (k : ℕ) :
    Nat.choose k 2 = (k - 1) + Nat.choose (k - 1) 2 := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_succ_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]

/-- The exact star-plus-residual decomposition of the pair ledger. -/
theorem paritySafePrimePairOverlapCount_eq_supportExcess_add_residual
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafeSupportExcess n + paritySafeResidualPairMass n := by
  classical
  unfold paritySafePrimePairOverlapCount paritySafeSupportExcess
    paritySafeResidualPairMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact (choose_two_eq_sub_one_add_choose_sub_one
    (paritySafeActiveSupport n r).card)

/-- Residual mass vanishes exactly when every active support has size at most 2. -/
theorem paritySafeResidualPairMass_eq_zero_iff
    (n : ℕ) :
    paritySafeResidualPairMass n = 0 ↔
      ∀ r ∈ squareAnchorOddPointCoprimeOffsets n,
        (paritySafeActiveSupport n r).card ≤ 2 := by
  classical
  unfold paritySafeResidualPairMass
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h r hr
      by_contra hlarge
      have hchoose : 0 < Nat.choose
          ((paritySafeActiveSupport n r).card - 1) 2 := by
        apply Nat.choose_pos
        omega
      have := h r hr
      omega
    · intro h r hr
      have hk := h r hr
      exact Nat.choose_eq_zero_of_lt (by omega :
        (paritySafeActiveSupport n r).card - 1 < 2)
  · intro r hr
    exact Nat.zero_le _

/-- A support of size at least three contributes positive residual mass. -/
theorem paritySafeResidualPairMass_pos_iff
    (n : ℕ) :
    0 < paritySafeResidualPairMass n ↔
      ∃ r ∈ squareAnchorOddPointCoprimeOffsets n,
        3 ≤ (paritySafeActiveSupport n r).card := by
  classical
  unfold paritySafeResidualPairMass
  constructor
  · intro hpos
    by_contra hnone
    have hzero : ∀ r ∈ squareAnchorOddPointCoprimeOffsets n,
        (paritySafeActiveSupport n r).card ≤ 2 := by
      intro r hr
      by_contra hlarge
      exact hnone ⟨r, hr, by omega⟩
    have hzero' := (paritySafeResidualPairMass_eq_zero_iff n).mpr hzero
    have hz : (∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        Nat.choose ((paritySafeActiveSupport n r).card - 1) 2) = 0 := by
      simpa [paritySafeResidualPairMass] using hzero'
    omega
  · rintro ⟨r, hr, hcard⟩
    have hchoose : 0 < Nat.choose
        ((paritySafeActiveSupport n r).card - 1) 2 := by
      apply Nat.choose_pos
      omega
    have hle := Finset.single_le_sum
      (f := fun s => Nat.choose ((paritySafeActiveSupport n s).card - 1) 2)
      (fun s _ => Nat.zero_le _) hr
    omega

/-! ### PRIM-L041.2: canonical residual triple incidence -/

/--
Finite triples `(r,(q,s))` with `q < s` in the erased canonical quotient
co-support.  The nested product representation is definitionally finite and
keeps the candidate coordinate visible for the factorization packet.
-/
noncomputable def paritySafeCanonicalResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  ((paritySafeCoveredCandidates n).product
      ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n))).filter
    (fun triple =>
      triple.2.1 < triple.2.2 ∧
      triple.2.1 ∈
        (squareQuotientAnchorNondivisorSupport n
          (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
            (paritySafeCanonicalSupportPrime n triple.1) ∧
      triple.2.2 ∈
        (squareQuotientAnchorNondivisorSupport n
          (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
            (paritySafeCanonicalSupportPrime n triple.1))

private theorem erased_quotientCoSupport_subset_activeSupport
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    (squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r) ⊆
      paritySafeActiveSupport n r := by
  intro q hq
  have hp := (paritySafeCanonicalSupportPrime_packet hr).2.2.1
  have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp
    (Finset.erase_subset _ _ hq)
  rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
    (mem_paritySafeCoveredCandidates.mp hr).1] at hqoff
  exact hqoff

/-- The local residual pair filter is exactly `upperPairs` of the erased support. -/
private theorem paritySafeCanonicalResidualTriple_pair_filter_eq_upperPairs
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n)).filter
        (fun pair =>
          pair.1 < pair.2 ∧
          pair.1 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r) ∧
          pair.2 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r)) =
      upperPairs ((squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r)) := by
  classical
  ext pair
  rcases pair with ⟨q, s⟩
  have hsub := erased_quotientCoSupport_subset_activeSupport hr
  let E := (squareQuotientAnchorNondivisorSupport n
    (paritySafeCanonicalSupportPrime n r) r).erase
      (paritySafeCanonicalSupportPrime n r)
  change (q, s) ∈
      ((squareAnchorOddActivePrimes n).product
        (squareAnchorOddActivePrimes n)).filter
        (fun pair => pair.1 < pair.2 ∧ pair.1 ∈ E ∧ pair.2 ∈ E) ↔
    (q, s) ∈ E.offDiag.filter (fun pair => pair.1 < pair.2)
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    have hlt := h'.2.1
    have hq := h'.2.2.1
    have hs := h'.2.2.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_offDiag.mpr ⟨hq, hs, by omega⟩, hlt⟩
  · intro h
    have h' := Finset.mem_filter.mp h
    have hdiag := Finset.mem_offDiag.mp h'.1
    have hq := hdiag.1
    have hs := hdiag.2.1
    have hlt := h'.2
    have hqactive : q ∈ squareAnchorOddActivePrimes n := by
      exact (Finset.mem_filter.mp (hsub hq)).1
    have hsactive : s ∈ squareAnchorOddActivePrimes n := by
      exact (Finset.mem_filter.mp (hsub hs)).1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hqactive, hsactive⟩, hlt, hq, hs⟩

/-- The residual triple incidence has the exact residual cardinality. -/
theorem paritySafeCanonicalResidualTripleIncidences_card_eq_residual
    (n : ℕ) :
    (paritySafeCanonicalResidualTripleIncidences n).card =
      paritySafeResidualPairMass n := by
  classical
  unfold paritySafeCanonicalResidualTripleIncidences
  calc
    Finset.card (((paritySafeCoveredCandidates n).product
        ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n))).filter
        (fun triple =>
          triple.2.1 < triple.2.2 ∧
          triple.2.1 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
                (paritySafeCanonicalSupportPrime n triple.1) ∧
          triple.2.2 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
                (paritySafeCanonicalSupportPrime n triple.1))) =
      ∑ triple ∈ (paritySafeCoveredCandidates n).product
        ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n)),
        if triple.2.1 < triple.2.2 ∧
            triple.2.1 ∈
              (squareQuotientAnchorNondivisorSupport n
                (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
                  (paritySafeCanonicalSupportPrime n triple.1) ∧
            triple.2.2 ∈
              (squareQuotientAnchorNondivisorSupport n
                (paritySafeCanonicalSupportPrime n triple.1) triple.1).erase
                  (paritySafeCanonicalSupportPrime n triple.1) then 1 else 0 := by
      simp
    _ = ∑ r ∈ paritySafeCoveredCandidates n,
        ∑ pair ∈ (squareAnchorOddActivePrimes n).product
          (squareAnchorOddActivePrimes n),
          if pair.1 < pair.2 ∧
              pair.1 ∈
                (squareQuotientAnchorNondivisorSupport n
                  (paritySafeCanonicalSupportPrime n r) r).erase
                    (paritySafeCanonicalSupportPrime n r) ∧
              pair.2 ∈
                (squareQuotientAnchorNondivisorSupport n
                  (paritySafeCanonicalSupportPrime n r) r).erase
                    (paritySafeCanonicalSupportPrime n r) then 1 else 0 := by
      exact Finset.sum_product'
        (paritySafeCoveredCandidates n)
        ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n))
        (fun r pair => if pair.1 < pair.2 ∧
          pair.1 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r) ∧
          pair.2 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r) then 1 else 0)
    _ = ∑ r ∈ paritySafeCoveredCandidates n,
        Nat.choose
          (((squareQuotientAnchorNondivisorSupport n
            (paritySafeCanonicalSupportPrime n r) r).erase
              (paritySafeCanonicalSupportPrime n r)).card) 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      rw [paritySafeCanonicalResidualTriple_pair_filter_eq_upperPairs hr]
      exact card_upperPairs_eq_choose _
    _ = ∑ r ∈ paritySafeCoveredCandidates n,
        Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [paritySafeSupportExcess_seat_eq_quotientCoSupport_card hr]
    _ = paritySafeResidualPairMass n := by
      unfold paritySafeResidualPairMass
      let f : ℕ → ℕ := fun r =>
        Nat.choose ((paritySafeActiveSupport n r).card - 1) 2
      change (∑ r ∈ paritySafeCoveredCandidates n, f r) =
        ∑ r ∈ squareAnchorOddPointCoprimeOffsets n, f r
      have hsubset : paritySafeCoveredCandidates n ⊆
          squareAnchorOddPointCoprimeOffsets n := by
        intro r hr
        exact (mem_paritySafeCoveredCandidates.mp hr).1
      have houtside : ∀ r ∈ squareAnchorOddPointCoprimeOffsets n,
          r ∉ paritySafeCoveredCandidates n → f r = 0 := by
        intro r hr hnot
        have hnonempty : ¬ (paritySafeActiveSupport n r).Nonempty := by
          intro h
          apply hnot
          exact mem_paritySafeCoveredCandidates.mpr ⟨hr, h⟩
        have hempty : paritySafeActiveSupport n r = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
        simp [f, hempty]
      exact Finset.sum_subset hsubset houtside

/-! ### PRIM-L041.3: triple factorization packet -/

/-- Every residual triple gives three distinct active prime directions. -/
theorem paritySafeCanonicalResidualTripleIncidence_packet
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      paritySafeCanonicalSupportPrime n r ∈ squareAnchorOddActivePrimes n ∧
      q ∈ squareAnchorOddActivePrimes n ∧
      s ∈ squareAnchorOddActivePrimes n ∧
      paritySafeCanonicalSupportPrime n r ≠ q ∧
      paritySafeCanonicalSupportPrime n r ≠ s ∧
      q ≠ s ∧
      paritySafeCanonicalSupportPrime n r * q * s ∣ n ^ 2 + r ∧
      Nat.Coprime (2 * n)
        (paritySafeCanonicalSupportPrime n r * q * s) := by
  classical
  have hinc' := Finset.mem_filter.mp hinc
  have hproduct := Finset.mem_product.mp hinc'.1
  have hpair := Finset.mem_product.mp hproduct.2
  have hr : r ∈ paritySafeCoveredCandidates n := hproduct.1
  have hqactive : q ∈ squareAnchorOddActivePrimes n := hpair.1
  have hsactive : s ∈ squareAnchorOddActivePrimes n := hpair.2
  have hcond := hinc'.2
  have hlt : q < s := hcond.1
  have hqerase : q ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r) := hcond.2.1
  have hserase : s ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r) := hcond.2.2
  have hqquot := (Finset.mem_erase.mp hqerase).2
  have hsquot := (Finset.mem_erase.mp hserase).2
  have hpq : paritySafeCanonicalSupportPrime n r ≠ q :=
    (Finset.mem_erase.mp hqerase).1.symm
  have hps : paritySafeCanonicalSupportPrime n r ≠ s :=
    (Finset.mem_erase.mp hserase).1.symm
  have hqs : q ≠ s := by omega
  have hpack := paritySafeCanonicalSupportPrime_packet hr
  have hqdiv := (mem_squareQuotientAnchorNondivisorSupport.mp hqquot).2.2.2
  have hsdiv := (mem_squareQuotientAnchorNondivisorSupport.mp hsquot).2.2.2
  have hpdiv : paritySafeCanonicalSupportPrime n r ∣ n ^ 2 + r :=
    (mem_squareOffsetAnchorNondivisorSupport.mp hpack.2.2.1).2.2.2
  have hqprime := (mem_squareQuotientAnchorNondivisorSupport.mp hqquot).1
  have hsprime := (mem_squareQuotientAnchorNondivisorSupport.mp hsquot).1
  have hqscop : Nat.Coprime q s :=
    (Nat.coprime_primes hqprime hsprime).2 hqs
  have hqsmuldiv : q * s ∣
      squareOffsetSupportQuotient n
        (paritySafeCanonicalSupportPrime n r) r :=
    hqscop.mul_dvd_of_dvd_of_dvd hqdiv hsdiv
  have hfactor := mul_squareOffsetSupportQuotient_eq hpdiv
  have htriplediv : paritySafeCanonicalSupportPrime n r * q * s ∣
      n ^ 2 + r := by
    rcases hqsmuldiv with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      n ^ 2 + r = paritySafeCanonicalSupportPrime n r *
          squareOffsetSupportQuotient n
            (paritySafeCanonicalSupportPrime n r) r := hfactor.symm
      _ = paritySafeCanonicalSupportPrime n r * (q * s * t) := by rw [ht]
      _ = paritySafeCanonicalSupportPrime n r * q * s * t := by ring
  have hpcop := (activePrime_reducedResidue_packet hpack.2.2.2).2.2.2.2
  have hqcop := (activePrime_reducedResidue_packet hqactive).2.2.2.2
  have hscop := (activePrime_reducedResidue_packet hsactive).2.2.2.2
  have hcop : Nat.Coprime (2 * n)
      (paritySafeCanonicalSupportPrime n r * q * s) := by
    rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    exact ⟨⟨hpcop, hqcop⟩, hscop⟩
  exact ⟨hpack.1, hpack.2.2.2, hqactive, hsactive, hpq, hps, hqs,
    htriplediv, hcop⟩

/-! ### PRIM-L041.4: supplied three-direction witness -/

/--
The seat `n = 16`, `r = 17` has active support `{3, 7, 13}`.  Thus its
canonical star has two edges, its residual ledger has one pair, and the pair
`(7,13)` gives the factorization packet `3 * 7 * 13 ∣ 16^2 + 17`.
-/
theorem paritySafeCanonicalResidualTriple_witness_16_17 :
    17 ∈ squareAnchorOddPointCoprimeOffsets 16 ∧
      paritySafeActiveSupport 16 17 = {3, 7, 13} ∧
      paritySafeCanonicalSupportPrime 16 17 = 3 ∧
      (paritySafeActiveSupport 16 17).card - 1 = 2 ∧
      Nat.choose (paritySafeActiveSupport 16 17).card 2 = 3 ∧
      Nat.choose ((paritySafeActiveSupport 16 17).card - 1) 2 = 1 ∧
      (17, (7, 13)) ∈ paritySafeCanonicalResidualTripleIncidences 16 ∧
      3 * 7 * 13 ∣ 16 ^ 2 + 17 := by
  classical
  have hcandidate : 17 ∈ squareAnchorOddPointCoprimeOffsets 16 := by
    apply mem_squareAnchorOddPointCoprimeOffsets.mpr
    norm_num [mem_squareAnchorCoprimeOffsets, SquareOffset, Odd]
  have hsupport : paritySafeActiveSupport 16 17 = {3, 7, 13} := by
    ext q
    constructor
    · intro hq
      rw [paritySafeActiveSupport] at hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime := (mem_squareAnchorOddActivePrimes.mp hq'.1).1
      have hqle := (mem_squareAnchorOddActivePrimes.mp hq'.1).2.1
      interval_cases q <;> simp_all [SquareOffsetForbiddenBy]
    · intro hq
      have hq' : q = 3 ∨ q = 7 ∨ q = 13 := by simpa using hq
      rcases hq' with rfl | rfl | rfl
      · rw [paritySafeActiveSupport]
        apply Finset.mem_filter.mpr
        constructor
        · apply mem_squareAnchorOddActivePrimes.mpr
          norm_num [squareAnchorOddActivePrimes, squareAnchorNondivisorPrimes,
            primeScalesUpTo]
        · norm_num [SquareOffsetForbiddenBy]
      · rw [paritySafeActiveSupport]
        apply Finset.mem_filter.mpr
        constructor
        · apply mem_squareAnchorOddActivePrimes.mpr
          norm_num [squareAnchorOddActivePrimes, squareAnchorNondivisorPrimes,
            primeScalesUpTo]
        · norm_num [SquareOffsetForbiddenBy]
      · rw [paritySafeActiveSupport]
        apply Finset.mem_filter.mpr
        constructor
        · apply mem_squareAnchorOddActivePrimes.mpr
          norm_num [squareAnchorOddActivePrimes, squareAnchorNondivisorPrimes,
            primeScalesUpTo]
        · norm_num [SquareOffsetForbiddenBy]
  have hcovered : 17 ∈ paritySafeCoveredCandidates 16 := by
    apply mem_paritySafeCoveredCandidates.mpr
    exact ⟨hcandidate, by rw [hsupport]; simp⟩
  have hcanonical : paritySafeCanonicalSupportPrime 16 17 = 3 := by
    have hnonempty := (mem_paritySafeCoveredCandidates.mp hcovered).2
    rw [paritySafeCanonicalSupportPrime, dite_eq_left hnonempty]
    apply (Finset.min'_eq_iff
      (s := paritySafeActiveSupport 16 17) (H := hnonempty) 3).2
    constructor
    · rw [hsupport]
      simp
    · intro q hq
      rw [hsupport] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      omega
  have h7 : 7 ∈ squareQuotientAnchorNondivisorSupport 16 3 17 := by
    apply mem_squareQuotientAnchorNondivisorSupport.mpr
    norm_num [squareOffsetSupportQuotient, squareAnchorNondivisorPrimes,
      primeScalesUpTo]
  have h13 : 13 ∈ squareQuotientAnchorNondivisorSupport 16 3 17 := by
    apply mem_squareQuotientAnchorNondivisorSupport.mpr
    norm_num [squareOffsetSupportQuotient, squareAnchorNondivisorPrimes,
      primeScalesUpTo]
  have htriple : (17, (7, 13)) ∈
      paritySafeCanonicalResidualTripleIncidences 16 := by
    apply Finset.mem_filter.mpr
    have hprod : (17, (7, 13)) ∈
        (paritySafeCoveredCandidates 16).product
          ((squareAnchorOddActivePrimes 16).product
            (squareAnchorOddActivePrimes 16)) := by
      apply Finset.mem_product.mpr
      refine ⟨hcovered, ?_⟩
      apply Finset.mem_product.mpr
      constructor <;> apply mem_squareAnchorOddActivePrimes.mpr <;> norm_num
    refine ⟨hprod, ?_⟩
    change 7 < 13 ∧
      7 ∈ (squareQuotientAnchorNondivisorSupport 16
        (paritySafeCanonicalSupportPrime 16 17) 17).erase
          (paritySafeCanonicalSupportPrime 16 17) ∧
      13 ∈ (squareQuotientAnchorNondivisorSupport 16
        (paritySafeCanonicalSupportPrime 16 17) 17).erase
        (paritySafeCanonicalSupportPrime 16 17)
    rw [hcanonical]
    refine ⟨by norm_num, ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      exact ⟨by norm_num, h7⟩
    · apply Finset.mem_erase.mpr
      exact ⟨by norm_num, h13⟩
  have hstar : (paritySafeActiveSupport 16 17).card - 1 = 2 := by
    rw [hsupport]
    norm_num
  have hpair : Nat.choose (paritySafeActiveSupport 16 17).card 2 = 3 := by
    rw [hsupport]
    norm_num
  have hres : Nat.choose ((paritySafeActiveSupport 16 17).card - 1) 2 = 1 := by
    rw [hsupport]
    norm_num
  exact ⟨hcandidate, hsupport, hcanonical, hstar, hpair, hres, htriple,
    by norm_num⟩

end DkMath.NumberTheory.Legendre
