/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
import DkMath.NumberTheory.Legendre.QuotientSupport

#print "file: DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient"

/-!
## ParitySafeSupportExcessQuotient

This module transports the candidate-side support excess from PRIM-L036 to
canonical quotient co-support.  For a covered parity-safe candidate, the
least active old prime is selected and erased from the quotient support.  The
result is an exact finite incidence and factorization state: every remaining
direction is distinct from the selected one and divides the corresponding
anchored point together with it.  The construction distinguishes distinct
prime directions from repeated powers and does not assert descent, a
universal estimate, or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ### PRIM-L040.1: canonical selected support prime -/

/- The least active direction is used only on covered candidates; the default
   makes the definition total for convenient finite constructions. -/
noncomputable def paritySafeCanonicalSupportPrime (n r : ℕ) : ℕ :=
  if h : (paritySafeActiveSupport n r).Nonempty then
    (paritySafeActiveSupport n r).min' h
  else 0

/-- A covered candidate has a canonical active support prime. -/
theorem paritySafeCanonicalSupportPrime_mem_activeSupport
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r := by
  classical
  have hnonempty := (mem_paritySafeCoveredCandidates.mp hr).2
  rw [paritySafeCanonicalSupportPrime, dif_pos hnonempty]
  exact Finset.min'_mem _ hnonempty

/-- The canonical prime has the old nondivisor and parity-safe active packets. -/
theorem paritySafeCanonicalSupportPrime_packet
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r ∧
      paritySafeCanonicalSupportPrime n r ∈
        squareOffsetAnchorNondivisorSupport n r ∧
      paritySafeCanonicalSupportPrime n r ∈ squareAnchorOddActivePrimes n := by
  classical
  have hr' := mem_paritySafeCoveredCandidates.mp hr
  have hpactive := paritySafeCanonicalSupportPrime_mem_activeSupport hr
  have hsupport :=
    squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr'.1
  have hpoff : paritySafeCanonicalSupportPrime n r ∈
      squareOffsetAnchorNondivisorSupport n r := by
    rw [hsupport]
    exact hpactive
  have hpprime : paritySafeCanonicalSupportPrime n r ∈
      squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hpactive
    exact (Finset.mem_filter.mp hpactive).1
  exact ⟨hr'.1, hpactive, hpoff, hpprime⟩

/-! ### PRIM-L040.2: exact per-seat quotient transport -/

/-- Support excess at a covered seat is exactly erased quotient co-support. -/
theorem paritySafeSupportExcess_seat_eq_quotientCoSupport_card
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    (paritySafeActiveSupport n r).card - 1 =
      ((squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r)).card := by
  have hr' := mem_paritySafeCoveredCandidates.mp hr
  have hpoff := (paritySafeCanonicalSupportPrime_packet hr).2.2.1
  have hsupport :=
    squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr'.1
  calc
    (paritySafeActiveSupport n r).card - 1 =
        (squareOffsetAnchorNondivisorSupport n r).card - 1 := by
          rw [hsupport]
    _ = ((squareOffsetAnchorNondivisorSupport n r).erase
        (paritySafeCanonicalSupportPrime n r)).card := by
          rw [Finset.card_erase_of_mem hpoff]
    _ = ((squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r)).card := by
          rw [erase_squareQuotientSupport_eq_erase_offsetSupport hpoff]

/-- The complete L036 support excess is a sum over covered candidates only. -/
theorem paritySafeSupportExcess_eq_covered_quotientCoSupport_sum
    (n : ℕ) :
    paritySafeSupportExcess n =
      ∑ r ∈ paritySafeCoveredCandidates n,
        ((squareQuotientAnchorNondivisorSupport n
          (paritySafeCanonicalSupportPrime n r) r).erase
            (paritySafeCanonicalSupportPrime n r)).card := by
  classical
  unfold paritySafeSupportExcess
  rw [paritySafeCoveredCandidates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hnonempty : (paritySafeActiveSupport n r).Nonempty
  · have hcovered : r ∈ paritySafeCoveredCandidates n :=
      mem_paritySafeCoveredCandidates.mpr ⟨hr, hnonempty⟩
    simpa [hnonempty] using
      (paritySafeSupportExcess_seat_eq_quotientCoSupport_card hcovered)
  · have hempty : paritySafeActiveSupport n r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hempty]

/-! ### PRIM-L040.3: canonical quotient co-support incidences -/

/-- Finite `(candidate, quotient-direction)` incidences after canonical erasure. -/
noncomputable def paritySafeCanonicalQuotientCoSupportIncidences
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeCoveredCandidates n).product (squareAnchorOddActivePrimes n) |>.filter
    (fun pair => pair.2 ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n pair.1) pair.1).erase
          (paritySafeCanonicalSupportPrime n pair.1))

/-- The incidence set has exactly the transported support-excess cardinality. -/
theorem paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess
    (n : ℕ) :
    (paritySafeCanonicalQuotientCoSupportIncidences n).card =
      paritySafeSupportExcess n := by
  classical
  unfold paritySafeCanonicalQuotientCoSupportIncidences
  calc
    Finset.card (((paritySafeCoveredCandidates n).product
        (squareAnchorOddActivePrimes n)).filter
        (fun pair => pair.2 ∈
          (squareQuotientAnchorNondivisorSupport n
            (paritySafeCanonicalSupportPrime n pair.1) pair.1).erase
              (paritySafeCanonicalSupportPrime n pair.1))) =
      ∑ pair ∈ (paritySafeCoveredCandidates n).product
        (squareAnchorOddActivePrimes n),
        if pair.2 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n pair.1) pair.1).erase
              (paritySafeCanonicalSupportPrime n pair.1) then 1 else 0 := by
      simp
    _ =
        ∑ r ∈ paritySafeCoveredCandidates n,
          ∑ q ∈ squareAnchorOddActivePrimes n,
            if q ∈
                (squareQuotientAnchorNondivisorSupport n
                  (paritySafeCanonicalSupportPrime n r) r).erase
                  (paritySafeCanonicalSupportPrime n r) then 1 else 0 := by
      exact Finset.sum_product'
        (paritySafeCoveredCandidates n) (squareAnchorOddActivePrimes n)
        (fun r q => if q ∈
          (squareQuotientAnchorNondivisorSupport n
            (paritySafeCanonicalSupportPrime n r) r).erase
              (paritySafeCanonicalSupportPrime n r) then 1 else 0)
    _ = ∑ r ∈ paritySafeCoveredCandidates n,
          ((squareQuotientAnchorNondivisorSupport n
            (paritySafeCanonicalSupportPrime n r) r).erase
              (paritySafeCanonicalSupportPrime n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      have hfilter :
          Finset.filter (fun q => q ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r))
            (squareAnchorOddActivePrimes n) =
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r) := by
        ext q
        simp only [Finset.mem_filter]
        constructor
        · intro hq
          exact hq.2
        · intro hq
          have hpoff :=
            (paritySafeCanonicalSupportPrime_packet hr).2.2.1
          have hsupport :=
            squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
              (mem_paritySafeCoveredCandidates.mp hr).1
          have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
            hpoff (Finset.erase_subset _ _ hq)
          have hqactiveSupport : q ∈ paritySafeActiveSupport n r := by
            rw [← hsupport]
            exact hqoff
          rw [paritySafeActiveSupport] at hqactiveSupport
          exact ⟨(Finset.mem_filter.mp hqactiveSupport).1, hq⟩
      exact congrArg Finset.card hfilter
    _ = paritySafeSupportExcess n :=
      (paritySafeSupportExcess_eq_covered_quotientCoSupport_sum n).symm

/-! ### PRIM-L040.4: factorization packet for every transported incidence -/

/--
Every canonical quotient co-support incidence yields two distinct active old
primes.  Their product divides the anchored point, and remains coprime to the
even anchor modulus.
-/
theorem paritySafeCanonicalQuotientCoSupportIncidence_packet
    {n r q : ℕ}
    (hinc : (r, q) ∈ paritySafeCanonicalQuotientCoSupportIncidences n) :
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      paritySafeCanonicalSupportPrime n r ∈ squareAnchorOddActivePrimes n ∧
      q ∈ squareAnchorOddActivePrimes n ∧
      paritySafeCanonicalSupportPrime n r ≠ q ∧
      q ∣ squareOffsetSupportQuotient n
        (paritySafeCanonicalSupportPrime n r) r ∧
      paritySafeCanonicalSupportPrime n r * q ∣ n ^ 2 + r ∧
      Nat.Coprime (2 * n)
        (paritySafeCanonicalSupportPrime n r * q) := by
  classical
  have hinc' := Finset.mem_filter.mp hinc
  have hpair := Finset.mem_product.mp hinc'.1
  have hr : r ∈ paritySafeCoveredCandidates n := by simpa using hpair.1
  have hqactive : q ∈ squareAnchorOddActivePrimes n := by simpa using hpair.2
  have hqerase' : q ∈ (squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r) := by
    simpa using hinc'.2
  have hqquot : q ∈ squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r :=
    (Finset.mem_erase.mp hqerase').2
  have hqne : q ≠ paritySafeCanonicalSupportPrime n r := by
    exact (Finset.mem_erase.mp hqerase').1
  have hpack := paritySafeCanonicalSupportPrime_packet hr
  have hqdiv := (mem_squareQuotientAnchorNondivisorSupport.mp hqquot).2.2.2
  have hpdiv : paritySafeCanonicalSupportPrime n r ∣ n ^ 2 + r :=
    (mem_squareOffsetAnchorNondivisorSupport.mp hpack.2.2.1).2.2.2
  have hfactor := mul_squareOffsetSupportQuotient_eq hpdiv
  have hpqdiv : paritySafeCanonicalSupportPrime n r * q ∣ n ^ 2 + r := by
    rcases hqdiv with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      n ^ 2 + r = paritySafeCanonicalSupportPrime n r *
          squareOffsetSupportQuotient
            n (paritySafeCanonicalSupportPrime n r) r := hfactor.symm
      _ = paritySafeCanonicalSupportPrime n r * (q * t) := by rw [ht]
      _ = paritySafeCanonicalSupportPrime n r * q * t := by ring
  have hpcop := (activePrime_reducedResidue_packet hpack.2.2.2).2.2.2.2
  have hqcop := (activePrime_reducedResidue_packet hqactive).2.2.2.2
  have hpqcop : Nat.Coprime (2 * n)
      (paritySafeCanonicalSupportPrime n r * q) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hpcop, hqcop⟩
  exact ⟨hpack.1, hpack.2.2.2, hqactive, hqne.symm, hqdiv, hpqdiv, hpqcop⟩

/-! ### PRIM-L040.5: direction/depth false beam -/

/-- The `(n,r)=(5,2)` seat has one direction but selected-prime depth three. -/
theorem paritySafeDirectionDepth_false_beam_five_two :
    2 ∈ squareAnchorOddPointCoprimeOffsets 5 ∧
      paritySafeActiveSupport 5 2 = {3} ∧
      (paritySafeActiveSupport 5 2).card - 1 = 0 ∧
      3 ∣ squareOffsetSupportQuotient 5 3 2 ∧
      3 ∈ squareQuotientAnchorNondivisorSupport 5 3 2 ∧
      ((squareQuotientAnchorNondivisorSupport 5 3 2).erase 3).card = 0 := by
  classical
  have hcandidate : 2 ∈ squareAnchorOddPointCoprimeOffsets 5 := by
    apply mem_squareAnchorOddPointCoprimeOffsets.mpr
    norm_num [mem_squareAnchorCoprimeOffsets, SquareOffset, Odd]
  have hsupport : paritySafeActiveSupport 5 2 = {3} := by
    ext q
    constructor
    · intro hq
      rw [paritySafeActiveSupport] at hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime := (mem_squareAnchorOddActivePrimes.mp hq'.1).1
      have hqle := (mem_squareAnchorOddActivePrimes.mp hq'.1).2.1
      interval_cases q <;> simp_all [SquareOffsetForbiddenBy]
    · intro hq
      have hq3 : q = 3 := by simpa using hq
      subst q
      rw [paritySafeActiveSupport]
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_squareAnchorOddActivePrimes.mpr
        norm_num [squareAnchorOddActivePrimes, squareAnchorNondivisorPrimes,
          primeScalesUpTo]
      · norm_num [SquareOffsetForbiddenBy]
  have hcard : (paritySafeActiveSupport 5 2).card - 1 = 0 := by
    rw [hsupport]
    norm_num
  have hquot : 3 ∣ squareOffsetSupportQuotient 5 3 2 := by
    norm_num [squareOffsetSupportQuotient]
  have hqmem : 3 ∈ squareQuotientAnchorNondivisorSupport 5 3 2 := by
    apply mem_squareQuotientAnchorNondivisorSupport.mpr
    norm_num [squareOffsetSupportQuotient, squareAnchorNondivisorPrimes,
      primeScalesUpTo]
  have herase :
      ((squareQuotientAnchorNondivisorSupport 5 3 2).erase 3).card = 0 := by
    have hqSupport : squareQuotientAnchorNondivisorSupport 5 3 2 = {3} := by
      ext q
      constructor
      · intro hq
        have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
        have hqprime := hq'.1
        have hqle := hq'.2.1
        have hqdiv := hq'.2.2.2
        interval_cases q <;> simp_all [squareOffsetSupportQuotient]
      · intro hq
        have hq3 : q = 3 := by simpa using hq
        subst q
        exact hqmem
    rw [hqSupport]
    simp
  exact ⟨hcandidate, hsupport, hcard, hquot, hqmem, herase⟩

end DkMath.NumberTheory.Legendre
