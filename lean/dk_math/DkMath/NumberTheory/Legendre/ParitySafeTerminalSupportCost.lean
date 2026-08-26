/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost"

/-!
## ParitySafeTerminalSupportCost

PRIM-L060T introduces the terminal seat image and its membership surface.  A
terminal key returns to its canonical far residual seat, its next quotient `1`
gives the exact point equation `n ^ 2 + r = p * q * s`, and L060S already
provides the exact support-card decomposition at each terminal key.

The attempted next-seat injectivity is recorded as an engineering boundary in
the checkpoint report; this module therefore does not claim image-card
equality, disjoint support cost, or a global descent.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableTerminalSupport (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem terminal_rough_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  have hs := mem_paritySafeSurvivingFarProductKeys.mp ht.1
  exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
    hs.1).mpr ⟨hs.2, rfl⟩

private theorem terminal_canonical_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeCanonicalFarProductWaveOffsets n (p, (q, s)) := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  rw [← paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
    (mem_paritySafeSurvivingFarProductKeys.mp ht.1).1]
  exact terminal_rough_seat hkey

/-- A terminal key returns to its canonical far residual incidence. -/
theorem paritySafeTerminalSurvivingFarProductKey_residual_seat
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    (paritySafeFarProductWaveNextSeat n (p, (q, s)), (q, s)) ∈
      paritySafeCanonicalFarResidualTripleIncidences n := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  exact paritySafeCanonicalFarProductWaveOffset_mem_farResidual
    (mem_paritySafeSurvivingFarProductKeys.mp ht.1).1 (terminal_canonical_seat hkey)

/-- At a terminal key, the wave point is exactly the three-prime product. -/
theorem paritySafeTerminalSurvivingFarProductKey_point_eq
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) = p * q * s := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  have hs := mem_paritySafeSurvivingFarProductKeys.mp ht.1
  have hc := terminal_canonical_seat hkey
  have hp := paritySafeFarProductWaveCofactor_packet hs.1
    (mem_paritySafeCanonicalFarProductWaveOffsets.mp hc).1
  have hq := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    hs.1 hs.2.1
  rw [hq, ht.2] at hp
  simpa [paritySafeTripleProductModulus] using hp.2.1.symm

/-! ### PRIM-L060S: exact active support of a terminal point -/

/-- The ordered-prime and canonical-owner packet attached to a terminal key. -/
theorem paritySafeTerminalSurvivingFarProductKey_prime_packet
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    p ∈ squareAnchorOddActivePrimes n ∧
      q ∈ squareAnchorOddActivePrimes n ∧
      s ∈ squareAnchorOddActivePrimes n ∧
      p < q ∧ q < s ∧
      p = paritySafeCanonicalSupportPrime n
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
  have ht := mem_paritySafeTerminalSurvivingFarProductKeys.mp hkey
  have hs := mem_paritySafeSurvivingFarProductKeys.mp ht.1
  have htriple := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hs.1).1
  rcases htriple with ⟨hp, hq, hS, hpq, hqs⟩
  have hcanonical := (mem_paritySafeCanonicalFarProductWaveOffsets.mp
    (terminal_canonical_seat hkey)).2.2
  exact ⟨(mem_paritySafeTripleGatePrimes.mp hp).1, hq, hS, hpq, hqs,
    hcanonical⟩

/-- The three ordered primes of a terminal key lie in the active support of
its terminal seat. -/
theorem paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    p ∈ paritySafeActiveSupport n
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) ∧
      q ∈ paritySafeActiveSupport n
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) ∧
      s ∈ paritySafeActiveSupport n
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
  have hprime := paritySafeTerminalSurvivingFarProductKey_prime_packet hkey
  have hpoint := paritySafeTerminalSurvivingFarProductKey_point_eq hkey
  have hpdiv : p ∣ n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
    rw [hpoint]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl p) q) s
  have hqdiv : q ∣ n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
    rw [hpoint]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (dvd_refl q) p) s
  have hsdiv : s ∣ n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) := by
    rw [hpoint]
    exact dvd_mul_of_dvd_right (dvd_refl s) (p * q)
  exact ⟨mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hprime.1, hpdiv⟩,
    mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hprime.2.1, hqdiv⟩,
    mem_paritySafeActiveSupport_iff_dvd.mpr ⟨hprime.2.2.1, hsdiv⟩⟩

/-- Every active support prime of a terminal seat is one of its three ordered
factors.  This is the upper half of the terminal support-card sandwich. -/
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_cases
    {n p q s u : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (hu : u ∈ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p, (q, s)))) :
    u = p ∨ u = q ∨ u = s := by
  have hu' := mem_paritySafeActiveSupport_iff_dvd.mp hu
  have hpoint := paritySafeTerminalSurvivingFarProductKey_point_eq hkey
  have hudiv := hu'.2
  rw [hpoint] at hudiv
  have huprime := (mem_squareAnchorOddActivePrimes.mp hu'.1).1
  have hprime := paritySafeTerminalSurvivingFarProductKey_prime_packet hkey
  rcases (Nat.Prime.dvd_mul huprime).mp hudiv with hupq | hus
  · rcases (Nat.Prime.dvd_mul huprime).mp hupq with hup | huq
    · have heq := ((Nat.dvd_prime
        (mem_squareAnchorOddActivePrimes.mp hprime.1).1).mp hup).resolve_left
          huprime.ne_one
      exact Or.inl heq
    · have heq := ((Nat.dvd_prime
        (mem_squareAnchorOddActivePrimes.mp hprime.2.1).1).mp huq).resolve_left
          huprime.ne_one
      exact Or.inr <| Or.inl heq
  · have heq := ((Nat.dvd_prime
      (mem_squareAnchorOddActivePrimes.mp hprime.2.2.1).1).mp hus).resolve_left
        huprime.ne_one
    exact Or.inr <| Or.inr heq

/-- The displayed factors form the lower half of the terminal support-card
sandwich. -/
theorem paritySafeTerminalSurvivingFarProductKey_three_subset_activeSupport
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    ({p, q, s} : Finset ℕ) ⊆ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
  intro u hu
  have hthree :=
    paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport hkey
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact hthree.1
  · exact hthree.2.1
  · exact hthree.2.2

/-- The active support of a terminal seat has no fourth prime: divisibility of
the terminal point splits through the three prime factors. -/
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_subset_three
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeActiveSupport n
        (paritySafeFarProductWaveNextSeat n (p, (q, s))) ⊆
      ({p, q, s} : Finset ℕ) := by
  intro u hu
  rcases paritySafeTerminalSurvivingFarProductKey_activeSupport_cases hkey hu with
    h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

/-- A terminal key has exactly three active support primes. -/
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    (paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p, (q, s)))).card = 3 := by
  have hlower := Finset.card_le_card
    (paritySafeTerminalSurvivingFarProductKey_three_subset_activeSupport hkey)
  have hupper := Finset.card_le_card
    (paritySafeTerminalSurvivingFarProductKey_activeSupport_subset_three hkey)
  have hprime := paritySafeTerminalSurvivingFarProductKey_prime_packet hkey
  have hpqne : p ≠ q := Nat.ne_of_lt hprime.2.2.2.1
  have hqsne : q ≠ s := Nat.ne_of_lt hprime.2.2.2.2.1
  have hpsne : p ≠ s := Nat.ne_of_lt
    (lt_trans hprime.2.2.2.1 hprime.2.2.2.2.1)
  have hcard : ({p, q, s} : Finset ℕ).card = 3 := by
    simp [hpqne, hqsne, hpsne]
  rw [hcard] at hupper
  omega

/-- The supplied terminal witness `(n, r) = (16, 17)` has support-card `3`. -/
theorem paritySafeTerminalSupport_card_regression_16 :
    (paritySafeActiveSupport 16 17).card = 3 := by
  have hw := paritySafeCanonicalResidualTriple_witness_16_17
  rw [hw.2.1]
  norm_num

/-- The established terminal arithmetic witness at `n = 16`. -/
theorem paritySafeTerminalSupport_regression_16 :
    paritySafeFarProductWaveNextQuotient 16 (3, (7, 13)) = 1 ∧
      paritySafeFarProductWaveNextSeat 16 (3, (7, 13)) = 17 ∧
      16 ^ 2 + 17 = 3 * 7 * 13 := by
  norm_num [paritySafeFarProductWaveNextQuotient,
    paritySafeFarProductWaveNextSeat, paritySafeTripleProductModulus]

/-! ### PRIM-L060T: terminal seat image -/

/-- The set of next seats contributed by surviving terminal far-product keys. -/
noncomputable def paritySafeTerminalFarProductSeats (n : ℕ) : Finset ℕ :=
  (paritySafeTerminalSurvivingFarProductKeys n).image
    (paritySafeFarProductWaveNextSeat n)

/-- A terminal seat is exactly the next-seat image of a surviving terminal key. -/
@[simp] theorem mem_paritySafeTerminalFarProductSeats
    {n r : ℕ} :
    r ∈ paritySafeTerminalFarProductSeats n ↔
      ∃ key ∈ paritySafeTerminalSurvivingFarProductKeys n,
        paritySafeFarProductWaveNextSeat n key = r := by
  simp [paritySafeTerminalFarProductSeats]

end
end DkMath.NumberTheory.Legendre
