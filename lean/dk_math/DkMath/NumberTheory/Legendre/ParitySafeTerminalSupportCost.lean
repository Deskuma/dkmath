/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost"

/-!
## ParitySafeTerminalSupportCost

PRIM-L060U closes direct same-seat reconstruction from the L060S exact
three-support surface.  A terminal key returns to its canonical far residual
seat, its next quotient `1` gives the exact point equation
`n ^ 2 + r = p * q * s`, and equal terminal seats determine equal ordered keys.

The resulting finite image has the same card as its key domain.  The module
also closes the bounded L060V disjoint weighted support-cost ledger, but does
not add near counting or a global descent.
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

/-! ### PRIM-L060T/U: terminal seat image and direct reconstruction -/

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

/-! ### PRIM-L060V.2: terminal seat support and candidate surface -/

/-- A seat in the terminal image has exactly three active support primes. -/
theorem paritySafeTerminalFarProductSeat_activeSupport_card_eq_three
    {n r : ℕ}
    (hr : r ∈ paritySafeTerminalFarProductSeats n) :
    (paritySafeActiveSupport n r).card = 3 := by
  rcases mem_paritySafeTerminalFarProductSeats.mp hr with ⟨key, hkey, hseat⟩
  rcases key with ⟨p, q, s⟩
  have hcard :=
    paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three hkey
  rw [hseat] at hcard
  exact hcard

/-- Every terminal seat lies in the common odd coprime candidate surface. -/
theorem paritySafeTerminalFarProductSeats_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  intro r hr
  rcases mem_paritySafeTerminalFarProductSeats.mp hr with ⟨key, hkey, hseat⟩
  rcases key with ⟨p, q, s⟩
  have hfar := paritySafeTerminalSurvivingFarProductKey_residual_seat hkey
  have hcandidate := (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hfar).1
  rw [hseat] at hcandidate
  exact (mem_paritySafeCoveredCandidates.mp
    (Finset.mem_product.mp (Finset.mem_filter.mp hcandidate).1).1).1

/-! ### PRIM-L060U: direct same-seat reconstruction -/

/-- Equal terminal seats force equality of the three ordered key components.

This uses only the exact three-element support and the ordering packet from
L060S; in particular, it does not unfold a next-seat formula or use a
cofactor API. -/
theorem paritySafeTerminalKeys_components_eq_of_nextSeat_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁, (q₁, s₁)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (h₂ : (p₂, (q₂, s₂)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (hseat :
      paritySafeFarProductWaveNextSeat n (p₁, (q₁, s₁)) =
        paritySafeFarProductWaveNextSeat n (p₂, (q₂, s₂))) :
    p₁ = p₂ ∧ q₁ = q₂ ∧ s₁ = s₂ := by
  have hpacket₁ :=
    paritySafeTerminalSurvivingFarProductKey_prime_packet h₁
  have hpacket₂ :=
    paritySafeTerminalSurvivingFarProductKey_prime_packet h₂
  rcases hpacket₁ with ⟨hp₁, hq₁, hs₁, hp₁q₁, hq₁s₁, hcanon₁⟩
  rcases hpacket₂ with ⟨hp₂, hq₂, hs₂, hp₂q₂, hq₂s₂, hcanon₂⟩
  have hp_eq : p₁ = p₂ := by
    have hcanon_eq := congrArg (paritySafeCanonicalSupportPrime n) hseat
    exact hcanon₁.trans (hcanon_eq.trans hcanon₂.symm)
  have hthree₂ :=
    paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport h₂
  have hq₂support : q₂ ∈ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p₁, (q₁, s₁))) := by
    rw [hseat]
    exact hthree₂.2.1
  have hs₂support : s₂ ∈ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p₁, (q₁, s₁))) := by
    rw [hseat]
    exact hthree₂.2.2
  have hq₂cases :=
    paritySafeTerminalSurvivingFarProductKey_activeSupport_cases h₁ hq₂support
  have hs₂cases :=
    paritySafeTerminalSurvivingFarProductKey_activeSupport_cases h₁ hs₂support
  rcases hq₂cases with hq₂p | hq₂q | hq₂s <;>
    rcases hs₂cases with hs₂p | hs₂q | hs₂s <;>
    omega

/-- Equal next seats determine equality of surviving terminal keys by the
explicit scalar reconstruction theorem. -/
theorem paritySafeTerminalKeys_eq_of_nextSeat_eq
    {n : ℕ}
    {key₁ key₂ : ℕ × (ℕ × ℕ)}
    (h₁ : key₁ ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (h₂ : key₂ ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (hseat : paritySafeFarProductWaveNextSeat n key₁ =
      paritySafeFarProductWaveNextSeat n key₂) :
    key₁ = key₂ := by
  rcases key₁ with ⟨p₁, q₁, s₁⟩
  rcases key₂ with ⟨p₂, q₂, s₂⟩
  obtain ⟨hp, hq, hs⟩ :=
    paritySafeTerminalKeys_components_eq_of_nextSeat_eq h₁ h₂ hseat
  subst p₂
  subst q₂
  subst s₂
  rfl

/-- The terminal next-seat map is injective on surviving terminal keys. -/
theorem paritySafeTerminalFarProductWaveNextSeat_injectiveOn
    {n : ℕ} :
    Set.InjOn
      (paritySafeFarProductWaveNextSeat n)
      (paritySafeTerminalSurvivingFarProductKeys n : Set (ℕ × (ℕ × ℕ))) := by
  intro key₁ h₁ key₂ h₂ hseat
  exact paritySafeTerminalKeys_eq_of_nextSeat_eq h₁ h₂ hseat

/-- The terminal seat image has the same cardinality as its key domain. -/
theorem paritySafeTerminalFarProductSeats_card_eq_terminalKeys
    (n : ℕ) :
    (paritySafeTerminalFarProductSeats n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card := by
  unfold paritySafeTerminalFarProductSeats
  exact Finset.card_image_iff.mpr
    (paritySafeTerminalFarProductWaveNextSeat_injectiveOn (n := n))

/-! ### PRIM-L060V.3--V.8: disjoint weighted support-cost ledger -/

/-- Terminal and exact-depth collision seats are disjoint by support size. -/
theorem paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
    (n : ℕ) :
    Disjoint
      (paritySafeTerminalFarProductSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  rw [Finset.disjoint_left]
  intro r hterminal hcollision
  have hterminalCard :=
    paritySafeTerminalFarProductSeat_activeSupport_card_eq_three hterminal
  have hcollisionCard :=
    paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hcollision
  omega

/-- The exact terminal support cost is two per terminal seat. -/
theorem paritySafeTerminalFarProductSeats_supportCost_sum_eq
    (n : ℕ) :
    (∑ r ∈ paritySafeTerminalFarProductSeats n,
      ((paritySafeActiveSupport n r).card - 1)) =
      2 * (paritySafeTerminalFarProductSeats n).card := by
  calc
    (∑ r ∈ paritySafeTerminalFarProductSeats n,
        ((paritySafeActiveSupport n r).card - 1)) =
        ∑ _r ∈ paritySafeTerminalFarProductSeats n, 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [paritySafeTerminalFarProductSeat_activeSupport_card_eq_three hr]
    _ = 2 * (paritySafeTerminalFarProductSeats n).card := by
      simp [Nat.mul_comm]

/-- A collision seat contributes at least three units of local support cost. -/
theorem three_mul_depthFiberCollisionSeats_card_le_localSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
      ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
  have hterm : ∀ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
      3 ≤ (paritySafeActiveSupport n r).card - 1 := by
    intro r hr
    have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
    omega
  calc
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card =
        ∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 3 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr

/-- The terminal and collision seat union remains inside the candidate set. -/
theorem paritySafeTerminalCollisionSeats_union_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ∪
      paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
        squareAnchorOddPointCoprimeOffsets n := by
  intro r hr
  rcases Finset.mem_union.mp hr with hterminal | hcollision
  · exact paritySafeTerminalFarProductSeats_subset_candidate n hterminal
  · exact paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate n hcollision

/-- The terminal and collision charges fit in one disjoint candidate-side
support-excess sum.

The proof deliberately uses the union sum, so the same support excess is not
charged independently to the two seat families. -/
theorem two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  have hdisjoint :=
    paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats n
  have hsubset := paritySafeTerminalCollisionSeats_union_subset_candidate n
  have hcollision := three_mul_depthFiberCollisionSeats_card_le_localSupportCost n
  have hunion_le :
      (∑ r ∈ paritySafeTerminalFarProductSeats n ∪
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1)) ≤
        ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ((paritySafeActiveSupport n r).card - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro r _ _
    exact Nat.zero_le _
  calc
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card =
        2 * (paritySafeTerminalFarProductSeats n).card +
          3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
      rw [paritySafeTerminalFarProductSeats_card_eq_terminalKeys]
    _ = (∑ r ∈ paritySafeTerminalFarProductSeats n,
          ((paritySafeActiveSupport n r).card - 1)) +
          3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
      rw [paritySafeTerminalFarProductSeats_supportCost_sum_eq]
    _ ≤ (∑ r ∈ paritySafeTerminalFarProductSeats n,
          ((paritySafeActiveSupport n r).card - 1)) +
          ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
            ((paritySafeActiveSupport n r).card - 1) := by
      exact Nat.add_le_add_left hcollision _
    _ = ∑ r ∈ paritySafeTerminalFarProductSeats n ∪
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
      rw [Finset.sum_union hdisjoint]
    _ ≤ ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ((paritySafeActiveSupport n r).card - 1) := hunion_le
    _ = paritySafeSupportExcess n := by
      rfl

end
end DkMath.NumberTheory.Legendre
