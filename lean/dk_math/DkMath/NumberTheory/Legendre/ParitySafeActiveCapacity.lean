/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ActivePrimeCapacity

#print "file: DkMath.NumberTheory.Legendre.ParitySafeActiveCapacity"

/-!
## ParitySafeActiveCapacity

This module isolates the parity-safe active world.  A seat is retained only
when it is anchor-coprime and its complete point is odd; the usable old-prime
world is consequently `squareAnchorNondivisorPrimes n` with the prime `2`
removed.  The resulting support-disjoint family has a sharp finite capacity
bound and, unlike the unrestricted odd-anchor family, has no fresh collision.

The module stops at this finite candidate/capacity frontier.  It does not
provide a universal provider for the candidate surplus and therefore does not
prove Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L034.1: parity-safe candidate and active worlds -/

/-- Coprime square offsets whose complete points are odd. -/
noncomputable def squareAnchorOddPointCoprimeOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter (fun r => Odd (n ^ 2 + r))

@[simp] theorem mem_squareAnchorOddPointCoprimeOffsets
    {n r : ℕ} :
    r ∈ squareAnchorOddPointCoprimeOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧ Odd (n ^ 2 + r) := by
  simp [squareAnchorOddPointCoprimeOffsets]

/-- An odd-point candidate is still a square offset. -/
theorem squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    {n r : ℕ} (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    SquareOffset n r :=
  (mem_squareAnchorCoprimeOffsets.mp
    (mem_squareAnchorOddPointCoprimeOffsets.mp hr).1).1

/-- An odd-point candidate is coprime to its anchor. -/
theorem coprime_of_mem_squareAnchorOddPointCoprimeOffsets
    {n r : ℕ} (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    Nat.Coprime n r :=
  (mem_squareAnchorCoprimeOffsets.mp
    (mem_squareAnchorOddPointCoprimeOffsets.mp hr).1).2

/-- The parity-safe active old-prime world, with prime `2` removed. -/
noncomputable def squareAnchorOddActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorNondivisorPrimes n).erase 2

@[simp] theorem mem_squareAnchorOddActivePrimes
    {n q : ℕ} :
    q ∈ squareAnchorOddActivePrimes n ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ≠ 2 := by
  classical
  simp [squareAnchorOddActivePrimes, and_assoc, and_left_comm, and_comm]

/-! ### PRIM-L034.2: odd points remove the prime-two collision -/

/-- An odd complete point has no prime-two support. -/
theorem not_mem_squareOffsetPrimeSupport_of_odd_point
    {n r : ℕ} (hodd : Odd (n ^ 2 + r)) :
    2 ∉ squareOffsetPrimeSupport n r := by
  intro h2
  have h2' := mem_squareOffsetPrimeSupport.mp h2
  have heven : Even (n ^ 2 + r) := even_iff_two_dvd.mpr h2'.2.2
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- The same prime-two exclusion holds for the active nondivisor support. -/
theorem not_mem_squareOffsetAnchorNondivisorSupport_of_odd_point
    {n r : ℕ} (hodd : Odd (n ^ 2 + r)) :
    2 ∉ squareOffsetAnchorNondivisorSupport n r := by
  intro h2
  have h2' := mem_squareOffsetAnchorNondivisorSupport.mp h2
  have heven : Even (n ^ 2 + r) := even_iff_two_dvd.mpr h2'.2.2.2
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-! ### PRIM-L034.3: parity-safe family and collision elimination -/

/-- Odd-point seats with pairwise disjoint active nondivisor supports. -/
def PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, r ∈ squareAnchorOddPointCoprimeOffsets n) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetAnchorNondivisorSupport n r)

private theorem pairwiseActive_of_pairwiseParitySafe
    {n : ℕ} {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R) :
    PairwiseActiveOldSupportDisjointSquareSeatFamily n R := by
  constructor
  · intro r hr
    exact (mem_squareAnchorOddPointCoprimeOffsets.mp (hsafe.1 r hr)).1
  · exact hsafe.2

/-- The parity-safe family satisfies the old-support family interface. -/
theorem pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R) :
    PairwiseOldSupportDisjointSquareSeatFamily n R :=
  pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseActiveOldSupportDisjointSquareSeatFamily
    hn (pairwiseActive_of_pairwiseParitySafe hsafe)

/-- No fresh collision remains inside a parity-safe active family. -/
theorem pairwiseCoprimeSquareSeatFamily_of_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R) :
    PairwiseCoprimeSquareSeatFamily n R := by
  classical
  refine ⟨fun r hr => squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (hsafe.1 r hr), ?_⟩
  intro r hr s hs hrs
  have hmemr := mem_squareAnchorOddPointCoprimeOffsets.mp (hsafe.1 r hr)
  have hmems := mem_squareAnchorOddPointCoprimeOffsets.mp (hsafe.1 s hs)
  have hn : 0 < n := by
    have hpoint := (mem_squareAnchorCoprimeOffsets.mp hmemr.1).1
    dsimp [SquareOffset] at hpoint
    exact by omega
  have hOld := pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    hn hsafe
  by_contra hncop
  rcases lt_or_gt_of_ne hrs with hrs' | hsr'
  · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
      hOld hr hs hrs' hncop
    rcases freshCollision_primeTwo_owner hcollision with howner | howner
    · exact (not_mem_squareOffsetPrimeSupport_of_odd_point hmemr.2) howner.1
    · exact (not_mem_squareOffsetPrimeSupport_of_odd_point hmems.2) howner.2
  · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
      hOld hs hr hsr' (by
        intro hcop
        exact hncop hcop.symm)
    rcases freshCollision_primeTwo_owner hcollision with howner | howner
    · exact (not_mem_squareOffsetPrimeSupport_of_odd_point hmems.2) howner.1
    · exact (not_mem_squareOffsetPrimeSupport_of_odd_point hmemr.2) howner.2

/-! ### PRIM-L034.4: parity-safe active capacity -/

/-- Full cover bounds a parity-safe family by the odd active prime world. -/
theorem card_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily_le_oddActivePrimes_of_fullyCovered
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R)
    (hfull : SquareOffsetsFullyCovered n) :
    R.card ≤ (squareAnchorOddActivePrimes n).card := by
  classical
  have hnonempty : ∀ r ∈ R,
      (squareOffsetAnchorNondivisorSupport n r).Nonempty := by
    intro r hr
    have hmem := mem_squareAnchorOddPointCoprimeOffsets.mp (hsafe.1 r hr)
    have hcovered := hfull r (mem_squareAnchorCoprimeOffsets.mp hmem.1).1
    have hsupport := squareOffsetCovered_iff_primeSupport_nonempty.mp hcovered
    rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn
      (mem_squareAnchorCoprimeOffsets.mp hmem.1).2]
    exact hsupport
  have hunion :
      R.biUnion (fun r => squareOffsetAnchorNondivisorSupport n r) ⊆
        squareAnchorOddActivePrimes n := by
    intro q hq
    simp only [Finset.mem_biUnion] at hq
    rcases hq with ⟨r, hr, hqr⟩
    have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hqr
    have hodd := (mem_squareAnchorOddPointCoprimeOffsets.mp (hsafe.1 r hr)).2
    have hqne : q ≠ 2 := by
      intro hqeq
      subst q
      exact not_mem_squareOffsetAnchorNondivisorSupport_of_odd_point hodd hqr
    exact mem_squareAnchorOddActivePrimes.mpr ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqne⟩
  calc
    R.card = ∑ r ∈ R, 1 := by simp
    _ ≤ ∑ r ∈ R, (squareOffsetAnchorNondivisorSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.card_pos.mpr (hnonempty r hr)
    _ = (R.biUnion (fun r => squareOffsetAnchorNondivisorSupport n r)).card := by
      symm
      exact Finset.card_biUnion hsafe.2
    _ ≤ (squareAnchorOddActivePrimes n).card := Finset.card_le_card hunion

/-- Active-capacity excess excludes full cover for the parity-safe family. -/
theorem not_fullyCovered_of_oddActivePrimes_card_lt_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R)
    (hcard : (squareAnchorOddActivePrimes n).card < R.card) :
    ¬ SquareOffsetsFullyCovered n := by
  intro hfull
  exact (not_le_of_gt hcard)
    (card_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily_le_oddActivePrimes_of_fullyCovered
      hn hsafe hfull)

/-- Capacity excess exposes a prime in the square cell. -/
theorem exists_prime_squareCell_of_oddActivePrimes_card_lt_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hsafe : PairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily n R)
    (hcard : (squareAnchorOddActivePrimes n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hnotfull :=
    not_fullyCovered_of_oddActivePrimes_card_lt_pairwiseParitySafeActiveOldSupportDisjointSquareSeatFamily
      hn hsafe hcard
  obtain ⟨r, hr⟩ := not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp hnotfull
  have hescape := mem_escapingSquareOffsets.mp hr
  have hdisj :
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) :=
    supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hescape.2
  refine ⟨n ^ 2 + r,
    prime_of_squareAnchoredSupportEscape hn hescape.1 hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
    ⟨r, hescape.1, rfl⟩

/-! ### PRIM-L034.5: comparison with the totient world -/

/-- On an even anchor every coprime seat has an odd complete point. -/
theorem squareAnchorOddPointCoprimeOffsets_eq_coprimeOffsets_of_even_anchor
    {n : ℕ} (heven : Even n) :
    squareAnchorOddPointCoprimeOffsets n = squareAnchorCoprimeOffsets n := by
  ext r
  constructor
  · intro hr
    exact (mem_squareAnchorOddPointCoprimeOffsets.mp hr).1
  · intro hr
    have hcop := mem_squareAnchorCoprimeOffsets.mp hr
    have h2n : 2 ∣ n := even_iff_two_dvd.mp heven
    have hnot2r : ¬ 2 ∣ r := by
      intro h2r
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨2, Nat.prime_two, h2n, h2r⟩) hcop.2
    have hrodd : Odd r := by
      apply Nat.not_even_iff_odd.mp
      intro hev
      exact hnot2r (even_iff_two_dvd.mp hev)
    have hsq : Even (n ^ 2) :=
      even_iff_two_dvd.mpr (dvd_pow h2n (by decide))
    exact mem_squareAnchorOddPointCoprimeOffsets.mpr ⟨hr, hsq.add_odd hrodd⟩

/-- The even-anchor candidate world has the full `2 * totient` cardinality. -/
theorem card_squareAnchorOddPointCoprimeOffsets_of_even_anchor
    {n : ℕ} (hn : 0 < n) (heven : Even n) :
    (squareAnchorOddPointCoprimeOffsets n).card = 2 * Nat.totient n := by
  rw [squareAnchorOddPointCoprimeOffsets_eq_coprimeOffsets_of_even_anchor heven]
  exact card_squareAnchorCoprimeOffsets hn

/-- Every active nondivisor prime is a coprime base offset. -/
theorem squareAnchorNondivisorPrimes_subset_squareAnchorCoprimeBaseOffsets
    (n : ℕ) :
    squareAnchorNondivisorPrimes n ⊆ squareAnchorCoprimeBaseOffsets n := by
  intro q hq
  have hq' := mem_squareAnchorNondivisorPrimes.mp hq
  apply mem_squareAnchorCoprimeBaseOffsets.mpr
  refine ⟨hq'.1.one_le, hq'.2.1, ?_⟩
  exact (hq'.1.coprime_iff_not_dvd.mpr hq'.2.2).symm

/-- The nondivisor world is strictly smaller than the totient world for `1<n`. -/
theorem squareAnchorNondivisorPrimes_card_lt_totient_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    (squareAnchorNondivisorPrimes n).card < Nat.totient n := by
  have hsub := squareAnchorNondivisorPrimes_subset_squareAnchorCoprimeBaseOffsets n
  have honeBase : 1 ∈ squareAnchorCoprimeBaseOffsets n := by
    apply mem_squareAnchorCoprimeBaseOffsets.mpr
    exact ⟨by norm_num, by omega, Nat.coprime_one_right n⟩
  have honeNondiv : 1 ∉ squareAnchorNondivisorPrimes n := by
    simp
  have hne : squareAnchorNondivisorPrimes n ≠ squareAnchorCoprimeBaseOffsets n := by
    intro heq
    exact honeNondiv (heq ▸ honeBase)
  have hcard := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩)
  rw [card_squareAnchorCoprimeBaseOffsets (by omega : 0 < n)] at hcard
  exact hcard

/-- Removing prime `2` preserves the strict totient upper bound. -/
theorem squareAnchorOddActivePrimes_card_lt_totient_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    (squareAnchorOddActivePrimes n).card < Nat.totient n := by
  exact lt_of_le_of_lt
    (Finset.card_le_card (Finset.erase_subset 2 (squareAnchorNondivisorPrimes n)))
    (squareAnchorNondivisorPrimes_card_lt_totient_of_one_lt hn)

/-! ### PRIM-L034.6: candidate surplus and the false odd beam -/

private theorem odd_of_prime_ne_two {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2) : Odd q := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  have h2q : 2 ∣ q := even_iff_two_dvd.mp heven
  have hqe : 2 = q := ((Nat.dvd_prime hq).mp h2q).resolve_left (by norm_num)
  exact hq2 hqe.symm

private theorem odd_point_of_even_anchor_active_prime
    {n q : ℕ} (heven : Even n) (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    Odd (n ^ 2 + q) := by
  have h2n : 2 ∣ n := even_iff_two_dvd.mp heven
  have hsq : Even (n ^ 2) :=
    even_iff_two_dvd.mpr (dvd_pow h2n (by decide))
  exact hsq.add_odd (odd_of_prime_ne_two hq hq2)

private theorem odd_point_of_odd_anchor_shift_active_prime
    {n q : ℕ} (hnodd : Odd n) (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    Odd (n ^ 2 + (n + q)) := by
  have hsum : Even (n ^ 2 + n) := hnodd.pow.add_odd hnodd
  have heq : n ^ 2 + (n + q) = (n ^ 2 + n) + q := by omega
  rw [heq]
  exact hsum.add_odd (odd_of_prime_ne_two hq hq2)

private noncomputable def paritySafePacketChoice (n r : ℕ) : ℕ :=
  if Odd (n ^ 2 + r) then r else n + r

private theorem paritySafePacketChoice_mem_of_odd_anchor
    {n r : ℕ} (hnodd : Odd n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    paritySafePacketChoice n r ∈ squareAnchorOddPointCoprimeOffsets n := by
  by_cases hodd : Odd (n ^ 2 + r)
  · rw [paritySafePacketChoice, if_pos hodd]
    exact mem_squareAnchorOddPointCoprimeOffsets.mpr
      ⟨mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets hr, hodd⟩
  · have heven : Even (n ^ 2 + r) := Nat.not_odd_iff_even.mp hodd
    have hshiftodd : Odd (n ^ 2 + (n + r)) := by
      have hsum : Odd ((n ^ 2 + r) + n) := heven.add_odd hnodd
      have heq : n ^ 2 + (n + r) = (n ^ 2 + r) + n := by omega
      rw [heq]
      exact hsum
    rw [paritySafePacketChoice, if_neg hodd]
    exact mem_squareAnchorOddPointCoprimeOffsets.mpr
      ⟨mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hr, hshiftodd⟩

private theorem paritySafePacketChoice_injective_of_odd_anchor
    {n : ℕ} (_hnodd : Odd n) :
    Set.InjOn (paritySafePacketChoice n)
      (squareAnchorCoprimeBaseOffsets n : Set ℕ) := by
  intro a ha b hb hab
  have ha' := mem_squareAnchorCoprimeBaseOffsets.mp ha
  have hb' := mem_squareAnchorCoprimeBaseOffsets.mp hb
  by_cases hpa : Odd (n ^ 2 + a)
  · by_cases hpb : Odd (n ^ 2 + b)
    · simpa [paritySafePacketChoice, hpa, hpb] using hab
    · have hab' : a = n + b := by
        simpa [paritySafePacketChoice, hpa, hpb] using hab
      omega
  · by_cases hpb : Odd (n ^ 2 + b)
    · have hab' : n + a = b := by
        simpa [paritySafePacketChoice, hpa, hpb] using hab
      omega
    · have hab' : n + a = n + b := by
        simpa [paritySafePacketChoice, hpa, hpb] using hab
      exact Nat.add_left_cancel hab'

/-- For an odd anchor, the packet choice supplies at least one candidate per
coprime base seat, hence the candidate cardinal is at least `totient n`. -/
theorem totient_le_squareAnchorOddPointCoprimeOffsets_card_of_odd_anchor
    {n : ℕ} (hn : 0 < n) (hnodd : Odd n) :
    Nat.totient n ≤ (squareAnchorOddPointCoprimeOffsets n).card := by
  classical
  let g := paritySafePacketChoice n
  have hsub :
      (squareAnchorCoprimeBaseOffsets n).image g ⊆
        squareAnchorOddPointCoprimeOffsets n := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨s, hs, rfl⟩
    exact paritySafePacketChoice_mem_of_odd_anchor hnodd hs
  have hcard :
      ((squareAnchorCoprimeBaseOffsets n).image g).card =
        (squareAnchorCoprimeBaseOffsets n).card := by
    apply Finset.card_image_iff.mpr
    exact paritySafePacketChoice_injective_of_odd_anchor hnodd
  calc
    Nat.totient n = (squareAnchorCoprimeBaseOffsets n).card :=
      (card_squareAnchorCoprimeBaseOffsets hn).symm
    _ = ((squareAnchorCoprimeBaseOffsets n).image g).card := hcard.symm
    _ ≤ (squareAnchorOddPointCoprimeOffsets n).card := Finset.card_le_card hsub

/-- For `1<n`, the parity-safe candidate world strictly exceeds the active world.

This is the finite surplus needed by the capacity consumer.  The theorem is
proved directly by an injective packet choice; it does not assert the exact
candidate cardinal `Nat.totient n` or a provider for a full cover.
-/
theorem squareAnchorOddActivePrimes_card_lt_squareAnchorOddPointCoprimeOffsets_card_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    (squareAnchorOddActivePrimes n).card <
      (squareAnchorOddPointCoprimeOffsets n).card := by
  classical
  by_cases heven : Even n
  · have hsub : squareAnchorOddActivePrimes n ⊆
        squareAnchorOddPointCoprimeOffsets n := by
      intro q hq
      have hq' := mem_squareAnchorOddActivePrimes.mp hq
      have hbase : q ∈ squareAnchorCoprimeBaseOffsets n := by
        apply mem_squareAnchorCoprimeBaseOffsets.mpr
        refine ⟨hq'.1.one_le, hq'.2.1, ?_⟩
        exact (hq'.1.coprime_iff_not_dvd.mpr hq'.2.2.1).symm
      apply mem_squareAnchorOddPointCoprimeOffsets.mpr
      exact ⟨mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets hbase,
        odd_point_of_even_anchor_active_prime heven hq'.1 hq'.2.2.2⟩
    have hone : 1 ∈ squareAnchorOddPointCoprimeOffsets n := by
      apply mem_squareAnchorOddPointCoprimeOffsets.mpr
      have hseat : SquareOffset n 1 := by
        dsimp [SquareOffset]
        omega
      refine ⟨mem_squareAnchorCoprimeOffsets.mpr ⟨hseat, ?_⟩, ?_⟩
      · exact Nat.coprime_one_right n
      · have h2n : 2 ∣ n := even_iff_two_dvd.mp heven
        have hsq : Even (n ^ 2) :=
          even_iff_two_dvd.mpr (dvd_pow h2n (by decide))
        exact hsq.add_odd (by norm_num : Odd (1 : ℕ))
    have hone' : 1 ∉ squareAnchorOddActivePrimes n := by simp
    have hstrict := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro heq
      exact hone' (heq ▸ hone)
      ⟩
    exact Finset.card_lt_card hstrict
  · have hnodd : Odd n := Nat.not_even_iff_odd.mp heven
    let f : ℕ → ℕ := fun q => n + q
    have hinj : Function.Injective f := by
      intro a b hab
      dsimp [f] at hab
      exact Nat.add_left_cancel hab
    have himage : (squareAnchorOddActivePrimes n).image f ⊆
        squareAnchorOddPointCoprimeOffsets n := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
      have hq' := mem_squareAnchorOddActivePrimes.mp hq
      have hbase : q ∈ squareAnchorCoprimeBaseOffsets n := by
        apply mem_squareAnchorCoprimeBaseOffsets.mpr
        refine ⟨hq'.1.one_le, hq'.2.1, ?_⟩
        exact (hq'.1.coprime_iff_not_dvd.mpr hq'.2.2.1).symm
      apply mem_squareAnchorOddPointCoprimeOffsets.mpr
      exact ⟨mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hbase,
        odd_point_of_odd_anchor_shift_active_prime hnodd hq'.1 hq'.2.2.2⟩
    have htwo : 2 ∈ squareAnchorOddPointCoprimeOffsets n := by
      apply mem_squareAnchorOddPointCoprimeOffsets.mpr
      refine ⟨mem_squareAnchorCoprimeOffsets.mpr ⟨by norm_num [SquareOffset] at hn ⊢; omega,
        Nat.coprime_two_right.mpr hnodd⟩, ?_⟩
      exact hnodd.pow.add_even (even_iff_two_dvd.mpr ⟨1, by omega⟩)
    have htwo' : 2 ∉ (squareAnchorOddActivePrimes n).image f := by
      intro hx
      rcases Finset.mem_image.mp hx with ⟨q, hq, hqeq⟩
      have hq' := mem_squareAnchorOddActivePrimes.mp hq
      dsimp [f] at hqeq
      have hqge : 3 ≤ q := by
        have hqle : 2 ≤ q := hq'.1.two_le
        omega
      omega
    have hstrict := Finset.ssubset_iff_subset_ne.mpr ⟨himage, by
      intro heq
      exact htwo' (heq ▸ htwo)
      ⟩
    have hcardImage :
        ((squareAnchorOddActivePrimes n).image f).card =
          (squareAnchorOddActivePrimes n).card :=
      Finset.card_image_iff.mpr hinj.injOn
    calc
      (squareAnchorOddActivePrimes n).card =
          ((squareAnchorOddActivePrimes n).image f).card := hcardImage.symm
      _ < (squareAnchorOddPointCoprimeOffsets n).card :=
        Finset.card_lt_card hstrict

/-- The odd-anchor example `n=5`, offsets `2` and `8`, is a false beam:
both seats are odd-point candidates but share the active old prime `3`. -/
theorem odd_anchor_five_false_beam :
    2 ∈ squareAnchorOddPointCoprimeOffsets 5 ∧
      8 ∈ squareAnchorOddPointCoprimeOffsets 5 ∧
      3 ∈ squareOffsetAnchorNondivisorSupport 5 2 ∧
      3 ∈ squareOffsetAnchorNondivisorSupport 5 8 ∧
      ¬ Disjoint (squareOffsetAnchorNondivisorSupport 5 2)
        (squareOffsetAnchorNondivisorSupport 5 8) := by
  have h2 : 2 ∈ squareAnchorOddPointCoprimeOffsets 5 := by
    norm_num [squareAnchorOddPointCoprimeOffsets, squareAnchorCoprimeOffsets,
      squareOffsets, SquareOffset, Nat.Coprime, Odd]
  have h8 : 8 ∈ squareAnchorOddPointCoprimeOffsets 5 := by
    norm_num [squareAnchorOddPointCoprimeOffsets, squareAnchorCoprimeOffsets,
      squareOffsets, SquareOffset, Nat.Coprime, Odd]
  have h32 : 3 ∈ squareOffsetAnchorNondivisorSupport 5 2 := by
    apply mem_squareOffsetAnchorNondivisorSupport.mpr
    norm_num [SquareOffsetForbiddenBy]
  have h38 : 3 ∈ squareOffsetAnchorNondivisorSupport 5 8 := by
    apply mem_squareOffsetAnchorNondivisorSupport.mpr
    norm_num [SquareOffsetForbiddenBy]
  exact ⟨h2, h8, h32, h38, by
    intro hdisj
    exact (Finset.disjoint_left.mp hdisj) h32 h38⟩

end DkMath.NumberTheory.Legendre
