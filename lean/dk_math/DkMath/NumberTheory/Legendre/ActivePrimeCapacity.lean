/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreshCollisionRepair
import DkMath.NumberTheory.Legendre.CoprimePacket

#print "file: DkMath.NumberTheory.Legendre.ActivePrimeCapacity"

/-!
## ActivePrimeCapacity

Anchor-coprime seats cannot be covered by prime directions dividing the
anchor.  This module therefore counts only the exact active finite world
`squareAnchorNondivisorPrimes n`.  It also composes the L032 prime-`2`
ownership theorem with even-anchor localization: on an even anchor an active
old-support-disjoint family is already complete-point pairwise coprime.

The threshold is a strict finite improvement over the full old-prime world
for `1 < n`.  The odd-anchor witness at `n = 13` records why the parity
elimination cannot be generalized.  No universal provider or proof of
Legendre's conjecture is asserted here.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L033.1: active family interface -/

/-- Anchor-coprime seats with pairwise disjoint active old-prime supports. -/
def PairwiseActiveOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, r ∈ squareAnchorCoprimeOffsets n) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetAnchorNondivisorSupport n r)

/-- Active support separation implies the L029 old-support family interface. -/
theorem pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R) :
    PairwiseOldSupportDisjointSquareSeatFamily n R := by
  constructor
  · intro r hr
    exact (mem_squareAnchorCoprimeOffsets.mp (hactive.1 r hr)).1
  · intro r hr s hs hrs
    have hcr := (mem_squareAnchorCoprimeOffsets.mp (hactive.1 r hr)).2
    have hcs := (mem_squareAnchorCoprimeOffsets.mp (hactive.1 s hs)).2
    have hdisj := hactive.2 hr hs hrs
    change Disjoint (squareOffsetAnchorNondivisorSupport n r)
      (squareOffsetAnchorNondivisorSupport n s) at hdisj
    rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hcr,
      ← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hcs]
      at hdisj
    exact hdisj

/-- The L029 family interface returns to active support under coprime membership. -/
theorem pairwiseActiveOldSupportDisjointSquareSeatFamily_of_pairwiseOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hcop : ∀ r ∈ R, r ∈ squareAnchorCoprimeOffsets n)
    (hold : PairwiseOldSupportDisjointSquareSeatFamily n R) :
    PairwiseActiveOldSupportDisjointSquareSeatFamily n R := by
  constructor
  · exact hcop
  · intro r hr s hs hrs
    have hcr := (mem_squareAnchorCoprimeOffsets.mp (hcop r hr)).2
    have hcs := (mem_squareAnchorCoprimeOffsets.mp (hcop s hs)).2
    have hdisj := hold.2 hr hs hrs
    change Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s) at hdisj
    rw [squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hcr,
      squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hcs]
      at hdisj
    exact hdisj

/-! ### PRIM-L033.2: active-world capacity -/

/-- Full cover bounds an active old-support-disjoint family by the nondivisor world. -/
theorem card_pairwiseActiveOldSupportDisjointSquareSeatFamily_le_nondivisorPrimes_of_fullyCovered
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R)
    (hfull : SquareOffsetsFullyCovered n) :
    R.card ≤ (squareAnchorNondivisorPrimes n).card := by
  classical
  have hnonempty : ∀ r ∈ R,
      (squareOffsetAnchorNondivisorSupport n r).Nonempty := by
    intro r hr
    have hmem := mem_squareAnchorCoprimeOffsets.mp (hactive.1 r hr)
    have hcovered := hfull r hmem.1
    have hsupport := squareOffsetCovered_iff_primeSupport_nonempty.mp hcovered
    rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hmem.2]
    exact hsupport
  have hunion :
      R.biUnion (fun r => squareOffsetAnchorNondivisorSupport n r) ⊆
        squareAnchorNondivisorPrimes n := by
    intro q hq
    simp only [Finset.mem_biUnion] at hq
    rcases hq with ⟨r, hr, hqr⟩
    exact mem_squareAnchorNondivisorPrimes.mpr
      (mem_squareOffsetAnchorNondivisorSupport.mp hqr |>.imp_right
        (by omega))
  calc
    R.card = ∑ r ∈ R, 1 := by simp
    _ ≤ ∑ r ∈ R, (squareOffsetAnchorNondivisorSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.card_pos.mpr (hnonempty r hr)
    _ = (R.biUnion (fun r => squareOffsetAnchorNondivisorSupport n r)).card := by
      symm
      exact Finset.card_biUnion hactive.2
    _ ≤ (squareAnchorNondivisorPrimes n).card := Finset.card_le_card hunion

/-- Active-world capacity excess prevents full cover. -/
theorem not_fullyCovered_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R)
    (hcard : (squareAnchorNondivisorPrimes n).card < R.card) :
    ¬ SquareOffsetsFullyCovered n := by
  intro hfull
  exact (not_le_of_gt hcard)
    (card_pairwiseActiveOldSupportDisjointSquareSeatFamily_le_nondivisorPrimes_of_fullyCovered
      hn hactive hfull)

/-- Active-world capacity excess produces a prime in the square cell. -/
theorem exists_prime_squareCell_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R)
    (hcard : (squareAnchorNondivisorPrimes n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hnotfull :=
    not_fullyCovered_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily
      hn hactive hcard
  obtain ⟨r, hr⟩ :=
    not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp hnotfull
  have hescape := mem_escapingSquareOffsets.mp hr
  have hdisj :
      SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) :=
    supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr
      hescape.2
  refine ⟨n ^ 2 + r,
    prime_of_squareAnchoredSupportEscape hn hescape.1 hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).mpr
    ⟨r, hescape.1, rfl⟩

/-! ### PRIM-L033.3: the active world is strictly smaller -/

/-- The divisor and nondivisor worlds have the exact old-world cardinal sum. -/
theorem card_squareAnchorDivisorPrimes_add_nondivisorPrimes
    (n : ℕ) :
    (squareAnchorDivisorPrimes n).card +
        (squareAnchorNondivisorPrimes n).card =
      (primeScalesUpTo n).card := by
  calc
    (squareAnchorDivisorPrimes n).card +
        (squareAnchorNondivisorPrimes n).card =
        (squareAnchorDivisorPrimes n ∪
          squareAnchorNondivisorPrimes n).card := by
      symm
      exact Finset.card_union_of_disjoint
        (disjoint_squareAnchorDivisorPrimes_squareAnchorNondivisorPrimes n)
    _ = (primeScalesUpTo n).card := by
      rw [squareAnchorDivisorPrimes_union_nondivisorPrimes]

/-- For `1<n`, at least one old prime divides the anchor. -/
theorem squareAnchorDivisorPrimes_nonempty_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    (squareAnchorDivisorPrimes n).Nonempty := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hpLe : p ≤ n := Nat.le_of_dvd (by omega) hpd
  exact ⟨p, mem_squareAnchorDivisorPrimes.mpr ⟨hp, hpLe, hpd⟩⟩

/-- The active threshold is strictly below the full old-prime threshold for `1<n`. -/
theorem squareAnchorNondivisorPrimes_card_lt_primeScalesUpTo_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    (squareAnchorNondivisorPrimes n).card < (primeScalesUpTo n).card := by
  have hpos : 0 < (squareAnchorDivisorPrimes n).card :=
    Finset.card_pos.mpr (squareAnchorDivisorPrimes_nonempty_of_one_lt hn)
  have hcard := card_squareAnchorDivisorPrimes_add_nondivisorPrimes n
  omega

/-! ### PRIM-L033.4: even-anchor fresh-collision elimination -/

private theorem not_mem_squareOffsetPrimeSupport_of_even_anchor_of_coprime
    {n r : ℕ} (hn : 0 < n) (heven : Even n) (hcop : Nat.Coprime n r) :
    2 ∉ squareOffsetPrimeSupport n r := by
  rw [squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime hn hcop]
  intro h2
  have h2' := mem_squareOffsetAnchorNondivisorSupport.mp h2
  rcases heven with ⟨a, ha⟩
  have h2n : 2 ∣ n := ⟨a, by omega⟩
  exact h2'.2.2.1 h2n

/-- On an even anchor, active support separation already implies point coprimality. -/
theorem pairwiseCoprimeSquareSeatFamily_of_even_pairwiseActiveOldSupportDisjointSquareSeatFamily
    {n : ℕ} {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R)
    (heven : Even n) :
    PairwiseCoprimeSquareSeatFamily n R := by
  classical
  refine ⟨fun r hr => (mem_squareAnchorCoprimeOffsets.mp (hactive.1 r hr)).1, ?_⟩
  intro r hr s hs hrs
  have hmemr := mem_squareAnchorCoprimeOffsets.mp (hactive.1 r hr)
  have hmems := mem_squareAnchorCoprimeOffsets.mp (hactive.1 s hs)
  have hn : 0 < n := by
    dsimp [SquareOffset] at hmemr
    omega
  have hOld :=
    pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseActiveOldSupportDisjointSquareSeatFamily
      hn hactive
  by_contra hncop
  rcases lt_or_gt_of_ne hrs with hrs' | hsr'
  · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
      hOld hr hs hrs' hncop
    rcases freshCollision_primeTwo_owner hcollision with howner | howner
    · exact (not_mem_squareOffsetPrimeSupport_of_even_anchor_of_coprime
        hn heven hmemr.2) howner.1
    · exact (not_mem_squareOffsetPrimeSupport_of_even_anchor_of_coprime
        hn heven hmems.2) howner.2
  · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
      hOld hs hr hsr' (by
        intro hcop
        exact hncop hcop.symm)
    rcases freshCollision_primeTwo_owner hcollision with howner | howner
    · exact (not_mem_squareOffsetPrimeSupport_of_even_anchor_of_coprime
        hn heven hmems.2) howner.1
    · exact (not_mem_squareOffsetPrimeSupport_of_even_anchor_of_coprime
        hn heven hmemr.2) howner.2

/-! ### PRIM-L033.5: even-anchor capacity consumer -/

/-- The localized active threshold gives a square-cell prime on even anchors. -/
theorem exists_prime_squareCell_of_even_pairwiseActiveOldSupportDisjointSquareSeatFamily_card_excess
    {n : ℕ} (hn : 0 < n) (heven : Even n) {R : Finset ℕ}
    (hactive : PairwiseActiveOldSupportDisjointSquareSeatFamily n R)
    (hcard : (squareAnchorNondivisorPrimes n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have _ := pairwiseCoprimeSquareSeatFamily_of_even_pairwiseActiveOldSupportDisjointSquareSeatFamily
    hactive heven
  exact exists_prime_squareCell_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily
    hn hactive hcard

/-! ### PRIM-L033.6: odd-anchor false beam -/

/-- The odd anchor `13` retains the fresh collision at offsets `1` and `18`. -/
theorem odd_anchor_thirteen_freshCollision_falseBeam :
    1 ∈ squareAnchorCoprimeOffsets 13 ∧
      18 ∈ squareAnchorCoprimeOffsets 13 ∧
      Disjoint (squareOffsetAnchorNondivisorSupport 13 1)
        (squareOffsetAnchorNondivisorSupport 13 18) ∧
      ¬ Nat.Coprime (13 ^ 2 + 1) (13 ^ 2 + 18) ∧
      Nat.gcd (13 ^ 2 + 1) (13 ^ 2 + 18) = 17 ∧
      Nat.Prime 17 ∧ 13 < 17 := by
  have hr : 1 ∈ squareAnchorCoprimeOffsets 13 := by
    norm_num [squareAnchorCoprimeOffsets, squareOffsets, Nat.Coprime]
  have hs : 18 ∈ squareAnchorCoprimeOffsets 13 := by
    norm_num [squareAnchorCoprimeOffsets, squareOffsets, Nat.Coprime]
  have hdisj :
      Disjoint (squareOffsetAnchorNondivisorSupport 13 1)
        (squareOffsetAnchorNondivisorSupport 13 18) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp18
    have hp1' := mem_squareOffsetAnchorNondivisorSupport.mp hp1
    have hp18' := mem_squareOffsetAnchorNondivisorSupport.mp hp18
    have hpgcd : p ∣ 17 := by
      have h := Nat.dvd_gcd hp1'.2.2.2 hp18'.2.2.2
      norm_num at h
      exact h
    have hp17 : Nat.Prime 17 := by norm_num
    have hpeq : p = 17 :=
      ((Nat.dvd_prime hp17).mp hpgcd).resolve_left hp1'.1.ne_one
    omega
  refine ⟨hr, hs, hdisj, ?_, ?_, by norm_num, by norm_num⟩
  · norm_num [Nat.Coprime]
  · norm_num

end DkMath.NumberTheory.Legendre
