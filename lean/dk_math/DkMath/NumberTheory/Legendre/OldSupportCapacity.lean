/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CoprimeSeatCapacity

#print "file: DkMath.NumberTheory.Legendre.OldSupportCapacity"

/-!
## OldSupportCapacity

The finite capacity argument needs pairwise disjointness of actual bounded
old-prime supports, not complete-point coprimality itself.  This module makes
that weaker interface explicit, proves the corresponding capacity/frontier
bridge, and characterizes support disjointness for ordered offsets by
divisibility of the offset gap.

The concrete `n = 3`, offsets `{1, 6}` witness records that a fresh common
prime can destroy complete-point coprimality without consuming a common old
prime direction.  No universal provider is asserted here.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L029.1: exact old-support family predicate -/

/--
A finite square-seat family whose actual bounded old-prime supports are
pairwise disjoint.  This is the exact input consumed by finite capacity
counting; complete-point coprimality is not part of the predicate.
-/
def PairwiseOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, SquareOffset n r) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetPrimeSupport n r)

/-! ### PRIM-L029.2: complete-coprime bridge -/

/-- Complete-point coprimality implies the weaker old-support family condition. -/
theorem pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R) :
    PairwiseOldSupportDisjointSquareSeatFamily n R := by
  exact ⟨hfamily.1,
    pairwiseDisjoint_squareOffsetPrimeSupport_of_family hfamily⟩

/-! ### PRIM-L029.3: strictness witness -/

/-- The two offsets `1` and `6` belong to the square shell anchored at `3`. -/
theorem squareOffset_oldSupportCapacity_strictness_left :
    SquareOffset 3 1 := by
  norm_num [SquareOffset]

/-- The two offsets `1` and `6` belong to the square shell anchored at `3`. -/
theorem squareOffset_oldSupportCapacity_strictness_right :
    SquareOffset 3 6 := by
  norm_num [SquareOffset]

/-- The corresponding complete points `10` and `15` are not coprime. -/
theorem not_coprime_oldSupportCapacity_strictness_points :
    ¬ Nat.Coprime 10 15 := by
  norm_num [Nat.Coprime]

/--
The actual old-prime supports of offsets `1` and `6` at anchor `3` are
disjoint, although the complete points share the fresh prime `5`.
-/
theorem disjoint_oldSupportCapacity_strictness_supports :
    Disjoint (squareOffsetPrimeSupport 3 1)
      (squareOffsetPrimeSupport 3 6) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq6
  have hq1' := mem_squareOffsetPrimeSupport.mp hq1
  have hq6' := mem_squareOffsetPrimeSupport.mp hq6
  have hqle : q ≤ 3 := hq1'.2.1
  have hqdiv : q ∣ 2 * 5 := by
    simpa using hq1'.2.2
  rcases (Nat.Prime.dvd_mul hq1'.1).mp hqdiv with hq2 | hq5
  · have hqeq : q = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hq1'.1.ne_one
    subst q
    have hbad : (2 : ℕ) ∣ 15 := hq6'.2.2
    norm_num at hbad
  · have hqeq : q = 5 :=
      ((Nat.dvd_prime Nat.prime_five).mp hq5).resolve_left hq1'.1.ne_one
    omega

/--
The `n=3`, `{1,6}` witness is old-support-disjoint but not
complete-point-coprime.
-/
theorem exists_oldSupportDisjoint_not_completeCoprime_family :
    ∃ R : Finset ℕ,
      PairwiseOldSupportDisjointSquareSeatFamily 3 R ∧
        ¬ PairwiseCoprimeSquareSeatFamily 3 R := by
  let R : Finset ℕ := {1, 6}
  have hfamily : PairwiseOldSupportDisjointSquareSeatFamily 3 R := by
    constructor
    · intro r hr
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact squareOffset_oldSupportCapacity_strictness_left
      · exact squareOffset_oldSupportCapacity_strictness_right
    · intro r hr s hs hrs
      have hr' : r = 1 ∨ r = 6 := by simpa [R] using hr
      have hs' : s = 1 ∨ s = 6 := by simpa [R] using hs
      rcases hr' with rfl | rfl
      · rcases hs' with rfl | rfl
        · exact (hrs rfl).elim
        · exact disjoint_oldSupportCapacity_strictness_supports
      · rcases hs' with rfl | rfl
        · exact disjoint_oldSupportCapacity_strictness_supports.symm
        · exact (hrs rfl).elim
  refine ⟨R, hfamily, ?_⟩
  intro hcop
  have hpoints := hcop.2 1 (by simp [R]) 6 (by simp [R]) (by norm_num)
  exact not_coprime_oldSupportCapacity_strictness_points hpoints

/-! ### PRIM-L029.4: exact ordered difference criterion -/

/--
For ordered offsets, actual old-support disjointness is exactly the absence
of a bounded prime divisor of the offset gap after it divides the first
complete point.
-/
theorem disjoint_squareOffsetPrimeSupport_iff_no_bounded_prime_dividing_offset_gap
    {n r s : ℕ} (hrs : r ≤ s) :
    Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) ↔
      ∀ q, Nat.Prime q → q ≤ n → q ∣ n ^ 2 + r →
        ¬ q ∣ s - r := by
  constructor
  · intro hdisj q hq hqle hqr hqgap
    have hqr' : q ∈ squareOffsetPrimeSupport n r :=
      mem_squareOffsetPrimeSupport.mpr ⟨hq, hqle, hqr⟩
    have hsum : q ∣ n ^ 2 + s := by
      have hid : n ^ 2 + s = (n ^ 2 + r) + (s - r) := by omega
      rw [hid]
      exact dvd_add hqr hqgap
    have hqs' : q ∈ squareOffsetPrimeSupport n s :=
      mem_squareOffsetPrimeSupport.mpr ⟨hq, hqle, hsum⟩
    exact (Finset.disjoint_left.mp hdisj) hqr' hqs'
  · intro hgap
    rw [Finset.disjoint_left]
    intro q hqr hqs
    have hqr' := mem_squareOffsetPrimeSupport.mp hqr
    have hqs' := mem_squareOffsetPrimeSupport.mp hqs
    have hid : n ^ 2 + s = (n ^ 2 + r) + (s - r) := by omega
    have hsum : q ∣ (n ^ 2 + r) + (s - r) := by
      simpa [hid] using hqs'.2.2
    have hqgap : q ∣ s - r :=
      (Nat.dvd_add_iff_right hqr'.2.2).mpr hsum
    exact hgap q hqr'.1 hqr'.2.1 hqr'.2.2 hqgap

/-! ### PRIM-L029.5: exact old-support capacity -/

/--
Full cover bounds an old-support-disjoint seat family by the finite old-prime
world, without any complete-point coprimality assumption.
-/
theorem card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (hfull : SquareOffsetsFullyCovered n) :
    R.card ≤ (primeScalesUpTo n).card := by
  classical
  have hnonempty : ∀ r ∈ R,
      (squareOffsetPrimeSupport n r).Nonempty := by
    intro r hr
    exact squareOffsetCovered_iff_primeSupport_nonempty.mp
      (hfull r (hfamily.1 r hr))
  have hunion :
      R.biUnion (fun r => squareOffsetPrimeSupport n r) ⊆
        primeScalesUpTo n := by
    intro q hq
    simp only [Finset.mem_biUnion] at hq
    rcases hq with ⟨r, hr, hqr⟩
    exact squareOffsetPrimeSupport_subset_primeScalesUpTo hqr
  calc
    R.card = ∑ r ∈ R, 1 := by simp
    _ ≤ ∑ r ∈ R, (squareOffsetPrimeSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.card_pos.mpr (hnonempty r hr)
    _ = (R.biUnion (fun r => squareOffsetPrimeSupport n r)).card := by
      symm
      exact Finset.card_biUnion hfamily.2
    _ ≤ (primeScalesUpTo n).card := Finset.card_le_card hunion

/-! ### PRIM-L029.6: strict old-support obstruction -/

/-- Strict old-support capacity excess prevents full cover. -/
theorem not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card < R.card) :
    ¬ SquareOffsetsFullyCovered n := by
  intro hfull
  exact (not_le_of_gt hcard)
    (card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
      hfamily hfull)

/-! ### PRIM-L029.7: local prime-square-cell consumer -/

/--
Strict old-support capacity excess yields a prime in the square cell through
the existing Frontier API.
-/
theorem exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    {n : ℕ} {R : Finset ℕ}
    (hn : 0 < n)
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  have hnotfull :=
    not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
      hfamily hcard
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

/-! ### PRIM-L029.8: optional universal sufficient provider -/

/--
A universal old-support-disjoint family provider is sufficient for Legendre's
conjecture.  This is one-way only; no converse or provider is asserted here.
-/
theorem legendreConjecture_of_universal_oldSupportCapacityProvider
    (hprovider : ∀ n, 0 < n → ∃ R : Finset ℕ,
      PairwiseOldSupportDisjointSquareSeatFamily n R ∧
        (primeScalesUpTo n).card < R.card) :
    LegendreConjecture := by
  intro n hn
  obtain ⟨R, hfamily, hcard⟩ := hprovider n hn
  exact exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    hn hfamily hcard

end DkMath.NumberTheory.Legendre
