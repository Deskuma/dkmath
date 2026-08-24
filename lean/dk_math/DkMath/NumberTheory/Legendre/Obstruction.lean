/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.QuotientSupport

#print "file: DkMath.NumberTheory.Legendre.Obstruction"

/-!
## Obstruction

PRIM-L017 seat classes, coprime trichotomy, and global obstruction ledgers.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-!
### PRIM-L017: coprime obstruction seats and the Direction/Depth budget

PRIM-L016 classifies one selected support incidence.  This checkpoint lifts
that result to whole coprime seats: a covered seat is either simple and fresh,
singleton-support with selected-prime depth, or multi-directional.  The last
two classes are charged to finite obstruction ledgers below.  These are exact
finite bookkeeping statements and upper bounds, not a contradiction or a
proof of Legendre's conjecture.
-/

/-! ### PRIM-L017.1: seat predicates and finite classes -/

/-- A coprime seat with one old direction and depth one. -/
def SquareAnchorCoprimeSimpleFreshSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    ¬ p ^ 2 ∣ n ^ 2 + r

/-- A coprime seat with one old direction and persistent selected depth. -/
def SquareAnchorCoprimeSingletonDepthSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    p ^ 2 ∣ n ^ 2 + r

/-- A coprime seat carrying at least two distinct old directions. -/
def SquareAnchorCoprimeMultiSupportSeat (n r : ℕ) : Prop :=
  2 ≤ (squareOffsetAnchorNondivisorSupport n r).card

/-- Coprime simple/fresh seats in the square window. -/
noncomputable def squareAnchorCoprimeSimpleFreshOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeSimpleFreshSeat n)

/-- Coprime singleton-depth seats in the square window. -/
noncomputable def squareAnchorCoprimeSingletonDepthOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeSingletonDepthSeat n)

/-- Coprime multi-direction seats in the square window. -/
noncomputable def squareAnchorCoprimeMultiSupportOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeMultiSupportSeat n)

@[simp] theorem mem_squareAnchorCoprimeSimpleFreshOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeSimpleFreshOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeSimpleFreshSeat n r := by
  simp [squareAnchorCoprimeSimpleFreshOffsets]

@[simp] theorem mem_squareAnchorCoprimeSingletonDepthOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeSingletonDepthOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeSingletonDepthSeat n r := by
  simp [squareAnchorCoprimeSingletonDepthOffsets]

@[simp] theorem mem_squareAnchorCoprimeMultiSupportOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeMultiSupportOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeMultiSupportSeat n r := by
  simp [squareAnchorCoprimeMultiSupportOffsets]

/-! ### PRIM-L017.2: seat trichotomy and partition -/

/-- A covered coprime seat is simple, depth-obstructed, or multi-directional. -/
theorem coprime_covered_seat_trichotomy
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r) :
    SquareAnchorCoprimeSimpleFreshSeat n r ∨
      SquareAnchorCoprimeSingletonDepthSeat n r ∨
      SquareAnchorCoprimeMultiSupportSeat n r := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hnondiv :=
    (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hr'.2).mp hcovered
  rcases hnondiv with ⟨p, hpWorld, hpforbid⟩
  have hpWorld' := mem_squareAnchorNondivisorPrimes.mp hpWorld
  have hp : p ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpWorld'.1, hpWorld'.2.1, hpWorld'.2.2, hpforbid⟩
  by_cases hcard :
      (squareOffsetAnchorNondivisorSupport n r).card = 1
  · have hsingle : squareOffsetAnchorNondivisorSupport n r = {p} := by
      rcases Finset.card_eq_one.mp hcard with ⟨q, hq⟩
      have hpq : p = q := by
        have hpq' : p ∈ ({q} : Finset ℕ) := by
          rw [← hq]
          exact hp
        simpa using hpq'
      calc
        squareOffsetAnchorNondivisorSupport n r = {q} := hq
        _ = {p} := by rw [hpq]
    by_cases hdepth : p ^ 2 ∣ n ^ 2 + r
    · exact Or.inr (Or.inl ⟨p, hp, hsingle, hdepth⟩)
    · exact Or.inl ⟨p, hp, hsingle, hdepth⟩
  · have hmulti :
        2 ≤ (squareOffsetAnchorNondivisorSupport n r).card := by
      have hpos : 0 < (squareOffsetAnchorNondivisorSupport n r).card :=
        Finset.card_pos.mpr ⟨p, hp⟩
      omega
    exact Or.inr (Or.inr hmulti)

private theorem not_simple_and_singletonDepth_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSimpleFreshSeat n r ∧
      SquareAnchorCoprimeSingletonDepthSeat n r) := by
  rintro ⟨hsimple, hdepth⟩
  rcases hsimple with ⟨p, hp, hpsingle, hpnot⟩
  rcases hdepth with ⟨q, hq, hqsingle, hqdepth⟩
  have hpq : p = q := by
    have hpq' : p ∈ ({q} : Finset ℕ) := by
      rw [← hqsingle]
      exact hp
    simpa using hpq'
  subst q
  exact hpnot hqdepth

private theorem not_simple_and_multiSupport_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSimpleFreshSeat n r ∧
      SquareAnchorCoprimeMultiSupportSeat n r) := by
  rintro ⟨hsimple, hmulti⟩
  rcases hsimple with ⟨p, hp, hsingle, _⟩
  dsimp [SquareAnchorCoprimeMultiSupportSeat] at hmulti
  rw [hsingle] at hmulti
  simp at hmulti

private theorem not_singletonDepth_and_multiSupport_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSingletonDepthSeat n r ∧
      SquareAnchorCoprimeMultiSupportSeat n r) := by
  rintro ⟨hdepth, hmulti⟩
  rcases hdepth with ⟨p, hp, hsingle, _⟩
  dsimp [SquareAnchorCoprimeMultiSupportSeat] at hmulti
  rw [hsingle] at hmulti
  simp at hmulti

theorem disjoint_squareAnchorCoprimeSimpleFreshOffsets_singletonDepthOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSimpleFreshOffsets n)
      (squareAnchorCoprimeSingletonDepthOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hs hd
  exact not_simple_and_singletonDepth_seat
    ⟨(mem_squareAnchorCoprimeSimpleFreshOffsets.mp hs).2,
      (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hd).2⟩

theorem disjoint_squareAnchorCoprimeSimpleFreshOffsets_multiSupportOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSimpleFreshOffsets n)
      (squareAnchorCoprimeMultiSupportOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hs hm
  exact not_simple_and_multiSupport_seat
    ⟨(mem_squareAnchorCoprimeSimpleFreshOffsets.mp hs).2,
      (mem_squareAnchorCoprimeMultiSupportOffsets.mp hm).2⟩

theorem disjoint_squareAnchorCoprimeSingletonDepthOffsets_multiSupportOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSingletonDepthOffsets n)
      (squareAnchorCoprimeMultiSupportOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hd hm
  exact not_singletonDepth_and_multiSupport_seat
    ⟨(mem_squareAnchorCoprimeSingletonDepthOffsets.mp hd).2,
      (mem_squareAnchorCoprimeMultiSupportOffsets.mp hm).2⟩

/-- Under full cover, the coprime window is the disjoint three-class union. -/
theorem squareAnchorCoprimeOffsets_eq_simpleFresh_union_singletonDepth_union_multi
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    squareAnchorCoprimeOffsets n =
      (squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n) ∪
        squareAnchorCoprimeMultiSupportOffsets n := by
  ext r
  constructor
  · intro hr
    have hcop := mem_squareAnchorCoprimeOffsets.mp hr
    rcases coprime_covered_seat_trichotomy hn hr (hfull r hcop.1) with
      hsimple | hdepth | hmulti
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (mem_squareAnchorCoprimeSimpleFreshOffsets.mpr ⟨hr, hsimple⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (mem_squareAnchorCoprimeSingletonDepthOffsets.mpr ⟨hr, hdepth⟩))
    · exact Finset.mem_union_right _
        (mem_squareAnchorCoprimeMultiSupportOffsets.mpr ⟨hr, hmulti⟩)
  · intro hr
    rcases Finset.mem_union.mp hr with hrleft | hrmulti
    · rcases Finset.mem_union.mp hrleft with hrsimple | hrdepth
      · exact (mem_squareAnchorCoprimeSimpleFreshOffsets.mp hrsimple).1
      · exact (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hrdepth).1
    · exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hrmulti).1

theorem two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n =
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      (squareAnchorCoprimeSingletonDepthOffsets n).card +
      (squareAnchorCoprimeMultiSupportOffsets n).card := by
  have hdisjLeft :=
    disjoint_squareAnchorCoprimeSimpleFreshOffsets_singletonDepthOffsets n
  have hdisjRight :
      Disjoint
        (squareAnchorCoprimeSimpleFreshOffsets n ∪
          squareAnchorCoprimeSingletonDepthOffsets n)
        (squareAnchorCoprimeMultiSupportOffsets n) := by
    rw [Finset.disjoint_left]
    intro r hleft hmulti
    rcases Finset.mem_union.mp hleft with hs | hd
    · exact (Finset.disjoint_left.mp
        (disjoint_squareAnchorCoprimeSimpleFreshOffsets_multiSupportOffsets n))
        hs hmulti
    · exact (Finset.disjoint_left.mp
        (disjoint_squareAnchorCoprimeSingletonDepthOffsets_multiSupportOffsets n))
        hd hmulti
  calc
    2 * Nat.totient n = (squareAnchorCoprimeOffsets n).card :=
      (card_squareAnchorCoprimeOffsets hn).symm
    _ = ((squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n) ∪
        squareAnchorCoprimeMultiSupportOffsets n).card :=
      congrArg Finset.card
        (squareAnchorCoprimeOffsets_eq_simpleFresh_union_singletonDepth_union_multi
          hn hfull)
    _ = (squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n).card +
        (squareAnchorCoprimeMultiSupportOffsets n).card :=
      Finset.card_union_of_disjoint hdisjRight
    _ = (squareAnchorCoprimeSimpleFreshOffsets n).card +
        (squareAnchorCoprimeSingletonDepthOffsets n).card +
        (squareAnchorCoprimeMultiSupportOffsets n).card := by
      rw [Finset.card_union_of_disjoint hdisjLeft]

/-! ### PRIM-L017.3: simple seats and the depth budget -/

/-- A simple seat supplies a finite-world fresh quotient direction. -/
theorem exists_fresh_quotient_of_mem_simpleFreshOffsets
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeSimpleFreshOffsets n) :
    ∃ p,
      p ∈ squareOffsetAnchorNondivisorSupport n r ∧
      FreshPrimeDirection
        (primeScalesUpTo n)
        (squareOffsetSupportQuotient n p r)
        (squareOffsetSupportQuotient n p r) := by
  have hr' := mem_squareAnchorCoprimeSimpleFreshOffsets.mp hr
  rcases hr'.2 with ⟨p, hp, hsingle, hdepth⟩
  exact ⟨p, hp,
    freshPrimeDirection_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
      hn hr'.1 hp hsingle hdepth⟩

/-- The upper ledger of singleton-depth seats, counting all `p^2` wave hits. -/
noncomputable def squareAnchorPrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareWaveOffsets n (p ^ 2)).card

/-- Singleton-depth seats are paid for by the prime-square wave ledger. -/
theorem card_singletonDepthOffsets_le_primeSquareDepthBudget
    (n : ℕ) :
    (squareAnchorCoprimeSingletonDepthOffsets n).card ≤
      squareAnchorPrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorPrimeSquareDepthBudget
  have hsubset : squareAnchorCoprimeSingletonDepthOffsets n ⊆
      squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr).1).1
  calc
    (squareAnchorCoprimeSingletonDepthOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr
      rcases hr'.2 with ⟨p, hp, _, hdepth⟩
      have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
      have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
        mem_squareAnchorNondivisorPrimes.mpr
          ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
      have hwave : r ∈ squareWaveOffsets n (p ^ 2) :=
        mem_squareWaveOffsets.mpr ⟨
          (mem_squareAnchorCoprimeOffsets.mp hr'.1).1, hdepth⟩
      have hsingle := Finset.single_le_sum
        (f := fun q => if r ∈ squareWaveOffsets n (q ^ 2) then 1 else 0)
        (fun q _ => Nat.zero_le _) hpWorld
      simpa [hwave] using hsingle
    _ ≤ ∑ r ∈ squareOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareOffsets n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          (squareWaveOffsets n (p ^ 2)).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareWaveOffsets, mem_squareOffsets]

/-- Exact baseline-plus-carry arithmetic form of the depth budget. -/
theorem squareAnchorPrimeSquareDepthBudget_eq_sum_div_add_carry
    (n : ℕ) :
    squareAnchorPrimeSquareDepthBudget n =
      ∑ p ∈ squareAnchorNondivisorPrimes n,
        ((2 * n) / (p ^ 2) + squareWaveCarry n (p ^ 2)) := by
  unfold squareAnchorPrimeSquareDepthBudget
  apply Finset.sum_congr rfl
  intro p hp
  simpa using card_squareWaveOffsets_eq_div_add_carry
    (Nat.pow_pos (mem_squareAnchorNondivisorPrimes.mp hp).1.pos)

/-! ### PRIM-L017.4: multi-direction and combined obstruction budgets -/

/-- Multi-direction seats are paid for by the existing pair-overlap ledger. -/
theorem card_multiSupportOffsets_le_squarePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squarePrimePairOverlapCount n := by
  classical
  have hmulti_subset : squareAnchorCoprimeMultiSupportOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hr).1
  have hcop_subset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp hr).1
  calc
    (squareAnchorCoprimeMultiSupportOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      apply Finset.sum_le_sum
      intro r hr
      have hmulti := mem_squareAnchorCoprimeMultiSupportOffsets.mp hr
      have hcop := mem_squareAnchorCoprimeOffsets.mp hmulti.1
      have hnpos : 0 < n := by
        dsimp [SquareOffset] at hcop
        omega
      have hsupport :=
        squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
          hnpos hcop.2
      have hcard : 2 ≤ (squareOffsetPrimeSupport n r).card := by
        rw [hsupport]
        simpa [SquareAnchorCoprimeMultiSupportSeat] using hmulti.2
      have hpair := primeSupport_sub_one_le_pairMultiplicity (n := n) (r := r)
      omega
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hmulti_subset
        (fun r _ _ => Nat.zero_le _)
    _ ≤ ∑ r ∈ squareOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hcop_subset
        (fun r _ _ => Nat.zero_le _)
    _ = squarePrimePairOverlapCount n :=
      (squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity n).symm

/-- Full cover separates coprime seats into fresh and obstruction budgets. -/
theorem two_mul_totient_le_simpleFresh_add_depthBudget_add_pairOverlap_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n := by
  have hpartition :=
    two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered hn hfull
  have hdepth := card_singletonDepthOffsets_le_primeSquareDepthBudget n
  have hmulti := card_multiSupportOffsets_le_squarePrimePairOverlapCount n
  calc
    2 * Nat.totient n =
        (squareAnchorCoprimeSimpleFreshOffsets n).card +
          (squareAnchorCoprimeSingletonDepthOffsets n).card +
          (squareAnchorCoprimeMultiSupportOffsets n).card := hpartition
    _ ≤ (squareAnchorCoprimeSimpleFreshOffsets n).card +
          squareAnchorPrimeSquareDepthBudget n +
          squarePrimePairOverlapCount n := by omega

/-- If no simple seat occurs, only the two finite obstruction budgets remain. -/
theorem two_mul_totient_le_depthBudget_add_pairOverlap_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n := by
  have hmain :=
    two_mul_totient_le_simpleFresh_add_depthBudget_add_pairOverlap_of_fullyCovered
      hn hfull
  simpa [hno] using hmain

end DkMath.NumberTheory.Legendre

