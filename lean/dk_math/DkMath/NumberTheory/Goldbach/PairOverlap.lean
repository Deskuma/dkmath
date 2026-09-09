/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Overlap
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.Goldbach.PairOverlap"

/-!
# Goldbach unordered prime-pair overlap ledger

An offset with `k` distinct obstruction primes has `choose k 2` unordered
obstruction pairs.  Pascal's identity splits this pair layer into the first
repeated-obstruction payment `k - 1` and a higher local residual
`choose (k - 1) 2`.  Thus pair overlap is the `r = 2` layer of the local
Pascal hierarchy.  Summing the canonical pairs over offsets gives an exact
double-count identity and an exact global residual decomposition.  This
suggests a future connection to the canonical GTail/Pascal filtration, but no
formal GTail equivalence is asserted here.  None of these ledgers is a
Goldbach escape theorem.
-/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- One offset's unordered pair multiplicity among proper small obstructions. -/
def goldbachOffsetPrimePairMultiplicity (n u : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupport n u).card 2

/-- The higher local pair-overlap residual after removing the first payment. -/
def goldbachLocalPairOverlapResidual (n u : ℕ) : ℕ :=
  Nat.choose ((goldbachObstructionSupport n u).card - 1) 2

/-- The general local `r`-fold observer for the finite Pascal hierarchy. -/
def goldbachOffsetROverlapMultiplicity (n u r : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupport n u).card r

@[simp] theorem goldbachOffsetROverlapMultiplicity_zero (n u : ℕ) :
    goldbachOffsetROverlapMultiplicity n u 0 = 1 := by
  simp [goldbachOffsetROverlapMultiplicity]

@[simp] theorem goldbachOffsetROverlapMultiplicity_one (n u : ℕ) :
    goldbachOffsetROverlapMultiplicity n u 1 =
      (goldbachObstructionSupport n u).card := by
  simp [goldbachOffsetROverlapMultiplicity]

@[simp] theorem goldbachOffsetROverlapMultiplicity_two (n u : ℕ) :
    goldbachOffsetROverlapMultiplicity n u 2 =
      goldbachOffsetPrimePairMultiplicity n u := by
  rfl

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

/-- Exact local Pascal decomposition of pair multiplicity. -/
theorem goldbach_pairMultiplicity_eq_localOverlap_add_residual
    (n u : ℕ) :
    goldbachOffsetPrimePairMultiplicity n u =
      goldbachLocalOverlapExcess n u +
        goldbachLocalPairOverlapResidual n u := by
  unfold goldbachOffsetPrimePairMultiplicity goldbachLocalPairOverlapResidual
  exact choose_two_eq_sub_one_add_choose_sub_one _

/-- A support of size `k` has at least `k-1` unordered distinct pairs. -/
theorem goldbach_support_sub_one_le_pairMultiplicity
    {n u : ℕ} :
    (goldbachObstructionSupport n u).card - 1 ≤
      goldbachOffsetPrimePairMultiplicity n u := by
  unfold goldbachOffsetPrimePairMultiplicity
  rw [Nat.choose_two_right]
  by_cases hsmall : (goldbachObstructionSupport n u).card ≤ 1
  · omega
  · have hlarge : 2 ≤ (goldbachObstructionSupport n u).card := by omega
    apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right ((goldbachObstructionSupport n u).card - 1) hlarge)

/-- One canonical unordered pair of every two distinct small obstruction primes. -/
def goldbachPrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((goldbachSmallPrimes n).product (goldbachSmallPrimes n)).filter
    (fun pair => pair.1 < pair.2)

@[simp] theorem mem_goldbachPrimePairs {n p q : ℕ} :
    (p, q) ∈ goldbachPrimePairs n ↔
      p ∈ goldbachSmallPrimes n ∧ q ∈ goldbachSmallPrimes n ∧ p < q := by
  simp [goldbachPrimePairs, and_assoc]

/-- Offsets where both members of a canonical pair are proper obstructions. -/
def goldbachPrimePairOverlapOffsets (n p q : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter
    (fun u => GoldbachProperObstructed n p u ∧
      GoldbachProperObstructed n q u)

/-- Total overlap incidences over canonical unordered small-prime pairs. -/
def goldbachPrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ goldbachPrimePairs n,
    (goldbachPrimePairOverlapOffsets n pair.1 pair.2).card

/-- Global residual mass in the pair-overlap Pascal layer. -/
def goldbachPairOverlapResidual (n : ℕ) : ℕ :=
  ∑ u ∈ goldbachOffsets n, goldbachLocalPairOverlapResidual n u

private def goldbachUpperPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.1 < pair.2)

private def goldbachLowerPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.2 < pair.1)

private theorem goldbach_card_upperPairs_eq_choose (s : Finset ℕ) :
    (goldbachUpperPairs s).card = Nat.choose s.card 2 := by
  classical
  have hswap : (goldbachLowerPairs s).card = (goldbachUpperPairs s).card := by
    apply Finset.card_bij (fun pair _ => (pair.2, pair.1))
    · intro pair hpair
      have hpair' := Finset.mem_filter.mp hpair
      have hdiag := Finset.mem_offDiag.mp hpair'.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_offDiag.mpr
          ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩, hpair'.2⟩
    · intro pair₁ hpair₁ pair₂ hpair₂ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pair hpair
      refine ⟨(pair.2, pair.1), ?_, ?_⟩
      · have hpair' := Finset.mem_filter.mp hpair
        have hdiag := Finset.mem_offDiag.mp hpair'.1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr
            ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩, hpair'.2⟩
      · rfl
  have hneg : s.offDiag.filter (fun pair => ¬ pair.1 < pair.2) =
      goldbachLowerPairs s := by
    ext pair
    simp [goldbachLowerPairs]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s.offDiag) (p := fun pair : ℕ × ℕ => pair.1 < pair.2)
  rw [hneg] at hsplit
  have hsum : (goldbachUpperPairs s).card +
      (goldbachLowerPairs s).card = s.offDiag.card := by
    simpa [goldbachUpperPairs] using hsplit
  have htwice : 2 * (goldbachUpperPairs s).card = s.offDiag.card := by
    omega
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one,
    ← Finset.offDiag_card]
  exact (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two htwice.symm).symm

private theorem goldbach_product_filter_eq_upperPairs (s : Finset ℕ) :
    (s.product s).filter (fun pair => pair.1 < pair.2) =
      goldbachUpperPairs s := by
  ext pair
  rcases pair with ⟨p, q⟩
  simp [goldbachUpperPairs, Finset.mem_offDiag]
  omega

/-- The pair ledger is exactly the sum of local unordered support-pair counts. -/
theorem goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity (n : ℕ) :
    goldbachPrimePairOverlapCount n =
      ∑ u ∈ goldbachOffsets n,
        goldbachOffsetPrimePairMultiplicity n u := by
  classical
  have hpairset (u : ℕ) :
      (goldbachPrimePairs n).filter
          (fun pair => pair.1 ∈ goldbachObstructionSupport n u ∧
            pair.2 ∈ goldbachObstructionSupport n u) =
        goldbachUpperPairs (goldbachObstructionSupport n u) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [goldbachPrimePairs, goldbachUpperPairs,
      goldbachObstructionSupport, Finset.mem_offDiag, and_assoc,
      and_left_comm, and_comm]
    omega
  unfold goldbachPrimePairOverlapCount
  calc
    (∑ pair ∈ goldbachPrimePairs n,
        (goldbachPrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ goldbachPrimePairs n, ∑ u ∈ goldbachOffsets n,
          if GoldbachProperObstructed n pair.1 u ∧
              GoldbachProperObstructed n pair.2 u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      unfold goldbachPrimePairOverlapOffsets
      rw [Finset.card_filter]
    _ = ∑ u ∈ goldbachOffsets n, ∑ pair ∈ goldbachPrimePairs n,
          if GoldbachProperObstructed n pair.1 u ∧
              GoldbachProperObstructed n pair.2 u then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ goldbachOffsets n,
          ((goldbachPrimePairs n).filter
            (fun pair => GoldbachProperObstructed n pair.1 u ∧
              GoldbachProperObstructed n pair.2 u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.card_filter]
    _ = ∑ u ∈ goldbachOffsets n,
          ((goldbachPrimePairs n).filter
            (fun pair => pair.1 ∈ goldbachObstructionSupport n u ∧
              pair.2 ∈ goldbachObstructionSupport n u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      ext pair
      rcases pair with ⟨p, q⟩
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hmem, hp, hq⟩
        exact ⟨hmem, mem_goldbachObstructionSupport.mpr
          ⟨(mem_goldbachPrimePairs.mp hmem).1, hp⟩,
          mem_goldbachObstructionSupport.mpr
            ⟨(mem_goldbachPrimePairs.mp hmem).2.1, hq⟩⟩
      · rintro ⟨hmem, hp, hq⟩
        exact ⟨hmem, (mem_goldbachObstructionSupport.mp hp).2,
          (mem_goldbachObstructionSupport.mp hq).2⟩
    _ = ∑ u ∈ goldbachOffsets n,
          (goldbachUpperPairs (goldbachObstructionSupport n u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hpairset]
    _ = ∑ u ∈ goldbachOffsets n,
          goldbachOffsetPrimePairMultiplicity n u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact goldbach_card_upperPairs_eq_choose _

/-- Exact global pair-overlap decomposition into first payment and residual. -/
theorem goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual
    (n : ℕ) :
    goldbachPrimePairOverlapCount n =
      goldbachOverlapExcess n + goldbachPairOverlapResidual n := by
  rw [goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity]
  unfold goldbachOverlapExcess goldbachPairOverlapResidual
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact goldbach_pairMultiplicity_eq_localOverlap_add_residual n u

/-- Pair overlap dominates the repeated-obstruction excess at every offset. -/
theorem goldbachOverlapExcess_le_primePairOverlapCount (n : ℕ) :
    goldbachOverlapExcess n ≤ goldbachPrimePairOverlapCount n := by
  rw [goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual]
  omega

end DkMath.NumberTheory
