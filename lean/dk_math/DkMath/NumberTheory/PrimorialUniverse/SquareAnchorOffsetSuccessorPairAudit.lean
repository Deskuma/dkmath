/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetPositiveFirstHitAudit
import Mathlib.Tactic

/-!
# Successor-pair positive first-hit audit

This provider-side module couples two consecutive square-anchor phases.  The
pair coordinate is the minimum of their positive first-hit coordinates, so it
records the first distance at which at least one adjacent anchor reaches a
wheel survivor.  The finite audit does not introduce a shell-width theorem,
primality claim, Jacobsthal theory, or a Legendre consumer.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Pair coordinate and semantics -/

/-- The positive first-hit coordinate of two consecutive square anchors. -/
noncomputable def squareAnchorSuccessorPairPositiveFirstHit
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  min
    (squareAnchorFirstPositiveUnreservedOffset S n hS hSne)
    (squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne)

/-- The pair coordinate is strictly positive. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_pos
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    0 < squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
  unfold squareAnchorSuccessorPairPositiveFirstHit
  exact (lt_min
    (squareAnchorFirstPositiveUnreservedOffset_pos hS hSne n)
    (squareAnchorFirstPositiveUnreservedOffset_pos hS hSne (n + 1)))

/-- The pair coordinate is bounded by the left first hit. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_le_left
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ≤
      squareAnchorFirstPositiveUnreservedOffset S n hS hSne := by
  exact min_le_left _ _

/-- The pair coordinate is bounded by the right first hit. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_le_right
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ≤
      squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne := by
  exact min_le_right _ _

/-- The pair coordinate is bounded by one wheel period. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_le_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ≤
      finitePrimeBasisProduct S := by
  exact (squareAnchorSuccessorPairPositiveFirstHit_le_left hS hSne n).trans
    (squareAnchorFirstPositiveUnreservedOffset_le_period hS hSne n)

/-- At the pair distance, one of the two consecutive anchors reaches a
wheel survivor. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_survivor_left_or_right
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    IsPrimeBasisWheelSurvivor S
        ((squareAnchorWheelProjection S n +
          squareAnchorSuccessorPairPositiveFirstHit S n hS hSne) %
          finitePrimeBasisProduct S) ∨
      IsPrimeBasisWheelSurvivor S
        ((squareAnchorWheelProjection S (n + 1) +
          squareAnchorSuccessorPairPositiveFirstHit S n hS hSne) %
          finitePrimeBasisProduct S) := by
  unfold squareAnchorSuccessorPairPositiveFirstHit
  by_cases hle : squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤
      squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne
  · left
    rw [min_eq_left hle]
    exact squareAnchorFirstPositiveUnreservedOffset_survivor hS hSne n
  · right
    rw [min_eq_right (Nat.le_of_not_ge hle)]
    exact squareAnchorFirstPositiveUnreservedOffset_survivor hS hSne (n + 1)

/-- A threshold is below the pair coordinate exactly when both anchors are
bad at that threshold. -/
theorem le_squareAnchorSuccessorPairPositiveFirstHit_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ) :
    k ≤ squareAnchorSuccessorPairPositiveFirstHit S n hS hSne ↔
      k ≤ squareAnchorFirstPositiveUnreservedOffset S n hS hSne ∧
        k ≤ squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne := by
  unfold squareAnchorSuccessorPairPositiveFirstHit
  constructor
  · intro hk
    exact ⟨hk.trans (min_le_left _ _), hk.trans (min_le_right _ _)⟩
  · rintro ⟨hleft, hright⟩
    exact le_min hleft hright

/-- The pair coordinate is below a threshold exactly when at least one
adjacent anchor is good before that threshold. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_lt_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne < k ↔
      squareAnchorFirstPositiveUnreservedOffset S n hS hSne < k ∨
        squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne < k := by
  constructor
  · intro hpair
    by_contra hnot
    have hnot' : k ≤ squareAnchorFirstPositiveUnreservedOffset S n hS hSne ∧
        k ≤ squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne := by
      constructor <;> omega
    have hle := (le_squareAnchorSuccessorPairPositiveFirstHit_iff hS hSne n k).mpr hnot'
    omega
  · rintro (hleft | hright)
    · exact lt_of_le_of_lt
        (squareAnchorSuccessorPairPositiveFirstHit_le_left hS hSne n) hleft
    · exact lt_of_le_of_lt
        (squareAnchorSuccessorPairPositiveFirstHit_le_right hS hSne n) hright

/-! ## Pair radius and periodicity -/

/-- Worst consecutive-pair positive first hit over one anchor period. -/
noncomputable def squareSuccessorPairPositiveFirstHitRadius
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).sup fun n =>
    squareAnchorSuccessorPairPositiveFirstHit S n hS hSne

/-- The successor-pair radius is bounded by the single-anchor square radius. -/
theorem squareSuccessorPairPositiveFirstHitRadius_le_squarePositiveFirstHitRadius
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) :
    squareSuccessorPairPositiveFirstHitRadius S hS hSne ≤
      squarePositiveFirstHitRadius S hS hSne := by
  unfold squareSuccessorPairPositiveFirstHitRadius
  apply Finset.sup_le
  intro n hn
  exact (squareAnchorSuccessorPairPositiveFirstHit_le_left hS hSne n).trans
    (squareAnchorFirstPositiveUnreservedOffset_le_squarePositiveFirstHitRadius
      hS hSne n)

/-- Shifting an anchor by one old period leaves the pair coordinate unchanged. -/
theorem squareAnchorSuccessorPairPositiveFirstHit_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorSuccessorPairPositiveFirstHit S
        (n + finitePrimeBasisProduct S) hS hSne =
      squareAnchorSuccessorPairPositiveFirstHit S n hS hSne := by
  have hphase₀ := sameSquareAnchorPhase_add_mul_period hS n 1
  have hphase₁ := sameSquareAnchorPhase_add_mul_period hS (n + 1) 1
  have h₀ := squareAnchorFirstPositiveUnreservedOffset_eq_of_samePhase
    hS hphase₀ hSne
  have h₁ := squareAnchorFirstPositiveUnreservedOffset_eq_of_samePhase
    hS hphase₁ hSne
  have h₀' : squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
      squareAnchorFirstPositiveUnreservedOffset S
        (n + finitePrimeBasisProduct S) hS hSne := by
    simpa using h₀
  have h₁' : squareAnchorFirstPositiveUnreservedOffset S (n + 1) hS hSne =
      squareAnchorFirstPositiveUnreservedOffset S
        ((n + 1) + finitePrimeBasisProduct S) hS hSne := by
    simpa using h₁
  unfold squareAnchorSuccessorPairPositiveFirstHit
  rw [← h₀']
  have harg : n + finitePrimeBasisProduct S + 1 =
      (n + 1) + finitePrimeBasisProduct S := by omega
  rw [harg, ← h₁']

/-! ## Small helper for finite regressions -/

private theorem squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n k : ℕ)
    (hk : k ∈ genericPositiveUnreservedOffsetProfile S
      (squareAnchorWheelProjection S n)) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤ k := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  have hle := Finset.min'_le
    (genericPositiveUnreservedOffsetProfile S (squareAnchorWheelProjection S n))
    k hk
  simpa [genericFirstPositiveUnreservedOffset] using hle

/-! ## Exact finite regressions -/

private theorem isFinitePrimeBasis_two_three_successorPair :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

private theorem isFinitePrimeBasis_two_three_five_successorPair :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- For `{2,3}`, successor pairing reduces the positive radius from `4` to
`1`. -/
theorem squareSuccessorPairPositiveFirstHit_two_three_regression :
    squarePositiveFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_successorPair (by simp) = 4 ∧
      squareSuccessorPairPositiveFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_successorPair (by simp) = 1 := by
  have hS := isFinitePrimeBasis_two_three_successorPair
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hfirst_le_one_at : ∀ m,
      squareAnchorWheelProjection ({2, 3} : Finset ℕ) m = 0 ∨
        squareAnchorWheelProjection ({2, 3} : Finset ℕ) m = 4 →
      squareAnchorFirstPositiveUnreservedOffset ({2, 3} : Finset ℕ) m
        hS hSne ≤ 1 := by
    intro m hm
    apply squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem hS hSne
      m 1
    rw [mem_genericPositiveUnreservedOffsetProfile_iff]
    rcases hm with hm | hm <;>
      norm_num [hm, finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis]
  have hpair_upper : squareSuccessorPairPositiveFirstHitRadius
      ({2, 3} : Finset ℕ) hS hSne ≤ 1 := by
    unfold squareSuccessorPairPositiveFirstHitRadius
    apply Finset.sup_le
    intro n hn
    have hn' : n < 6 := by simpa [finitePrimeBasisProduct] using hn
    have hphase :
        squareAnchorWheelProjection ({2, 3} : Finset ℕ) n = 0 ∨
          squareAnchorWheelProjection ({2, 3} : Finset ℕ) n = 4 ∨
          squareAnchorWheelProjection ({2, 3} : Finset ℕ) (n + 1) = 0 ∨
          squareAnchorWheelProjection ({2, 3} : Finset ℕ) (n + 1) = 4 := by
      interval_cases n <;>
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]
    rcases hphase with hphase | hphase | hphase | hphase
    · exact (min_le_left _ _).trans (hfirst_le_one_at n (Or.inl hphase))
    · exact (min_le_left _ _).trans (hfirst_le_one_at n (Or.inr hphase))
    · exact (min_le_right _ _).trans
        (hfirst_le_one_at (n + 1) (Or.inl hphase))
    · exact (min_le_right _ _).trans
        (hfirst_le_one_at (n + 1) (Or.inr hphase))
  have hpair_lower : 1 ≤ squareSuccessorPairPositiveFirstHitRadius
      ({2, 3} : Finset ℕ) hS hSne := by
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3} : Finset ℕ)))
      (b := 0)
      (f := fun n => squareAnchorSuccessorPairPositiveFirstHit
        ({2, 3} : Finset ℕ) n hS hSne)
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    have hpos := squareAnchorSuccessorPairPositiveFirstHit_pos hS hSne 0
    exact Nat.succ_le_of_lt (lt_of_lt_of_le hpos hle)
  have hsq : squarePositiveFirstHitRadius ({2, 3} : Finset ℕ) hS hSne = 4 := by
    simpa using (squarePhasePositiveFirstHit_two_three_regression).2.1
  exact ⟨hsq, le_antisymm hpair_upper hpair_lower⟩

/-- For `{2,3,5}`, successor pairing reduces the positive radius from `6` to
`5`; the edge at `n = 11` has first hits `6` and `5`. -/
theorem squareSuccessorPairPositiveFirstHit_two_three_five_regression :
    squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_successorPair (by simp) = 6 ∧
      squareSuccessorPairPositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_successorPair (by simp) = 5 ∧
      squareAnchorSuccessorPairPositiveFirstHit ({2, 3, 5} : Finset ℕ) 11
        isFinitePrimeBasis_two_three_five_successorPair (by simp) = 5 ∧
      squareAnchorFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 11
        isFinitePrimeBasis_two_three_five_successorPair (by simp) = 6 ∧
      squareAnchorFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 12
        isFinitePrimeBasis_two_three_five_successorPair (by simp) = 5 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 11 = 1 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 12 = 24 := by
  have hS := isFinitePrimeBasis_two_three_five_successorPair
  have hSne : ({2, 3, 5} : Finset ℕ).Nonempty := by simp
  have hfirst_le_five : ∀ A, A < 30 → A ≠ 1 → A ≠ 23 →
      genericFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) A hS hSne ≤ 5 := by
    intro A hA hne hne23
    have hwithin : ∃ t, t ≤ 5 ∧
        t ∈ genericPositiveUnreservedOffsetProfile
          ({2, 3, 5} : Finset ℕ) A := by
      interval_cases A <;>
        first
        | exact (hne rfl).elim
        | exact (hne23 rfl).elim
        | (refine ⟨1, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨2, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨3, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨4, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨5, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis])
    obtain ⟨t, ht, htm⟩ := hwithin
    have hle := Finset.min'_le
      (genericPositiveUnreservedOffsetProfile ({2, 3, 5} : Finset ℕ) A) t htm
    have hfirst : genericFirstPositiveUnreservedOffset
        ({2, 3, 5} : Finset ℕ) A hS hSne ≤ t := by
      simpa [genericFirstPositiveUnreservedOffset] using hle
    exact hfirst.trans ht
  have hpair_upper : squareSuccessorPairPositiveFirstHitRadius
      ({2, 3, 5} : Finset ℕ) hS hSne ≤ 5 := by
    unfold squareSuccessorPairPositiveFirstHitRadius
    apply Finset.sup_le
    intro n hn
    have hn' : n < 30 := by simpa [finitePrimeBasisProduct] using hn
    have hphase :
        (squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) n ≠ 1 ∧
          squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) n ≠ 23) ∨
        (squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) (n + 1) ≠ 1 ∧
          squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) (n + 1) ≠ 23) := by
      interval_cases n <;>
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]
    rcases hphase with hleft | hright
    · rw [squareAnchorSuccessorPairPositiveFirstHit]
      apply (min_le_left _ _).trans
      rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
      apply hfirst_le_five
      · exact Nat.mod_lt _ (by norm_num [finitePrimeBasisProduct])
      · exact hleft.1
      · exact hleft.2
    · rw [squareAnchorSuccessorPairPositiveFirstHit]
      apply (min_le_right _ _).trans
      rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne (n + 1)]
      apply hfirst_le_five
      · exact Nat.mod_lt _ (by norm_num [finitePrimeBasisProduct])
      · exact hright.1
      · exact hright.2
  have hfirst11_le : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 11 hS hSne ≤ 6 := by
    apply squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem hS hSne 11 6
    rw [mem_genericPositiveUnreservedOffsetProfile_iff]
    norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
  have hfirst12_le : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 12 hS hSne ≤ 5 := by
    apply squareAnchorFirstPositiveUnreservedOffset_le_of_profile_mem hS hSne 12 5
    rw [mem_genericPositiveUnreservedOffsetProfile_iff]
    norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
  have hfirst11_ge : 6 ≤ squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 11 hS hSne := by
    by_contra hnot
    have hlt := Nat.lt_of_not_ge hnot
    have hpos := squareAnchorFirstPositiveUnreservedOffset_pos hS hSne 11
    have hsurv := squareAnchorFirstPositiveUnreservedOffset_survivor hS hSne 11
    interval_cases hval : squareAnchorFirstPositiveUnreservedOffset
        ({2, 3, 5} : Finset ℕ) 11 hS hSne <;>
      norm_num [hval, squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis] at hsurv
  have hfirst12_ge : 5 ≤ squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 12 hS hSne := by
    by_contra hnot
    have hlt := Nat.lt_of_not_ge hnot
    have hpos := squareAnchorFirstPositiveUnreservedOffset_pos hS hSne 12
    have hsurv := squareAnchorFirstPositiveUnreservedOffset_survivor hS hSne 12
    interval_cases hval : squareAnchorFirstPositiveUnreservedOffset
        ({2, 3, 5} : Finset ℕ) 12 hS hSne <;>
      norm_num [hval, squareAnchorWheelProjection, primeBasisWheelProjection,
        finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis] at hsurv
  have hfirst11 : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 11 hS hSne = 6 :=
    le_antisymm hfirst11_le hfirst11_ge
  have hfirst12 : squareAnchorFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 12 hS hSne = 5 :=
    le_antisymm hfirst12_le hfirst12_ge
  have hpair11 : squareAnchorSuccessorPairPositiveFirstHit
      ({2, 3, 5} : Finset ℕ) 11 hS hSne = 5 := by
    norm_num [squareAnchorSuccessorPairPositiveFirstHit, hfirst11, hfirst12]
  have hpair_lower : 5 ≤ squareSuccessorPairPositiveFirstHitRadius
      ({2, 3, 5} : Finset ℕ) hS hSne := by
    rw [squareSuccessorPairPositiveFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ)))
      (b := 11)
      (f := fun n => squareAnchorSuccessorPairPositiveFirstHit
        ({2, 3, 5} : Finset ℕ) n hS hSne)
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    simpa [hpair11] using hle
  have hpair : squareSuccessorPairPositiveFirstHitRadius
      ({2, 3, 5} : Finset ℕ) hS hSne = 5 :=
    le_antisymm hpair_upper hpair_lower
  have hsq : squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne = 6 := by
    simpa using (squarePhasePositiveFirstHit_two_three_five_regression).2.1
  refine ⟨hsq, hpair, hpair11, hfirst11, hfirst12, ?_, ?_⟩
  · norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct]
  · norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
