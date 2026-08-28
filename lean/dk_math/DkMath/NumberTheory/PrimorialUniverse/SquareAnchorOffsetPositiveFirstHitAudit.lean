/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFirstHitAudit
import Mathlib.Tactic

/-!
# Positive-offset first-hit audit for square-anchor phases

This provider-side module removes the anchor seat `t = 0` from the finite
first-hit statistic of `SquareAnchorOffsetFirstHitAudit`.  The positive
profile searches `1 ≤ t ≤ M`, so a first positive return may be exactly one
period.  The square statistic is the restriction of the same generic profile
to square-anchor phases.

The finite comparison and the concrete regressions are an information audit;
they do not introduce a shell-width theorem, primality claim, or Legendre
consumer.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Positive generic profiles -/

/-- The one-period survivor profile with the anchor seat excluded. -/
noncomputable def genericPositiveUnreservedOffsetProfile
    (S : Finset ℕ) (A : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (finitePrimeBasisProduct S)).filter
    (fun t => IsPrimeBasisWheelSurvivor S
      ((A + t) % finitePrimeBasisProduct S))

/-- Membership records a strictly positive bounded offset and survival. -/
theorem mem_genericPositiveUnreservedOffsetProfile_iff
    {S : Finset ℕ} (A t : ℕ) :
    t ∈ genericPositiveUnreservedOffsetProfile S A ↔
      1 ≤ t ∧ t ≤ finitePrimeBasisProduct S ∧
        IsPrimeBasisWheelSurvivor S
          ((A + t) % finitePrimeBasisProduct S) := by
  simp only [genericPositiveUnreservedOffsetProfile, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hsurv⟩
    exact ⟨h₁, h₂, hsurv⟩
  · rintro ⟨h₁, h₂, hsurv⟩
    exact ⟨⟨h₁, h₂⟩, hsurv⟩

/-- Every positive generic profile is nonempty for a nonempty finite basis. -/
theorem genericPositiveUnreservedOffsetProfile_nonempty
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    (genericPositiveUnreservedOffsetProfile S A).Nonempty := by
  obtain ⟨t, ht⟩ := genericUnreservedOffsetProfile_nonempty hS hSne A
  have ht' := (mem_genericUnreservedOffsetProfile_iff A t).mp ht
  have hMgt : 1 < finitePrimeBasisProduct S :=
    one_lt_finitePrimeBasisProduct_of_nonempty hS hSne
  let u := if t = 0 then finitePrimeBasisProduct S else t
  have huIcc : 1 ≤ u ∧ u ≤ finitePrimeBasisProduct S := by
    by_cases htz : t = 0
    · simpa [u, htz] using
        (show 1 ≤ finitePrimeBasisProduct S ∧
            finitePrimeBasisProduct S ≤ finitePrimeBasisProduct S from
          ⟨by omega, le_rfl⟩)
    · have htpos : 0 < t := Nat.pos_of_ne_zero htz
      have htle : t ≤ finitePrimeBasisProduct S := Nat.le_of_lt ht'.1
      simpa [u, htz] using (show 1 ≤ t ∧ t ≤ finitePrimeBasisProduct S from
        ⟨htpos, htle⟩)
  refine ⟨u, (mem_genericPositiveUnreservedOffsetProfile_iff A u).mpr
    ⟨huIcc.1, huIcc.2, ?_⟩⟩
  by_cases htz : t = 0
  · simpa [u, htz, Nat.add_mod] using ht'.2
  · simpa [u, htz] using ht'.2

/-- The least strictly positive bounded offset to a generic survivor. -/
noncomputable def genericFirstPositiveUnreservedOffset
    (S : Finset ℕ) (A : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (genericPositiveUnreservedOffsetProfile S A).min'
    (genericPositiveUnreservedOffsetProfile_nonempty hS hSne A)

/-- The positive first hit belongs to its positive profile. -/
theorem genericFirstPositiveUnreservedOffset_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    genericFirstPositiveUnreservedOffset S A hS hSne ∈
      genericPositiveUnreservedOffsetProfile S A := by
  exact Finset.min'_mem _ _

/-- The positive first hit is strictly positive. -/
theorem genericFirstPositiveUnreservedOffset_pos
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    0 < genericFirstPositiveUnreservedOffset S A hS hSne := by
  have hmem := (mem_genericPositiveUnreservedOffsetProfile_iff A _).mp
    (genericFirstPositiveUnreservedOffset_mem hS hSne A)
  omega

/-- The positive first hit is at most one full wheel period. -/
theorem genericFirstPositiveUnreservedOffset_le_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    genericFirstPositiveUnreservedOffset S A hS hSne ≤
      finitePrimeBasisProduct S := by
  have hmem := (mem_genericPositiveUnreservedOffsetProfile_iff A _).mp
    (genericFirstPositiveUnreservedOffset_mem hS hSne A)
  exact hmem.2.1

/-- The positive first hit lands on a wheel survivor. -/
theorem genericFirstPositiveUnreservedOffset_survivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    IsPrimeBasisWheelSurvivor S
      ((A + genericFirstPositiveUnreservedOffset S A hS hSne) %
        finitePrimeBasisProduct S) := by
  have hmem := (mem_genericPositiveUnreservedOffsetProfile_iff A _).mp
    (genericFirstPositiveUnreservedOffset_mem hS hSne A)
  exact hmem.2.2

/-- Every smaller positive offset misses the generic survivor profile. -/
theorem genericFirstPositiveUnreservedOffset_minimal
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A t : ℕ)
    (htpos : 0 < t)
    (ht : t < genericFirstPositiveUnreservedOffset S A hS hSne) :
    ¬ IsPrimeBasisWheelSurvivor S
      ((A + t) % finitePrimeBasisProduct S) := by
  intro hsurv
  have htperiod := genericFirstPositiveUnreservedOffset_le_period hS hSne A
  have htm : t ∈ genericPositiveUnreservedOffsetProfile S A :=
    (mem_genericPositiveUnreservedOffsetProfile_iff A t).mpr
      ⟨by omega, by omega, hsurv⟩
  have hle := Finset.min'_le
    (genericPositiveUnreservedOffsetProfile S A) t htm
  have hle' : genericFirstPositiveUnreservedOffset S A hS hSne ≤ t := by
    simpa [genericFirstPositiveUnreservedOffset] using hle
  omega

/-! ## Square-anchor positive first hits -/

/-- The positive first hit at a square-anchor phase. -/
noncomputable def squareAnchorFirstPositiveUnreservedOffset
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  genericFirstPositiveUnreservedOffset S (squareAnchorWheelProjection S n)
    hS hSne

/-- Square-anchor and generic positive first-hit coordinates agree by phase. -/
theorem squareAnchorFirstPositiveUnreservedOffset_eq_generic
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne =
      genericFirstPositiveUnreservedOffset S (squareAnchorWheelProjection S n)
        hS hSne := by
  rfl

/-- The square-anchor positive first hit is strictly positive. -/
theorem squareAnchorFirstPositiveUnreservedOffset_pos
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    0 < squareAnchorFirstPositiveUnreservedOffset S n hS hSne := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  exact genericFirstPositiveUnreservedOffset_pos hS hSne _

/-- The square-anchor positive first hit is at most one period. -/
theorem squareAnchorFirstPositiveUnreservedOffset_le_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤
      finitePrimeBasisProduct S := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  exact genericFirstPositiveUnreservedOffset_le_period hS hSne _

/-- The square-anchor positive first hit lands on a wheel survivor. -/
theorem squareAnchorFirstPositiveUnreservedOffset_survivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    IsPrimeBasisWheelSurvivor S
      ((squareAnchorWheelProjection S n +
        squareAnchorFirstPositiveUnreservedOffset S n hS hSne) %
        finitePrimeBasisProduct S) := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  exact genericFirstPositiveUnreservedOffset_survivor hS hSne _

/-- The square-anchor positive first hit is minimal among positive offsets. -/
theorem squareAnchorFirstPositiveUnreservedOffset_minimal
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n t : ℕ)
    (htpos : 0 < t)
    (ht : t < squareAnchorFirstPositiveUnreservedOffset S n hS hSne) :
    ¬ IsPrimeBasisWheelSurvivor S
      ((squareAnchorWheelProjection S n + t) % finitePrimeBasisProduct S) := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n] at ht
  exact genericFirstPositiveUnreservedOffset_minimal hS hSne _ t htpos ht

/-- The positive first hit is unchanged by replacing an anchor with the same
square phase. -/
theorem squareAnchorFirstPositiveUnreservedOffset_eq_of_samePhase
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a b : ℕ} (hab : SameSquareAnchorPhase S a b)
    (hSne : S.Nonempty) :
    squareAnchorFirstPositiveUnreservedOffset S a hS hSne =
      squareAnchorFirstPositiveUnreservedOffset S b hS hSne := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne,
    squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne]
  exact congrArg (fun A => genericFirstPositiveUnreservedOffset S A hS hSne)
    (show squareAnchorWheelProjection S a =
      squareAnchorWheelProjection S b from hab)

/-! ## Positive first-hit radii -/

/-- Worst positive first-hit offset over all bounded cyclic labels. -/
noncomputable def genericPositiveFirstHitRadius
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).sup fun A =>
    genericFirstPositiveUnreservedOffset S A hS hSne

/-- Worst positive first-hit offset over square-reachable phase labels. -/
noncomputable def squarePositiveFirstHitRadius
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (squareAnchorReachablePhaseLabels S).sup fun A =>
    genericFirstPositiveUnreservedOffset S A hS hSne

/-- Square-reachable phases cannot have a larger positive radius. -/
theorem squarePositiveFirstHitRadius_le_genericPositiveFirstHitRadius
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) :
    squarePositiveFirstHitRadius S hS hSne ≤
      genericPositiveFirstHitRadius S hS hSne := by
  unfold squarePositiveFirstHitRadius genericPositiveFirstHitRadius
  have hMpos : 0 < finitePrimeBasisProduct S := Nat.pos_of_ne_zero
    (finitePrimeBasisProduct_ne_zero hS)
  apply Finset.sup_le
  intro A hA
  obtain ⟨n, hn, hAn⟩ :=
    (mem_squareAnchorReachablePhaseLabels_iff A).mp hA
  subst A
  exact Finset.le_sup (s := Finset.range (finitePrimeBasisProduct S))
    (f := fun A => genericFirstPositiveUnreservedOffset S A hS hSne)
    (Finset.mem_range.mpr (by
      simpa [squareAnchorWheelProjection, primeBasisWheelProjection] using
        Nat.mod_lt (n ^ 2) hMpos))

/-- Every square-anchor positive first hit is bounded by the square radius. -/
theorem squareAnchorFirstPositiveUnreservedOffset_le_squarePositiveFirstHitRadius
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstPositiveUnreservedOffset S n hS hSne ≤
      squarePositiveFirstHitRadius S hS hSne := by
  rw [squareAnchorFirstPositiveUnreservedOffset_eq_generic hS hSne n]
  apply Finset.le_sup (s := squareAnchorReachablePhaseLabels S)
    (f := fun A => genericFirstPositiveUnreservedOffset S A hS hSne)
  apply Finset.mem_image.mpr
  refine ⟨n % finitePrimeBasisProduct S, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.mod_lt _ (Nat.pos_of_ne_zero
      (finitePrimeBasisProduct_ne_zero hS))
  · simp [squareAnchorWheelProjection, primeBasisWheelProjection,
      Nat.pow_mod]

/-! ## Exact finite regressions -/

private theorem isFinitePrimeBasis_two_three_positiveFirstHit :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

private theorem isFinitePrimeBasis_two_three_five_positiveFirstHit :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

private theorem genericFirstPositiveUnreservedOffset_eq_of_lower_bound
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A k : ℕ)
    (hk : k ∈ genericPositiveUnreservedOffsetProfile S A)
    (hmin : ∀ t, t ∈ genericPositiveUnreservedOffsetProfile S A → k ≤ t) :
    genericFirstPositiveUnreservedOffset S A hS hSne = k := by
  apply le_antisymm
  · have hle := Finset.min'_le
      (genericPositiveUnreservedOffsetProfile S A) k hk
    simpa [genericFirstPositiveUnreservedOffset] using hle
  · exact Finset.le_min' (genericPositiveUnreservedOffsetProfile S A)
      (genericPositiveUnreservedOffsetProfile_nonempty hS hSne A) k hmin

private theorem genericFirstPositiveUnreservedOffset_le_of_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A k : ℕ) (hk : k ∈ genericPositiveUnreservedOffsetProfile S A) :
    genericFirstPositiveUnreservedOffset S A hS hSne ≤ k := by
  have hle := Finset.min'_le
    (genericPositiveUnreservedOffsetProfile S A) k hk
  simpa [genericFirstPositiveUnreservedOffset] using hle

/-! ### `{2, 3}` -/

/-- For `{2,3}`, both positive radii are `4`; phase `A = 1` is attained at
anchor `n = 1` and its next survivor is at offset `4`. -/
theorem squarePhasePositiveFirstHit_two_three_regression :
    genericPositiveFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_positiveFirstHit (by simp) = 4 ∧
      squarePositiveFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_positiveFirstHit (by simp) = 4 ∧
      genericFirstPositiveUnreservedOffset ({2, 3} : Finset ℕ) 1
          isFinitePrimeBasis_two_three_positiveFirstHit (by simp) = 4 ∧
      squareAnchorWheelProjection ({2, 3} : Finset ℕ) 1 = 1 := by
  have hS := isFinitePrimeBasis_two_three_positiveFirstHit
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hfirst1 : genericFirstPositiveUnreservedOffset
      ({2, 3} : Finset ℕ) 1 hS hSne = 4 := by
    apply genericFirstPositiveUnreservedOffset_eq_of_lower_bound hS hSne 1 4
    · rw [mem_genericPositiveUnreservedOffsetProfile_iff]
      norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 4 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericPositiveUnreservedOffsetProfile_iff,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have hcover : ∀ A, A < 6 →
      genericFirstPositiveUnreservedOffset ({2, 3} : Finset ℕ) A hS hSne ≤ 4 := by
    intro A hA
    have hwithin : ∃ t, t ≤ 4 ∧
        t ∈ genericPositiveUnreservedOffsetProfile ({2, 3} : Finset ℕ) A := by
      interval_cases A <;>
        first
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
             ReservedByPrimeBasis])
    obtain ⟨t, ht, htm⟩ := hwithin
    exact (genericFirstPositiveUnreservedOffset_le_of_mem hS hSne A t htm).trans ht
  have hgeneric_upper : genericPositiveFirstHitRadius ({2, 3} : Finset ℕ)
      hS hSne ≤ 4 := by
    unfold genericPositiveFirstHitRadius
    apply Finset.sup_le
    intro A hA
    exact hcover A (Finset.mem_range.mp hA)
  have hgeneric_lower : 4 ≤ genericPositiveFirstHitRadius
      ({2, 3} : Finset ℕ) hS hSne := by
    rw [genericPositiveFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3} : Finset ℕ)))
      (b := 1)
      (f := fun A => genericFirstPositiveUnreservedOffset
        ({2, 3} : Finset ℕ) A hS hSne)
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    simpa [hfirst1] using hle
  have hgeneric : genericPositiveFirstHitRadius ({2, 3} : Finset ℕ) hS hSne = 4 :=
    le_antisymm hgeneric_upper hgeneric_lower
  have hsq_upper : squarePositiveFirstHitRadius ({2, 3} : Finset ℕ)
      hS hSne ≤ 4 := by
    unfold squarePositiveFirstHitRadius
    apply Finset.sup_le
    intro A hA
    obtain ⟨n, hn, rfl⟩ :=
      (mem_squareAnchorReachablePhaseLabels_iff
        (S := ({2, 3} : Finset ℕ)) A).mp hA
    apply hcover
    simpa [squareAnchorWheelProjection, primeBasisWheelProjection,
      finitePrimeBasisProduct] using
      Nat.mod_lt (n ^ 2) (by norm_num [finitePrimeBasisProduct])
  have hsq_lower : 4 ≤ squarePositiveFirstHitRadius ({2, 3} : Finset ℕ)
      hS hSne := by
    have hle := Finset.le_sup
      (s := squareAnchorReachablePhaseLabels ({2, 3} : Finset ℕ))
      (b := 1)
      (f := fun A => genericFirstPositiveUnreservedOffset
        ({2, 3} : Finset ℕ) A hS hSne)
      (Finset.mem_image.mpr ⟨1, by norm_num [finitePrimeBasisProduct], by
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]⟩)
    calc
      4 = genericFirstPositiveUnreservedOffset ({2, 3} : Finset ℕ) 1 hS hSne :=
        hfirst1.symm
      _ ≤ squarePositiveFirstHitRadius ({2, 3} : Finset ℕ) hS hSne := hle
  refine ⟨hgeneric, le_antisymm hsq_upper hsq_lower, hfirst1, ?_⟩
  norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

/-! ### `{2, 3, 5}` -/

/-- For `{2,3,5}`, both positive radii are `6`; phase `A = 1` is attained at
anchor `n = 1` and its next survivor is `7`. -/
theorem squarePhasePositiveFirstHit_two_three_five_regression :
    genericPositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_positiveFirstHit (by simp) = 6 ∧
      squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_positiveFirstHit (by simp) = 6 ∧
      genericFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 1
          isFinitePrimeBasis_two_three_five_positiveFirstHit (by simp) = 6 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 1 = 1 := by
  have hS := isFinitePrimeBasis_two_three_five_positiveFirstHit
  have hSne : ({2, 3, 5} : Finset ℕ).Nonempty := by simp
  have hfirst1 : genericFirstPositiveUnreservedOffset
      ({2, 3, 5} : Finset ℕ) 1 hS hSne = 6 := by
    apply genericFirstPositiveUnreservedOffset_eq_of_lower_bound hS hSne 1 6
    · rw [mem_genericPositiveUnreservedOffsetProfile_iff]
      norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 6 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericPositiveUnreservedOffsetProfile_iff,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have hcover : ∀ A, A < 30 →
      genericFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) A hS hSne ≤ 6 := by
    intro A hA
    have hwithin : ∃ t, t ≤ 6 ∧
        t ∈ genericPositiveUnreservedOffsetProfile ({2, 3, 5} : Finset ℕ) A := by
      interval_cases A <;>
        first
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
             ReservedByPrimeBasis]
           done)
        | (refine ⟨6, by norm_num, ?_⟩
           rw [mem_genericPositiveUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis])
    obtain ⟨t, ht, htm⟩ := hwithin
    exact (genericFirstPositiveUnreservedOffset_le_of_mem hS hSne A t htm).trans ht
  have hgeneric_upper : genericPositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
      hS hSne ≤ 6 := by
    unfold genericPositiveFirstHitRadius
    apply Finset.sup_le
    intro A hA
    exact hcover A (Finset.mem_range.mp hA)
  have hgeneric_lower : 6 ≤ genericPositiveFirstHitRadius
      ({2, 3, 5} : Finset ℕ) hS hSne := by
    rw [genericPositiveFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ)))
      (b := 1)
      (f := fun A => genericFirstPositiveUnreservedOffset
        ({2, 3, 5} : Finset ℕ) A hS hSne)
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    simpa [hfirst1] using hle
  have hgeneric : genericPositiveFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne = 6 :=
    le_antisymm hgeneric_upper hgeneric_lower
  have hsq_upper : squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
      hS hSne ≤ 6 := by
    unfold squarePositiveFirstHitRadius
    apply Finset.sup_le
    intro A hA
    obtain ⟨n, hn, rfl⟩ :=
      (mem_squareAnchorReachablePhaseLabels_iff
        (S := ({2, 3, 5} : Finset ℕ)) A).mp hA
    apply hcover
    exact Nat.mod_lt _ (by norm_num [finitePrimeBasisProduct])
  have hsq_lower : 6 ≤ squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ)
      hS hSne := by
    have hle := Finset.le_sup
      (s := squareAnchorReachablePhaseLabels ({2, 3, 5} : Finset ℕ))
      (b := 1)
      (f := fun A => genericFirstPositiveUnreservedOffset
        ({2, 3, 5} : Finset ℕ) A hS hSne)
      (Finset.mem_image.mpr ⟨1, by norm_num [finitePrimeBasisProduct], by
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]⟩)
    calc
      6 = genericFirstPositiveUnreservedOffset ({2, 3, 5} : Finset ℕ) 1 hS hSne :=
        hfirst1.symm
      _ ≤ squarePositiveFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne := hle
  refine ⟨hgeneric, le_antisymm hsq_upper hsq_lower, hfirst1, ?_⟩
  norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
