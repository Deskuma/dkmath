/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetProfile
import Mathlib.Tactic

/-!
# First-hit audit for square-phase translations

This provider-side module compares arbitrary cyclic shifts of a finite wheel
with the shifts reached by square anchors.  It defines first unreserved
offsets and the two corresponding finite worst-case radii.  The result is an
information audit only: square phases can improve the radius for some bases,
but the comparison is not uniformly strict and does not imply a short-shell
escape, a gap bound, primality, or an analytic theorem.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Generic shifted profiles -/

/-- The one-period survivor profile for an arbitrary wheel label `A`. -/
noncomputable def genericUnreservedOffsetProfile
    (S : Finset ℕ) (A : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (finitePrimeBasisProduct S)).filter
    (fun t => IsPrimeBasisWheelSurvivor S
      ((A + t) % finitePrimeBasisProduct S))

/-- Membership in a generic profile is boundedness plus translated survival. -/
theorem mem_genericUnreservedOffsetProfile_iff
    {S : Finset ℕ} (A t : ℕ) :
    t ∈ genericUnreservedOffsetProfile S A ↔
      t < finitePrimeBasisProduct S ∧
        IsPrimeBasisWheelSurvivor S
          ((A + t) % finitePrimeBasisProduct S) := by
  simp [genericUnreservedOffsetProfile]

/-- The square-shell profile is the generic profile at its square phase. -/
theorem squareAnchorUnreservedOffsetProfile_eq_generic
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorUnreservedOffsetProfile S n =
      genericUnreservedOffsetProfile S (squareAnchorWheelProjection S n) := by
  ext t
  rw [squareAnchorUnreservedOffsetProfile_mem_iff_translated_survivor
    hS hSne, mem_genericUnreservedOffsetProfile_iff]

/-! ## Profile nonemptiness and first-hit coordinates -/

private theorem one_mem_primeBasisWheelSurvivors_of_nonempty
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) :
    1 ∈ primeBasisWheelSurvivors S := by
  rw [mem_primeBasisWheelSurvivors_iff]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact (one_lt_finitePrimeBasisProduct_of_nonempty hS hSne).trans_le
      (Nat.le_refl _)
  · rintro ⟨p, hp, hpone⟩
    exact (hS p hp).ne_one (Nat.dvd_one.mp hpone)

private theorem add_mod_inverse_eq
    {M A s : ℕ} (hAlt : A < M) (hslt : s < M) :
    (A + (s + (M - A)) % M) % M = s := by
  have hAle : A ≤ M := Nat.le_of_lt hAlt
  have hmod₁ : Nat.ModEq M ((s + (M - A)) % M) (s + (M - A)) :=
    Nat.mod_modEq _ _
  have hmod₂ : Nat.ModEq M
      (A + ((s + (M - A)) % M)) (A + (s + (M - A))) :=
    hmod₁.add_left A
  have hmod₃ : Nat.ModEq M (A + (s + (M - A))) s := by
    rw [show A + (s + (M - A)) = s + M by omega]
    simp [Nat.ModEq]
  have hmod := hmod₂.trans hmod₃
  change (A + ((s + (M - A)) % M)) % M = s % M at hmod
  simpa [Nat.mod_eq_of_lt hslt] using hmod

/-- Every generic profile is nonempty for a nonempty finite prime basis. -/
theorem genericUnreservedOffsetProfile_nonempty
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) : (genericUnreservedOffsetProfile S A).Nonempty := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hMgt : 1 < finitePrimeBasisProduct S :=
    one_lt_finitePrimeBasisProduct_of_nonempty hS hSne
  let B := A % finitePrimeBasisProduct S
  let t := (1 + (finitePrimeBasisProduct S - B)) %
    finitePrimeBasisProduct S
  have hBlt : B < finitePrimeBasisProduct S := by
    exact Nat.mod_lt _ hMpos
  have htlt : t < finitePrimeBasisProduct S := by
    exact Nat.mod_lt _ hMpos
  have hcoordB : (B + t) % finitePrimeBasisProduct S = 1 := by
    dsimp [t]
    exact add_mod_inverse_eq hBlt hMgt
  have hcoord : (A + t) % finitePrimeBasisProduct S = 1 := by
    dsimp [B] at hcoordB ⊢
    simpa [Nat.add_mod] using hcoordB
  refine ⟨t, (mem_genericUnreservedOffsetProfile_iff A t).mpr ?_⟩
  exact ⟨htlt, by rw [hcoord]; exact
    (mem_primeBasisWheelSurvivors_iff.mp
      (one_mem_primeBasisWheelSurvivors_of_nonempty hS hSne))⟩

/-- The least bounded offset in a generic shifted profile. -/
noncomputable def genericFirstUnreservedOffset
    (S : Finset ℕ) (A : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (genericUnreservedOffsetProfile S A).min'
    (genericUnreservedOffsetProfile_nonempty hS hSne A)

/-- The first generic offset belongs to its profile. -/
theorem genericFirstUnreservedOffset_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    genericFirstUnreservedOffset S A hS hSne ∈
      genericUnreservedOffsetProfile S A := by
  exact Finset.min'_mem _ _

/-- The first generic offset is inside one wheel period. -/
theorem genericFirstUnreservedOffset_lt
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A : ℕ) :
    genericFirstUnreservedOffset S A hS hSne <
      finitePrimeBasisProduct S := by
  exact (mem_genericUnreservedOffsetProfile_iff A _).mp
    (genericFirstUnreservedOffset_mem hS hSne A) |>.1

/-- Every smaller offset is absent from the generic profile. -/
theorem genericFirstUnreservedOffset_minimal
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A t : ℕ)
    (ht : t < genericFirstUnreservedOffset S A hS hSne) :
    t ∉ genericUnreservedOffsetProfile S A := by
  intro htm
  have hle := Finset.min'_le (genericUnreservedOffsetProfile S A) t htm
  have hle' : genericFirstUnreservedOffset S A hS hSne ≤ t := by
    simpa [genericFirstUnreservedOffset] using hle
  omega

/-- The least bounded offset in the square-anchor profile. -/
noncomputable def squareAnchorFirstUnreservedOffset
    (S : Finset ℕ) (n : ℕ)
    (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  genericFirstUnreservedOffset S (squareAnchorWheelProjection S n) hS hSne

/-- Square and generic first-hit coordinates agree at the square phase. -/
theorem squareAnchorFirstUnreservedOffset_eq_generic
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstUnreservedOffset S n hS hSne =
      genericFirstUnreservedOffset S (squareAnchorWheelProjection S n)
        hS hSne := by
  rfl

/-- The square first hit belongs to the square-anchor profile. -/
theorem squareAnchorFirstUnreservedOffset_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstUnreservedOffset S n hS hSne ∈
      squareAnchorUnreservedOffsetProfile S n := by
  rw [squareAnchorUnreservedOffsetProfile_eq_generic hS hSne n]
  exact genericFirstUnreservedOffset_mem hS hSne _

/-- The square first hit lies inside one old-wheel period. -/
theorem squareAnchorFirstUnreservedOffset_lt
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstUnreservedOffset S n hS hSne <
      finitePrimeBasisProduct S := by
  rw [squareAnchorFirstUnreservedOffset_eq_generic hS hSne n]
  exact genericFirstUnreservedOffset_lt hS hSne _

/-- Same square phase gives the same first-hit coordinate. -/
theorem squareAnchorFirstUnreservedOffset_eq_of_samePhase
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a b : ℕ} (hab : SameSquareAnchorPhase S a b)
    (hSne : S.Nonempty) :
    squareAnchorFirstUnreservedOffset S a hS hSne =
      squareAnchorFirstUnreservedOffset S b hS hSne := by
  rw [squareAnchorFirstUnreservedOffset_eq_generic hS hSne,
    squareAnchorFirstUnreservedOffset_eq_generic hS hSne]
  exact congrArg (fun A => genericFirstUnreservedOffset S A hS hSne)
    (show squareAnchorWheelProjection S a =
      squareAnchorWheelProjection S b from hab)

/-! ## Reachable square labels and worst-case radii -/

/-- Square-value labels reached by anchors in one old period. -/
noncomputable def squareAnchorReachablePhaseLabels
    (S : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (finitePrimeBasisProduct S)).image
    (squareAnchorWheelProjection S)

/-- A label is reachable exactly when a bounded anchor realizes it. -/
theorem mem_squareAnchorReachablePhaseLabels_iff
    {S : Finset ℕ} (A : ℕ) :
    A ∈ squareAnchorReachablePhaseLabels S ↔
      ∃ n < finitePrimeBasisProduct S,
        squareAnchorWheelProjection S n = A := by
  simp [squareAnchorReachablePhaseLabels]

/-- Worst first-hit offset over all bounded cyclic labels. -/
noncomputable def genericFirstHitRadius
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).sup fun A =>
    genericFirstUnreservedOffset S A hS hSne

/-- Worst first-hit offset over reachable square-phase labels. -/
noncomputable def squareFirstHitRadius
    (S : Finset ℕ) (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) : ℕ :=
  (squareAnchorReachablePhaseLabels S).sup fun A =>
    genericFirstUnreservedOffset S A hS hSne

/-- Square-reachable phases cannot have a larger worst first hit than arbitrary
cyclic labels. -/
theorem squareFirstHitRadius_le_genericFirstHitRadius
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty) :
    squareFirstHitRadius S hS hSne ≤ genericFirstHitRadius S hS hSne := by
  unfold squareFirstHitRadius genericFirstHitRadius
  have hMpos : 0 < finitePrimeBasisProduct S := Nat.pos_of_ne_zero
    (finitePrimeBasisProduct_ne_zero hS)
  apply Finset.sup_le
  intro A hA
  obtain ⟨n, hn, hAn⟩ :=
    (mem_squareAnchorReachablePhaseLabels_iff A).mp hA
  subst A
  exact Finset.le_sup (s := Finset.range (finitePrimeBasisProduct S))
    (f := fun A => genericFirstUnreservedOffset S A hS hSne)
    (Finset.mem_range.mpr (by
      simpa [squareAnchorWheelProjection, primeBasisWheelProjection] using
        Nat.mod_lt (n ^ 2) hMpos))

/-- Every square-anchor first hit is bounded by the square-restricted radius. -/
theorem squareAnchorFirstUnreservedOffset_le_squareFirstHitRadius
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    squareAnchorFirstUnreservedOffset S n hS hSne ≤
      squareFirstHitRadius S hS hSne := by
  rw [squareAnchorFirstUnreservedOffset_eq_generic hS hSne n]
  apply Finset.le_sup (s := squareAnchorReachablePhaseLabels S)
    (f := fun A => genericFirstUnreservedOffset S A hS hSne)
  apply Finset.mem_image.mpr
  refine ⟨n % finitePrimeBasisProduct S, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.mod_lt _ (Nat.pos_of_ne_zero
      (finitePrimeBasisProduct_ne_zero hS))
  · simp [squareAnchorWheelProjection, primeBasisWheelProjection,
      Nat.pow_mod]

private theorem genericFirstUnreservedOffset_eq_of_lower_bound
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A k : ℕ)
    (hk : k ∈ genericUnreservedOffsetProfile S A)
    (hmin : ∀ t, t ∈ genericUnreservedOffsetProfile S A → k ≤ t) :
    genericFirstUnreservedOffset S A hS hSne = k := by
  apply le_antisymm
  · have hle := Finset.min'_le (genericUnreservedOffsetProfile S A) k hk
    simpa [genericFirstUnreservedOffset] using hle
  · exact Finset.le_min' (genericUnreservedOffsetProfile S A)
      (genericUnreservedOffsetProfile_nonempty hS hSne A) k hmin

private theorem genericFirstUnreservedOffset_le_of_mem
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (A k : ℕ) (hk : k ∈ genericUnreservedOffsetProfile S A) :
    genericFirstUnreservedOffset S A hS hSne ≤ k := by
  have hle := Finset.min'_le (genericUnreservedOffsetProfile S A) k hk
  simpa [genericFirstUnreservedOffset] using hle

/-! ## Exact finite regressions -/

private theorem isFinitePrimeBasis_two_three_firstHit :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

private theorem isFinitePrimeBasis_two_three_five_firstHit :
    IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- For `{2,3}`, arbitrary shifts have radius `3`, while square phases have
radius `2`; label `A = 2` witnesses the arbitrary-shift worst case. -/
theorem squarePhaseFirstHit_two_three_regression :
    genericFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_firstHit (by simp) = 3 ∧
      squareFirstHitRadius ({2, 3} : Finset ℕ)
        isFinitePrimeBasis_two_three_firstHit (by simp) = 2 ∧
      genericFirstUnreservedOffset ({2, 3} : Finset ℕ) 2
          isFinitePrimeBasis_two_three_firstHit (by simp) = 3 := by
  have hS := isFinitePrimeBasis_two_three_firstHit
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hfirst2 : genericFirstUnreservedOffset ({2, 3} : Finset ℕ) 2 hS hSne = 3 := by
    apply genericFirstUnreservedOffset_eq_of_lower_bound hS hSne 2 3
    · rw [mem_genericUnreservedOffsetProfile_iff]
      norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 3 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericUnreservedOffsetProfile_iff,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have hgeneric_upper : genericFirstHitRadius ({2, 3} : Finset ℕ) hS hSne ≤ 3 := by
    unfold genericFirstHitRadius
    apply Finset.sup_le
    intro A hA
    have hAlt : A < 6 := Finset.mem_range.mp hA
    interval_cases A
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne 0 1 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne 1 0 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis])).trans (by norm_num)
    · exact hfirst2.le
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne 3 2 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne 4 1 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne 5 0 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis])).trans (by norm_num)
  have hgeneric_lower : 3 ≤ genericFirstHitRadius ({2, 3} : Finset ℕ) hS hSne := by
    rw [genericFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3} : Finset ℕ)))
      (b := 2)
      (f := fun A => genericFirstUnreservedOffset ({2, 3} : Finset ℕ) A hS hSne)
      (Finset.mem_range.mpr (by
        norm_num [finitePrimeBasisProduct]))
    simpa [hfirst2] using hle
  have hgeneric : genericFirstHitRadius ({2, 3} : Finset ℕ) hS hSne = 3 :=
    le_antisymm hgeneric_upper hgeneric_lower
  have hsq_lower : 2 ≤ squareFirstHitRadius ({2, 3} : Finset ℕ) hS hSne := by
    have hfirst3 : genericFirstUnreservedOffset ({2, 3} : Finset ℕ) 3 hS hSne = 2 := by
      apply genericFirstUnreservedOffset_eq_of_lower_bound hS hSne 3 2
      · rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis]
      · intro t ht
        by_contra hnot
        have hlt : t < 2 := Nat.lt_of_not_ge hnot
        interval_cases t <;>
          norm_num [mem_genericUnreservedOffsetProfile_iff,
            finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
            ReservedByPrimeBasis] at ht
    have hle := Finset.le_sup
      (s := squareAnchorReachablePhaseLabels ({2, 3} : Finset ℕ))
      (b := 3)
      (f := fun A => genericFirstUnreservedOffset ({2, 3} : Finset ℕ) A hS hSne)
      (Finset.mem_image.mpr ⟨3, by norm_num [finitePrimeBasisProduct], by
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]⟩)
    calc
      2 = genericFirstUnreservedOffset ({2, 3} : Finset ℕ) 3 hS hSne := hfirst3.symm
      _ ≤ squareFirstHitRadius ({2, 3} : Finset ℕ) hS hSne := hle
  have hsq_upper : squareFirstHitRadius ({2, 3} : Finset ℕ) hS hSne ≤ 2 := by
    unfold squareFirstHitRadius
    apply Finset.sup_le
    intro A hA
    obtain ⟨n, hn, rfl⟩ := (mem_squareAnchorReachablePhaseLabels_iff A).mp hA
    have hn' : n < 6 := by simpa [finitePrimeBasisProduct] using hn
    interval_cases n
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 1 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 0 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 1 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 2 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 1 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
    · exact (genericFirstUnreservedOffset_le_of_mem hS hSne _ 0 (by
        rw [mem_genericUnreservedOffsetProfile_iff]
        norm_num [finitePrimeBasisProduct, squareAnchorWheelProjection,
          primeBasisWheelProjection, IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis])).trans (by norm_num)
  refine ⟨hgeneric, le_antisymm hsq_upper hsq_lower, hfirst2⟩

/-- For `{2,3,5}`, the square-restricted radius reaches the generic radius;
the reachable label `24 = 12^2 mod 30` has first hit `5`. -/
theorem squarePhaseFirstHit_two_three_five_regression :
    genericFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_firstHit (by simp) = 5 ∧
      squareFirstHitRadius ({2, 3, 5} : Finset ℕ)
        isFinitePrimeBasis_two_three_five_firstHit (by simp) = 5 ∧
      genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) 24
          isFinitePrimeBasis_two_three_five_firstHit (by simp) = 5 ∧
      squareAnchorWheelProjection ({2, 3, 5} : Finset ℕ) 12 = 24 := by
  have hS := isFinitePrimeBasis_two_three_five_firstHit
  have hSne : ({2, 3, 5} : Finset ℕ).Nonempty := by simp
  have hfirst24 : genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) 24 hS hSne = 5 := by
    apply genericFirstUnreservedOffset_eq_of_lower_bound hS hSne 24 5
    · rw [mem_genericUnreservedOffsetProfile_iff]
      norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
        ReservedByPrimeBasis]
    · intro t ht
      by_contra hnot
      have hlt : t < 5 := Nat.lt_of_not_ge hnot
      interval_cases t <;>
        norm_num [mem_genericUnreservedOffsetProfile_iff,
          finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
          ReservedByPrimeBasis] at ht
  have hcover : ∀ A, A < 30 →
      genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) A hS hSne ≤ 5 := by
    intro A hA
    have hwithin : ∃ t, t ≤ 5 ∧
        t ∈ genericUnreservedOffsetProfile ({2, 3, 5} : Finset ℕ) A := by
      interval_cases A <;>
        first
        | (refine ⟨0, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨1, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨2, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨3, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨4, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis]
           done)
        | (refine ⟨5, by norm_num, ?_⟩
           rw [mem_genericUnreservedOffsetProfile_iff]
           norm_num [finitePrimeBasisProduct, IsPrimeBasisWheelSurvivor,
             ReservedByPrimeBasis])
    obtain ⟨t, ht, htm⟩ := hwithin
    exact (genericFirstUnreservedOffset_le_of_mem hS hSne A t htm).trans ht
  have hgeneric_upper : genericFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne ≤ 5 := by
    unfold genericFirstHitRadius
    apply Finset.sup_le
    intro A hA
    exact hcover A (Finset.mem_range.mp hA)
  have hgeneric_lower : 5 ≤ genericFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne := by
    rw [genericFirstHitRadius]
    have hle := Finset.le_sup
      (s := Finset.range (finitePrimeBasisProduct ({2, 3, 5} : Finset ℕ)))
      (b := 24)
      (f := fun A => genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) A hS hSne)
      (Finset.mem_range.mpr (by norm_num [finitePrimeBasisProduct]))
    calc
      5 = genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) 24 hS hSne := hfirst24.symm
      _ ≤ genericFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne := hle
  have hgeneric : genericFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne = 5 :=
    le_antisymm hgeneric_upper hgeneric_lower
  have hsq_upper : squareFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne ≤ 5 := by
    unfold squareFirstHitRadius
    apply Finset.sup_le
    intro A hA
    obtain ⟨n, hn, rfl⟩ := (mem_squareAnchorReachablePhaseLabels_iff A).mp hA
    apply hcover
    exact (Nat.mod_lt _ (by norm_num [finitePrimeBasisProduct]))
  have hsq_lower : 5 ≤ squareFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne := by
    have hle := Finset.le_sup
      (s := squareAnchorReachablePhaseLabels ({2, 3, 5} : Finset ℕ))
      (b := 24)
      (f := fun A => genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) A hS hSne)
      (Finset.mem_image.mpr ⟨12, by norm_num [finitePrimeBasisProduct], by
        norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
          finitePrimeBasisProduct]⟩)
    calc
      5 = genericFirstUnreservedOffset ({2, 3, 5} : Finset ℕ) 24 hS hSne := hfirst24.symm
      _ ≤ squareFirstHitRadius ({2, 3, 5} : Finset ℕ) hS hSne := hle
  refine ⟨hgeneric, le_antisymm hsq_upper hsq_lower, hfirst24, ?_⟩
  norm_num [squareAnchorWheelProjection, primeBasisWheelProjection,
    finitePrimeBasisProduct]

end DkMath.NumberTheory.PrimorialUniverse
