/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixAudit
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase

/-!
# Square-anchor unreserved offset profiles

This module packages the unreserved offsets in one old-wheel period above a
square anchor.  The profile is a translated copy of the fixed one-period
wheel-survivor set.  Its cardinality, same-phase invariance, and successor
transport are finite cyclic facts only; no offset bound, escape statement,
gap theorem, primality conclusion, or analytic consequence is introduced.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## The profile and its public membership forms -/

/-- The one-period offsets not reserved above the square anchor `n^2`. -/
noncomputable def squareAnchorUnreservedOffsetProfile
    (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (finitePrimeBasisProduct S)).filter
      (fun t => ¬ ReservedByPrimeBasis S (n ^ 2 + t))

/-- Membership in the profile is exactly bounded non-reservation. -/
theorem mem_squareAnchorUnreservedOffsetProfile_iff
    {S : Finset ℕ} (n t : ℕ) :
    t ∈ squareAnchorUnreservedOffsetProfile S n ↔
      t < finitePrimeBasisProduct S ∧
        ¬ ReservedByPrimeBasis S (n ^ 2 + t) := by
  simp [squareAnchorUnreservedOffsetProfile]

/-- For a nonempty finite basis, profile membership is translated survivor
membership on the old wheel. -/
theorem mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n t : ℕ) :
    t ∈ squareAnchorUnreservedOffsetProfile S n ↔
      t < finitePrimeBasisProduct S ∧
        IsPrimeBasisWheelSurvivor S
          ((squareAnchorWheelProjection S n + t) %
            finitePrimeBasisProduct S) := by
  rw [mem_squareAnchorUnreservedOffsetProfile_iff]
  rw [squareShell_not_reserved_iff_projection_survivor hS hSne]
  rw [squareShellWheelProjection_eq_anchor_add hS]

/-- The translated-survivor statement under the checkpoint-facing name. -/
theorem squareAnchorUnreservedOffsetProfile_mem_iff_translated_survivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n t : ℕ) :
    t ∈ squareAnchorUnreservedOffsetProfile S n ↔
      t < finitePrimeBasisProduct S ∧
        IsPrimeBasisWheelSurvivor S
          ((squareAnchorWheelProjection S n + t) %
            finitePrimeBasisProduct S) :=
  mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor hS hSne n t

/-! ## Translation and cardinality -/

/-- The profile is the fixed survivor set translated by the square-anchor
coordinate. -/
theorem mem_squareAnchorUnreservedOffsetProfile_iff_survivor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n t : ℕ) :
    t ∈ squareAnchorUnreservedOffsetProfile S n ↔
      t < finitePrimeBasisProduct S ∧
        (squareAnchorWheelProjection S n + t) %
            finitePrimeBasisProduct S ∈ primeBasisWheelSurvivors S := by
  rw [mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor hS hSne]
  rw [mem_primeBasisWheelSurvivors_iff]

private theorem squareAnchorUnreservedOffsetProfile_card_aux
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    (squareAnchorUnreservedOffsetProfile S n).card =
      (primeBasisWheelSurvivors S).card := by
  classical
  let M := finitePrimeBasisProduct S
  let A := squareAnchorWheelProjection S n
  have hMpos : 0 < M := Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hA : A < M := by
    dsimp [A]
    exact Nat.mod_lt _ hMpos
  apply Finset.card_bij (fun t _ => (A + t) % M)
  · intro t ht
    have ht' := (mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor
      hS hSne n t).mp ht
    simpa [M, A] using (mem_primeBasisWheelSurvivors_iff.mpr ht'.2)
  · intro t₁ ht₁ t₂ ht₂ heq
    have hmod : Nat.ModEq M (A + t₁) (A + t₂) := by
      simpa [Nat.ModEq] using heq
    have hmod' : Nat.ModEq M t₁ t₂ :=
      Nat.ModEq.rfl.add_left_cancel hmod
    have ht₁lt : t₁ < M :=
      (mem_squareAnchorUnreservedOffsetProfile_iff n t₁).mp ht₁ |>.1
    have ht₂lt : t₂ < M :=
      (mem_squareAnchorUnreservedOffsetProfile_iff n t₂).mp ht₂ |>.1
    exact hmod'.eq_of_lt_of_lt ht₁lt ht₂lt
  · intro s hs
    have hs' : IsPrimeBasisWheelSurvivor S s :=
      mem_primeBasisWheelSurvivors_iff.mp hs
    have hslt : s < M := hs'.2.1
    let t := (s + (M - A)) % M
    have htlt : t < M := Nat.mod_lt _ hMpos
    have hsum : (A + t) % M = s := by
      have hAle : A ≤ M := Nat.le_of_lt hA
      have hmod₁ : Nat.ModEq M t (s + (M - A)) := by
        dsimp [t]
        exact Nat.mod_modEq _ _
      have hmod₂ : Nat.ModEq M (A + t) (A + (s + (M - A))) :=
        hmod₁.add_left A
      have hmod₃ : Nat.ModEq M (A + (s + (M - A))) s := by
        have hsub : A + (M - A) = M := Nat.add_sub_of_le hAle
        rw [show A + (s + (M - A)) = s + M by omega]
        simp [Nat.ModEq]
      have hmod := hmod₂.trans hmod₃
      change (A + t) % M = s % M at hmod
      simpa [Nat.mod_eq_of_lt hslt] using hmod
    refine ⟨t, ?_, hsum⟩
    exact (mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor
      hS hSne n t).mpr ⟨htlt, by rw [hsum]; exact hs'⟩

/-- Every nonempty finite basis has the same number of profile offsets as its
one-period wheel survivors. -/
theorem card_squareAnchorUnreservedOffsetProfile
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    (n : ℕ) :
    (squareAnchorUnreservedOffsetProfile S n).card =
      (primeBasisWheelSurvivors S).card :=
  squareAnchorUnreservedOffsetProfile_card_aux hS hSne n

/-! ## Same phase and successor transport -/

/-- Same square phase gives the same unreserved offset profile. -/
theorem squareAnchorUnreservedOffsetProfile_eq_of_sameAnchorPhase
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a b : ℕ} (hab : SameSquareAnchorPhase S a b) :
    squareAnchorUnreservedOffsetProfile S a =
      squareAnchorUnreservedOffsetProfile S b := by
  ext t
  rw [mem_squareAnchorUnreservedOffsetProfile_iff,
    mem_squareAnchorUnreservedOffsetProfile_iff]
  exact ⟨fun ht => ⟨ht.1,
    (not_reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase hS hab t).mp ht.2⟩,
    fun ht => ⟨ht.1,
    (not_reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase hS hab t).mpr ht.2⟩⟩

/-- Same-phase profile equality under the shorter checkpoint-facing name. -/
theorem squareAnchorUnreservedOffsetProfile_eq_of_samePhase
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a b : ℕ} (hab : SameSquareAnchorPhase S a b) :
    squareAnchorUnreservedOffsetProfile S a =
      squareAnchorUnreservedOffsetProfile S b :=
  squareAnchorUnreservedOffsetProfile_eq_of_sameAnchorPhase hS hab

/-- One square step translates profile offsets by the odd increment, with the
orientation shown explicitly by the regression below. -/
theorem mem_squareAnchorUnreservedOffsetProfile_succ_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {n t : ℕ} (ht : t < finitePrimeBasisProduct S) :
    t ∈ squareAnchorUnreservedOffsetProfile S (n + 1) ↔
      (t + (2 * n + 1)) % finitePrimeBasisProduct S ∈
        squareAnchorUnreservedOffsetProfile S n := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  let M := finitePrimeBasisProduct S
  let A₀ := squareAnchorWheelProjection S n
  let d := 2 * n + 1
  have hcoord :
      (squareAnchorWheelProjection S (n + 1) + t) % M =
        (squareAnchorWheelProjection S n + (t + d) % M) % M := by
    have hstep : squareAnchorWheelProjection S (n + 1) =
        (A₀ + d) % M := by
      simpa [A₀, d, M] using squareAnchorWheelProjection_succ hS n
    have h₁ : Nat.ModEq M
        (squareAnchorWheelProjection S (n + 1)) (A₀ + d) := by
      rw [hstep]
      exact Nat.mod_modEq _ _
    have h₂ := h₁.add_right t
    have h₃ : Nat.ModEq M (A₀ + d + t)
        (A₀ + (t + d) % M) := by
      have hmod := (Nat.mod_modEq (t + d) M).add_left A₀
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmod.symm
    have htotal : Nat.ModEq M
        (squareAnchorWheelProjection S (n + 1) + t)
        (A₀ + (t + d) % M) := h₂.trans h₃
    change (squareAnchorWheelProjection S (n + 1) + t) % M =
      (squareAnchorWheelProjection S n + (t + d) % M) % M
    exact htotal
  rw [mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor hS hSne,
    mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor hS hSne]
  constructor
  · rintro ⟨ht, hsurv⟩
    refine ⟨Nat.mod_lt _ hMpos, ?_⟩
    rw [hcoord] at hsurv
    exact hsurv
  · rintro ⟨_hu, hsurv⟩
    refine ⟨ht, ?_⟩
    rw [hcoord]
    exact hsurv

/-- Successor profile transport under the checkpoint-facing name. -/
theorem squareAnchorUnreservedOffsetProfile_succ_transport
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (hSne : S.Nonempty)
    {n t : ℕ} (ht : t < finitePrimeBasisProduct S) :
    t ∈ squareAnchorUnreservedOffsetProfile S (n + 1) ↔
      (t + (2 * n + 1)) % finitePrimeBasisProduct S ∈
        squareAnchorUnreservedOffsetProfile S n :=
  mem_squareAnchorUnreservedOffsetProfile_succ_iff hS hSne ht

/-! ## Visible `{2, 3}` regression -/

private theorem isFinitePrimeBasis_two_three_offsetProfile :
    IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- For `S = {2,3}`, phases `1` and `5` agree, phase `2` differs, and the
successor transport uses the forward increment `t ↦ t + 3 (mod 6)`. -/
theorem squareAnchorUnreservedOffsetProfile_two_three_regression :
    squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 1 =
        squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 5 ∧
      squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 1 ≠
        squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 2 ∧
      (∀ t, t < 6 → (t ∈ squareAnchorUnreservedOffsetProfile
          ({2, 3} : Finset ℕ) 2 ↔
        (t + 3) % 6 ∈ squareAnchorUnreservedOffsetProfile
          ({2, 3} : Finset ℕ) 1)) := by
  have hS := isFinitePrimeBasis_two_three_offsetProfile
  have hM : finitePrimeBasisProduct ({2, 3} : Finset ℕ) = 6 := by decide
  have hphase : SameSquareAnchorPhase ({2, 3} : Finset ℕ) 1 5 := by
    norm_num [SameSquareAnchorPhase, squareAnchorWheelProjection,
      primeBasisWheelProjection, hM]
  have hphase_ne : ¬ SameSquareAnchorPhase ({2, 3} : Finset ℕ) 1 2 := by
    norm_num [SameSquareAnchorPhase, squareAnchorWheelProjection,
      primeBasisWheelProjection, hM]
  have hne : squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 1 ≠
      squareAnchorUnreservedOffsetProfile ({2, 3} : Finset ℕ) 2 := by
    intro heq
    have hmem1 : 0 ∈ squareAnchorUnreservedOffsetProfile
        ({2, 3} : Finset ℕ) 1 := by
      rw [mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor
        hS (by simp) 1 0]
      norm_num [hM, squareAnchorWheelProjection, primeBasisWheelProjection,
        IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis]
    have hmem2 := heq ▸ hmem1
    rw [mem_squareAnchorUnreservedOffsetProfile_iff_translatedSurvivor
      hS (by simp) 2 0] at hmem2
    norm_num [hM, squareAnchorWheelProjection, primeBasisWheelProjection,
      IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis] at hmem2
  /- The two profiles differ already at offset `0`. -/
  have hsucc : ∀ t, t < 6 → (t ∈ squareAnchorUnreservedOffsetProfile
      ({2, 3} : Finset ℕ) 2 ↔
        (t + 3) % 6 ∈ squareAnchorUnreservedOffsetProfile
          ({2, 3} : Finset ℕ) 1) := by
    intro t ht
    simpa [hM] using
      (mem_squareAnchorUnreservedOffsetProfile_succ_iff hS (by simp)
        (n := 1) (t := t) (by simpa [hM] using ht))
  /- The bounded successor check fixes the translation orientation. -/
  exact ⟨squareAnchorUnreservedOffsetProfile_eq_of_sameAnchorPhase hS hphase,
    hne, hsucc⟩

end DkMath.NumberTheory.PrimorialUniverse
