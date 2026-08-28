/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.WheelReplication
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.WheelProjection"

/-!
# Nested wheel projection

For a nonempty finite prime basis `S`, adjoining a fresh prime `q` produces a
finite enlarged wheel over the old wheel.  This module makes the quotient
map explicit: reduction modulo the old product sends every enlarged survivor
to an old survivor, every old survivor has a nonempty fiber, and every fiber
has exactly `q - 1` seats.  The quotient map also commutes with the product
period reflection.

The construction is finite and arithmetic.  It does not introduce square
anchors, Legendre propagation, a general wheel-gap recursion, Euler's totient
as the main proof route, PowerSwap, GN/CosmicFormula, PNT, or RH.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Canonical projection -/

/-- Reduction of a natural number to the one-period coordinate of `S`. -/
def primeBasisWheelProjection (S : Finset ℕ) (x : ℕ) : ℕ :=
  x % finitePrimeBasisProduct S

/-- The projection is a left inverse to a lift whose old coordinate is in range. -/
theorem primeBasisWheelProjection_lift
    {S : Finset ℕ} {r j : ℕ}
    (hrM : r < finitePrimeBasisProduct S) :
    primeBasisWheelProjection S (primeBasisWheelLift S r j) = r := by
  unfold primeBasisWheelProjection primeBasisWheelLift
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hrM]
  exact Nat.mod_eq_of_lt hrM

/-! ## Projection and surjectivity -/

/-- An enlarged survivor projects to the old survivor in the old period. -/
theorem enlargedWheelSurvivor_projects_to_oldSurvivor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : IsPrimeBasisWheelSurvivor (insert q S) x) :
    IsPrimeBasisWheelSurvivor S (primeBasisWheelProjection S x) := by
  obtain ⟨r, j, hr, hj, hxLift, _hqNot⟩ :=
    (enlargedWheelSurvivor_iff_exists_oldSurvivorLift hS hSne hq hqS).mp hx
  have hrM : r < finitePrimeBasisProduct S := hr.2.1
  have hProj : primeBasisWheelProjection S
      (primeBasisWheelLift S r j) = r :=
    primeBasisWheelProjection_lift hrM
  refine hxLift ▸ ?_
  simpa [hProj] using hr

/-- Every old survivor has a surviving lift above it. -/
theorem oldWheelSurvivor_has_enlargedLift
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    ∃ x : ℕ,
      IsPrimeBasisWheelSurvivor (insert q S) x ∧
      primeBasisWheelProjection S x = r := by
  have hcard :
      0 < (freshPrimeSurvivingLiftIndices S q r).card := by
    rw [card_freshPrimeSurvivingLiftIndices hS hq hqS hr]
    exact Nat.sub_pos_of_lt hq.one_lt
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  have hj' := mem_freshPrimeSurvivingLiftIndices_iff.mp hj
  refine ⟨primeBasisWheelLift S r j, ?_, ?_⟩
  · exact (enlargedWheelSurvivor_iff_exists_oldSurvivorLift
      hS hSne hq hqS).mpr ⟨r, j, hr, hj'.1, rfl, hj'.2⟩
  · exact primeBasisWheelProjection_lift hr.2.1

/-! ## Exact fibers -/

/-- The enlarged survivor seats lying over one old coordinate. -/
noncomputable def primeBasisWheelProjectionFiber
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (primeBasisWheelSurvivors (insert q S)).filter
    (fun x => primeBasisWheelProjection S x = r)

/-- A projection fiber is exactly the surviving lift image of its index set. -/
theorem primeBasisWheelProjectionFiber_eq_liftImage
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    primeBasisWheelProjectionFiber S q r =
      (freshPrimeSurvivingLiftIndices S q r).image
        (primeBasisWheelLift S r) := by
  classical
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    have hxSurv : IsPrimeBasisWheelSurvivor (insert q S) x :=
      mem_primeBasisWheelSurvivors_iff.mp hx'.1
    obtain ⟨r', j, hr', hj, hxLift, _hqNot⟩ :=
      (enlargedWheelSurvivor_iff_exists_oldSurvivorLift
        hS hSne hq hqS).mp hxSurv
    have hProj' := primeBasisWheelProjection_lift (j := j) hr'.2.1
    have hrr : r' = r := by
      calc
        r' = primeBasisWheelProjection S
            (primeBasisWheelLift S r' j) := hProj'.symm
        _ = primeBasisWheelProjection S x := by rw [hxLift]
        _ = r := hx'.2
    subst r'
    apply Finset.mem_image.mpr
    exact ⟨j, mem_freshPrimeSurvivingLiftIndices_iff.mpr
      ⟨hj, by simpa [hxLift] using _hqNot⟩, hxLift.symm⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := mem_freshPrimeSurvivingLiftIndices_iff.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨mem_primeBasisWheelSurvivors_iff.mpr ?_, ?_⟩
    · exact (enlargedWheelSurvivor_iff_exists_oldSurvivorLift
        hS hSne hq hqS).mpr ⟨r, j, hr, hj'.1, rfl, hj'.2⟩
    · exact primeBasisWheelProjection_lift hr.2.1

/-- Every old-survivor projection fiber has exactly `q - 1` seats. -/
theorem card_primeBasisWheelProjectionFiber
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : IsPrimeBasisWheelSurvivor S r) :
    (primeBasisWheelProjectionFiber S q r).card = q - 1 := by
  classical
  rw [primeBasisWheelProjectionFiber_eq_liftImage hS hSne hq hqS hr]
  calc
    ((freshPrimeSurvivingLiftIndices S q r).image
        (primeBasisWheelLift S r)).card =
        (freshPrimeSurvivingLiftIndices S q r).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hEq
      exact (primeBasisWheelLift_injective_on_period hr.2.1 hr.2.1 hEq).2
    _ = q - 1 := card_freshPrimeSurvivingLiftIndices hS hq hqS hr

/-! ## Reflection compatibility -/

/-- The old-period projection commutes with reflection on enlarged survivors. -/
theorem primeBasisWheelProjection_reflect_insert_fresh
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : IsPrimeBasisWheelSurvivor (insert q S) x) :
    primeBasisWheelProjection S
        (finitePrimeBasisProduct (insert q S) - x) =
      finitePrimeBasisProduct S - primeBasisWheelProjection S x := by
  obtain ⟨r, j, hr, hj, hxLift, _hqNot⟩ :=
    (enlargedWheelSurvivor_iff_exists_oldSurvivorLift hS hSne hq hqS).mp hx
  let M := finitePrimeBasisProduct S
  let k := q - (j + 1)
  have hjq : j + 1 ≤ q := Nat.succ_le_of_lt hj
  have hqSplit : q = k + (j + 1) := by
    dsimp [k]
    omega
  have hrM : r < M := hr.2.1
  have hrle : r ≤ M := Nat.le_of_lt hrM
  have hRefDecomp :
      finitePrimeBasisProduct (insert q S) - x = k * M + (M - r) := by
    rw [finitePrimeBasisProduct_insert hqS]
    rw [show finitePrimeBasisProduct S = M by rfl]
    rw [show x = r + j * M by simpa [M, primeBasisWheelLift] using hxLift]
    have hle : r + j * M ≤ q * M := by
      calc
        r + j * M = x := by simpa [M, primeBasisWheelLift] using hxLift.symm
        _ ≤ finitePrimeBasisProduct (insert q S) := hx.2.1.le
        _ = q * M := by rw [finitePrimeBasisProduct_insert hqS]
    rw [Nat.sub_eq_iff_eq_add hle]
    rw [hqSplit, add_mul, Nat.succ_mul]
    have hsub : M - r + r = M := Nat.sub_add_cancel hrle
    omega
  have hProj : primeBasisWheelProjection S x = r := by
    rw [hxLift]
    exact primeBasisWheelProjection_lift hr.2.1
  rw [hRefDecomp, hProj]
  unfold primeBasisWheelProjection
  rw [show finitePrimeBasisProduct S = M by rfl]
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt
    (Nat.sub_lt_of_pos_le hr.1 hrle)]
  simpa using Nat.mod_eq_of_lt (Nat.sub_lt_of_pos_le hr.1 hrle)

/-! ## The visible `6 → 30` regression -/

/-- The `6 → 30` projection fiber over `1` is `{1, 7, 13, 19}`. -/
theorem primeBasisWheelProjectionFiber_two_three_five_one :
    primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 1 =
      ({1, 7, 13, 19} : Finset ℕ) := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by norm_num
  have hr : IsPrimeBasisWheelSurvivor ({2, 3} : Finset ℕ) 1 := by
    norm_num [IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis,
      finitePrimeBasisProduct]
  rw [primeBasisWheelProjectionFiber_eq_liftImage hS hSne hq hqS hr]
  have hIdx : freshPrimeSurvivingLiftIndices ({2, 3} : Finset ℕ) 5 1 =
      ({0, 1, 2, 3} : Finset ℕ) := by
    ext j
    rw [mem_freshPrimeSurvivingLiftIndices_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hnot⟩
      interval_cases j <;>
        norm_num [primeBasisWheelLift, finitePrimeBasisProduct] at *
    · intro hj
      rcases hj with rfl | rfl | rfl | rfl <;>
        norm_num [primeBasisWheelLift, finitePrimeBasisProduct]
  rw [hIdx]
  norm_num [primeBasisWheelLift, finitePrimeBasisProduct]

/-- The `6 → 30` projection fiber over `5` is `{11, 17, 23, 29}`. -/
theorem primeBasisWheelProjectionFiber_two_three_five_five :
    primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 5 =
      ({11, 17, 23, 29} : Finset ℕ) := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hSne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by norm_num
  have hr : IsPrimeBasisWheelSurvivor ({2, 3} : Finset ℕ) 5 := by
    norm_num [IsPrimeBasisWheelSurvivor, ReservedByPrimeBasis,
      finitePrimeBasisProduct]
  rw [primeBasisWheelProjectionFiber_eq_liftImage hS hSne hq hqS hr]
  have hIdx : freshPrimeSurvivingLiftIndices ({2, 3} : Finset ℕ) 5 5 =
      ({1, 2, 3, 4} : Finset ℕ) := by
    ext j
    rw [mem_freshPrimeSurvivingLiftIndices_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hnot⟩
      interval_cases j <;>
        norm_num [primeBasisWheelLift, finitePrimeBasisProduct] at *
    · intro hj
      rcases hj with rfl | rfl | rfl | rfl <;>
        norm_num [primeBasisWheelLift, finitePrimeBasisProduct]
  rw [hIdx]
  norm_num [primeBasisWheelLift, finitePrimeBasisProduct]

/-- Both visible `6 → 30` fibers have the expected cardinality four. -/
theorem card_primeBasisWheelProjectionFiber_two_three_five :
    (primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 1).card = 4 ∧
      (primeBasisWheelProjectionFiber ({2, 3} : Finset ℕ) 5 5).card = 4 := by
  rw [primeBasisWheelProjectionFiber_two_three_five_one,
    primeBasisWheelProjectionFiber_two_three_five_five]
  decide

end DkMath.NumberTheory.PrimorialUniverse
