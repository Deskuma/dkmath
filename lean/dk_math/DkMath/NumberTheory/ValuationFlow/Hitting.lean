/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Mass.Branch

#print "file: DkMath.NumberTheory.ValuationFlow.Hitting"

open scoped BigOperators

namespace DkMath.NumberTheory.ValuationFlow

open DkMath.CosmicFormula.Mass

/--
Total mass of a finite hit set.

This is intentionally finite.  The analytic Erdos #1196 layer will later choose
a concrete weight such as `1 / (n * log n)`; this file only fixes the finite
combinatorial spine.
-/
def hitSetMass {α : Type _} (M : MassSpace α) (H : Finset α) : ℚ :=
  H.sum fun h => M.μ h

/-- Total mass of a finite source/root set. -/
def sourceSetMass {α : Type _} (M : MassSpace α) (R : Finset α) : ℚ :=
  R.sum fun r => M.μ r

/--
A finite hitting assignment controlled by source mass.

Each hit is assigned to a source/root in `R`; assignments are injective on the
hit set and every hit has mass bounded by its assigned source.  This is the
minimal non-overlap principle needed before adding concrete chain reachability.
-/
structure MassControlledAssignment {α : Type _} [DecidableEq α]
    (M : MassSpace α) (H R : Finset α) where
  assign : α → α
  assign_mem : ∀ h ∈ H, assign h ∈ R
  injective_on_hits : Set.InjOn assign H
  mass_le_assign : ∀ h ∈ H, M.μ h ≤ M.μ (assign h)

section Basic

variable {α : Type _}

@[simp] theorem hitSetMass_empty (M : MassSpace α) :
    hitSetMass M (∅ : Finset α) = 0 := by
  simp [hitSetMass]

@[simp] theorem sourceSetMass_empty (M : MassSpace α) :
    sourceSetMass M (∅ : Finset α) = 0 := by
  simp [sourceSetMass]

@[simp] theorem hitSetMass_singleton (M : MassSpace α) (a : α) :
    hitSetMass M ({a} : Finset α) = M.μ a := by
  simp [hitSetMass]

@[simp] theorem sourceSetMass_singleton (M : MassSpace α) (a : α) :
    sourceSetMass M ({a} : Finset α) = M.μ a := by
  simp [sourceSetMass]

/-- Hit-set mass is nonnegative. -/
theorem hitSetMass_nonneg (M : MassSpace α) (H : Finset α) :
    0 ≤ hitSetMass M H := by
  simpa [hitSetMass] using Finset.sum_nonneg fun h _hh => M.nonneg h

/-- Source-set mass is nonnegative. -/
theorem sourceSetMass_nonneg (M : MassSpace α) (R : Finset α) :
    0 ≤ sourceSetMass M R := by
  simpa [sourceSetMass] using Finset.sum_nonneg fun r _hr => M.nonneg r

/-- A singleton hit controlled by the same singleton source. -/
theorem hitSetMass_singleton_le_sourceSetMass_singleton
    (M : MassSpace α) (a : α) :
    hitSetMass M ({a} : Finset α) ≤ sourceSetMass M ({a} : Finset α) := by
  simp

end Basic

section Assignment

variable {α : Type _} [DecidableEq α]

/--
Finite non-overlapping hitting bound.

If every hit injects into a source/root with no larger mass, then the total hit
mass is bounded by the total source mass.
-/
theorem hitSetMass_le_sourceSetMass_of_injective_assignment
    (M : MassSpace α) {H R : Finset α}
    (A : MassControlledAssignment M H R) :
    hitSetMass M H ≤ sourceSetMass M R := by
  classical
  have hhit_le_image :
      H.sum (fun h => M.μ h) ≤ H.sum (fun h => M.μ (A.assign h)) := by
    exact Finset.sum_le_sum fun h hh => A.mass_le_assign h hh
  have hsum_image :
      H.sum (fun h => M.μ (A.assign h)) = (H.image A.assign).sum fun r => M.μ r := by
    exact (Finset.sum_image A.injective_on_hits).symm
  have himage_subset : H.image A.assign ⊆ R := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨h, hh, rfl⟩
    exact A.assign_mem h hh
  have himage_le_source :
      (H.image A.assign).sum (fun r => M.μ r) ≤ R.sum fun r => M.μ r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun r _hrR _hrImage => M.nonneg r)
  calc
    hitSetMass M H = H.sum (fun h => M.μ h) := rfl
    _ ≤ H.sum (fun h => M.μ (A.assign h)) := hhit_le_image
    _ = (H.image A.assign).sum (fun r => M.μ r) := hsum_image
    _ ≤ R.sum (fun r => M.μ r) := himage_le_source
    _ = sourceSetMass M R := rfl

/--
Alias phrased as "non-overlapping hits do not exceed source mass".
-/
theorem nonoverlapping_hitSetMass_le_sourceSetMass
    (M : MassSpace α) {H R : Finset α}
    (A : MassControlledAssignment M H R) :
    hitSetMass M H ≤ sourceSetMass M R :=
  hitSetMass_le_sourceSetMass_of_injective_assignment M A

end Assignment

end DkMath.NumberTheory.ValuationFlow
