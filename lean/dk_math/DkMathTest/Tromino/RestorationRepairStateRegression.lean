/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RestorationRepairState

#print "file: DkMathTest.Tromino.RestorationRepairStateRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

abbrev RestoreVertex := Fin 5

def RestoreGraph : SimpleGraph RestoreVertex := ⊤

def restoreMutable : RestoreVertex → Prop := fun v => v = 0

def restoreColored : RestoreVertex → Prop := fun v => v = 0 ∨ v = 1

def restoreRemaining : RestoreVertex → Prop := fun v => v = 2 ∨ v = 3 ∨ v = 4

def restoreBase : RestoreVertex → TrominoState :=
  fun v => if v = 1 then ⟨0, 1⟩ else 0

def restoreContext : RestorationContext RestoreGraph restoreMutable where
  colored := restoreColored
  remaining := restoreRemaining
  base := restoreBase
  mutable_colored := by
    intro v hv
    left
    exact hv
  remaining_uncolored := by
    intro v hv hc
    fin_cases v <;> simp [restoreRemaining, restoreColored] at hv hc

def restoreSource : MutableCoordinates restoreMutable := fun _ => 0

def restoreTarget : MutableCoordinates restoreMutable := fun _ => ⟨1, 0⟩

theorem restore_zero_ne_01 :
    (0 : TrominoState) ≠ ⟨0, 1⟩ := by
  intro h
  have hsnd := congrArg Prod.snd h
  norm_num at hsnd

theorem restore_zero_ne_10 :
    (0 : TrominoState) ≠ ⟨1, 0⟩ := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

theorem restore_10_ne_01 :
    (⟨1, 0⟩ : TrominoState) ≠ ⟨0, 1⟩ := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

theorem restore_realize_mutable :
    realize restoreContext restoreSource 0 = 0 := by
  rw [realize_mutable restoreContext restoreSource (by simp [restoreMutable])]
  rfl

theorem restore_realize_outside :
    realize restoreContext restoreSource 2 = restoreBase 2 := by
  exact realize_outside restoreContext restoreSource (by simp [restoreMutable])

theorem restore_source_proper : restoreContext.Proper restoreSource := by
  intro u v huv hu hv
  fin_cases u <;> fin_cases v <;>
    simp_all [RestoreGraph, restoreColored, realize, restoreContext,
      restoreBase, restoreSource, restoreMutable, restore_zero_ne_01,
      restore_zero_ne_10, restore_10_ne_01] <;> norm_num at *

theorem restore_target_proper : restoreContext.Proper restoreTarget := by
  intro u v huv hu hv
  fin_cases u <;> fin_cases v <;>
    simp_all [RestoreGraph, restoreColored, realize, restoreContext,
      restoreBase, restoreTarget, restoreMutable, restore_zero_ne_01,
      restore_zero_ne_10, restore_10_ne_01]

theorem restore_source_missing_valid :
    restoreContext.MissingValid restoreSource := by
  intro w hw
  refine ⟨⟨1, 0⟩, ?_⟩
  intro u huw hu
  fin_cases u <;> simp_all [RestoreGraph, restoreColored, realize,
    restoreContext, restoreBase, restoreSource, restoreMutable,
    restoreRemaining, restore_zero_ne_01, restore_zero_ne_10,
    restore_10_ne_01] <;> norm_num at *

theorem restore_target_missing_valid :
    restoreContext.MissingValid restoreTarget := by
  intro w hw
  refine ⟨0, ?_⟩
  intro u huw hu
  fin_cases u <;> simp_all [RestoreGraph, restoreColored, realize,
    restoreContext, restoreBase, restoreTarget, restoreMutable,
    restoreRemaining]

theorem restore_source_admissible :
    RestorationAdmissible restoreContext restoreSource :=
  ⟨restore_source_proper, restore_source_missing_valid⟩

theorem restore_target_admissible :
    RestorationAdmissible restoreContext restoreTarget :=
  ⟨restore_target_proper, restore_target_missing_valid⟩

theorem restore_coordinate_step :
    CoordinateOnePointStep restoreMutable restoreSource restoreTarget := by
  refine ⟨⟨0, rfl⟩, ?_, ?_⟩
  · change (0 : TrominoState) ≠ ⟨1, 0⟩
    intro h
    have hfst := congrArg Prod.fst h
    norm_num at hfst
  · intro u hu
    have hu0 : u = ⟨0, by simp [restoreMutable]⟩ := by
      apply Subtype.ext
      simpa [restoreMutable] using u.2
    exact (hu hu0).elim

theorem restore_admissible_step :
    AdmissibleRestorationStep restoreContext restoreSource restoreTarget := by
  exact ⟨restore_source_admissible, restore_target_admissible,
    restore_coordinate_step⟩

theorem restore_step_symmetric :
    AdmissibleRestorationStep restoreContext restoreTarget restoreSource :=
  admissibleRestorationStep_symmetric restoreContext restore_admissible_step

theorem restore_step_onePointRecolor :
    OnePointRecolor (ColoredGraph restoreContext) (liftedMutable restoreContext)
      (partialColoring restoreContext restoreSource restore_source_proper)
      (partialColoring restoreContext restoreTarget restore_target_proper) :=
  admissibleRestorationStep_onePointRecolor restoreContext restore_admissible_step

theorem restore_step_singletonKempeMove :
    SingletonKempeMove (ColoredGraph restoreContext) (liftedMutable restoreContext)
      (partialColoring restoreContext restoreSource restore_source_proper)
      (partialColoring restoreContext restoreTarget restore_target_proper) :=
  admissibleRestorationStep_singletonKempeMove restoreContext restore_admissible_step

def restoreFailureColored : RestoreVertex → Prop := fun v => v ≠ 4

def restoreFailureRemaining : RestoreVertex → Prop := fun v => v = 4

def restoreFailureAssignment : RestoreVertex → TrominoState :=
  fun v => if v = 0 then 0 else if v = 1 then ⟨0, 1⟩
    else if v = 2 then ⟨1, 0⟩ else ⟨1, 1⟩

theorem restore_missing_fails_with_four_colors :
    ¬ MissingValid RestoreGraph restoreFailureColored restoreFailureRemaining
      restoreFailureAssignment := by
  intro h
  rcases h 4 (by rfl) with ⟨missing, hmissing⟩
  have h0 := hmissing 0 (by simp [RestoreGraph]) (by simp [restoreFailureColored])
  have h1 := hmissing 1 (by simp [RestoreGraph]) (by simp [restoreFailureColored])
  have h2 := hmissing 2 (by simp [RestoreGraph]) (by simp [restoreFailureColored])
  have h3 := hmissing 3 (by simp [RestoreGraph]) (by simp [restoreFailureColored])
  rcases missing with ⟨a, b⟩
  fin_cases a
  · fin_cases b
    · exact h0 rfl
    · exact h1 rfl
  · fin_cases b
    · exact h2 rfl
    · exact h3 rfl

theorem restore_proper_ignores_remaining_edges :
    restoreContext.Proper restoreSource :=
  restore_source_proper

def restoreChildColored : RestoreVertex → Prop :=
  fun v => v = 0 ∨ v = 1 ∨ v = 2

def restoreChildRemaining : RestoreVertex → Prop := fun v => v = 3 ∨ v = 4

def restoreChildContext : RestorationContext RestoreGraph restoreMutable where
  colored := restoreChildColored
  remaining := restoreChildRemaining
  base := fun v => if v = 1 then ⟨0, 1⟩ else 0
  mutable_colored := by
    intro v hv
    left
    exact hv
  remaining_uncolored := by
    intro v hv hc
    fin_cases v <;> simp [restoreChildRemaining, restoreChildColored] at hv hc

theorem restore_transport_filter :
    TransportAdmissibleRestorationStep restoreContext restoreChildContext
        restoreSource restoreTarget ↔
      AdmissibleRestorationStep restoreContext restoreSource restoreTarget ∧
        RestorationAdmissible restoreChildContext restoreSource ∧
        RestorationAdmissible restoreChildContext restoreTarget :=
  transportAdmissibleRestorationStep_iff restoreContext restoreChildContext

theorem restore_transport_filter_rejects_child :
    ¬ RestorationAdmissible restoreChildContext restoreSource := by
  intro h
  have hproper := h.1 (u := 0) (v := 2) (by simp [RestoreGraph])
    (by simp [restoreChildContext, restoreChildColored])
    (by simp [restoreChildContext, restoreChildColored])
  have hz : (0 : TrominoState) ≠ 0 := by
    simpa [realize, restoreChildContext, restoreSource, restoreMutable] using
      hproper
  exact hz rfl

end DkMathTest.Tromino
