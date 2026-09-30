/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateProjectionTransport
import DkMathTest.Tromino.KempeRepairRegression

#print "file: DkMathTest.Tromino.StateProjectionTransportRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## A. An abstract chamber transport with a second admissible component -/

inductive TransportChild
  | root
  | moved
  deriving DecidableEq

inductive TransportParent
  | root
  | moved
  | extraRoot
  | extraMoved
  deriving DecidableEq

def transportChildStep : TransportChild → TransportChild → Prop
  | .root, .moved => True
  | .moved, .root => True
  | _, _ => False

def transportParentStep : TransportParent → TransportParent → Prop
  | .root, .moved => True
  | .moved, .root => True
  | .extraRoot, .extraMoved => True
  | .extraMoved, .extraRoot => True
  | _, _ => False

def transportAdmissible (_ : TransportParent) : Prop := True

def transportProject : TransportChild → TransportParent
  | .root => .root
  | .moved => .moved

theorem transportProject_injective : Function.Injective transportProject := by
  intro c d h
  cases c <;> cases d <;> simp_all [transportProject]

def transportPacket : RootedChamberTransport
    TransportChild TransportParent transportChildStep transportParentStep
      transportAdmissible transportProject .root .root where
  project_injective := transportProject_injective
  root_project := rfl
  parent_root_admissible := trivial
  map_step := by
    intro c d h
    cases c <;> cases d <;> simp_all [transportChildStep, transportProject,
      Restricted, transportAdmissible, transportParentStep]
  lift_step := by
    intro c p h
    cases c <;> cases p <;>
      simp_all [transportProject, Restricted, transportAdmissible,
        transportParentStep]
    · exact ⟨.moved, by simp [transportChildStep], rfl⟩
    · exact ⟨.root, by simp [transportChildStep], rfl⟩

theorem transport_chamber_equivalence :
    ∀ c, Reachable transportChildStep .root c ↔
      AdmissibleChamber transportParentStep transportAdmissible .root
        (transportProject c) := by
  intro c
  exact RootedChamberTransport.reachable_iff_admissibleChamber transportPacket

theorem transport_image_exact :
    ∀ p, AdmissibleChamber transportParentStep transportAdmissible .root p ↔
      ∃ c, Reachable transportChildStep .root c ∧ transportProject c = p := by
  intro p
  exact RootedChamberTransport.admissibleChamber_iff_exists_reachable_project_eq
    transportPacket

theorem transport_induced_edge_exact :
    ∀ c d, transportChildStep c d ↔
      Restricted transportParentStep transportAdmissible
        (transportProject c) (transportProject d) := by
  intro c d
  exact RootedChamberTransport.childStep_iff_restricted_projected transportPacket

theorem transport_extra_component_is_admissible :
    AdmissibleChamber transportParentStep transportAdmissible .extraRoot
      .extraRoot := by
  exact admissibleChamber_root_iff _ |>.mpr trivial

theorem transport_extra_component_not_in_root_chamber :
    ¬ AdmissibleChamber transportParentStep transportAdmissible .root
      .extraRoot := by
  intro h
  rcases (transport_image_exact .extraRoot).mp h with ⟨c, _, hproject⟩
  cases c <;> simp [transportProject] at hproject

/-! ## B. Shared coordinates across two graph topologies -/

def TinyEmptyGraph : SimpleGraph TinyVertex := ⊥

def tinyEmptyColoring : TinyEmptyGraph.Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun _ => 0)
    (by
      intro v w h
      simp [TinyEmptyGraph] at h)

def tinySingleMutable : TinyVertex → Prop := fun v => v = 0

def tinyOutsideBase : TinyVertex → TrominoState :=
  fun v => if v = 0 then 0 else ⟨0, 1⟩

theorem tinySource_agreesOutside :
    AgreesOutside tinySingleMutable tinyOutsideBase tinySource := by
  intro v hv
  fin_cases v
  · exact (hv rfl).elim
  · change (⟨0, 1⟩ : TrominoState) = ⟨0, 1⟩
    rfl

theorem tinyTarget_agreesOutside :
    AgreesOutside tinySingleMutable tinyOutsideBase tinyTarget := by
  intro v hv
  fin_cases v
  · exact (hv rfl).elim
  · change (⟨0, 1⟩ : TrominoState) = ⟨0, 1⟩
    rfl

theorem tiny_fixed_context_injectivity
    {source target : TinyGraph.Coloring TrominoState}
    (hsource : AgreesOutside tinySingleMutable tinyOutsideBase source)
    (htarget : AgreesOutside tinySingleMutable tinyOutsideBase target)
    (hprojection : mutableColorProjection TinyGraph tinySingleMutable source =
      mutableColorProjection TinyGraph tinySingleMutable target) :
    source = target := by
  exact mutableColorProjection_injective_of_agreesOutside hsource htarget
    hprojection

theorem tiny_source_target_not_equal : tinySource ≠ tinyTarget := by
  intro h
  exact tiny_changed (congrArg (fun c => c 0) h)

theorem tiny_source_target_projection_is_not_equal :
    mutableColorProjection TinyGraph tinySingleMutable tinySource ≠
      mutableColorProjection TinyGraph tinySingleMutable tinyTarget := by
  intro h
  exact tiny_source_target_not_equal
    (tiny_fixed_context_injectivity
      tinySource_agreesOutside tinyTarget_agreesOutside h)

theorem tiny_cross_graph_same_mutable_projection :
    SameMutableProjection tinySingleMutable tinySource tinyEmptyColoring := by
  apply (sameMutableProjection_iff).mpr
  intro v hv
  fin_cases v
  · change (0 : TrominoState) = 0
    rfl
  · have hfalse : False := by simpa [tinySingleMutable] using hv
    exact hfalse.elim

theorem tiny_cross_graph_same_mutable_projection_iff :
    SameMutableProjection tinySingleMutable tinySource tinyEmptyColoring ↔
      ∀ v, tinySingleMutable v → tinySource v = tinyEmptyColoring v := by
  exact sameMutableProjection_iff

end DkMathTest.Tromino
