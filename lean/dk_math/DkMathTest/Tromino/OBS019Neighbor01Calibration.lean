/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateProjectionTransport

#print "file: DkMathTest.Tromino.OBS019Neighbor01Calibration"

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Frozen OBS-019 neighbor-01 data

This file is a kernel-checked calibration of the frozen Python observation.
The four-state rows below are copied in mutable order
`[4, 5, 8, 9, 10, 12, 13, 14, 15, 17, 18]` from the committed JSON
artifacts.  The parent and child names are intentionally local to this test:
no production theorem is inferred from this finite witness.
-/

inductive PythonColor
  | zero
  | one
  | two
  | three
  deriving DecidableEq

def decodePythonColor : PythonColor → TrominoState
  | .zero => (0, 0)
  | .one => (0, 1)
  | .two => (1, 0)
  | .three => (1, 1)

inductive ChildState
  | c0
  | c1
  | c2
  | c3
  deriving DecidableEq

inductive ParentState
  | p8
  | p10
  | p12
  | p14
  deriving DecidableEq

def parentStateId : ParentState → Nat
  | .p8 => 8
  | .p10 => 10
  | .p12 => 12
  | .p14 => 14

def childRow0 : Fin 11 → TrominoState
  | ⟨0, _⟩ => decodePythonColor .zero
  | ⟨1, _⟩ => decodePythonColor .three
  | ⟨2, _⟩ => decodePythonColor .one
  | ⟨3, _⟩ => decodePythonColor .one
  | ⟨4, _⟩ => decodePythonColor .one
  | ⟨5, _⟩ => decodePythonColor .zero
  | ⟨6, _⟩ => decodePythonColor .zero
  | ⟨7, _⟩ => decodePythonColor .one
  | ⟨8, _⟩ => decodePythonColor .zero
  | ⟨9, _⟩ => decodePythonColor .one
  | ⟨10, _⟩ => decodePythonColor .three

def childRow1 : Fin 11 → TrominoState
  | ⟨0, _⟩ => decodePythonColor .zero
  | ⟨1, _⟩ => decodePythonColor .three
  | ⟨2, _⟩ => decodePythonColor .one
  | ⟨3, _⟩ => decodePythonColor .one
  | ⟨4, _⟩ => decodePythonColor .one
  | ⟨5, _⟩ => decodePythonColor .zero
  | ⟨6, _⟩ => decodePythonColor .one
  | ⟨7, _⟩ => decodePythonColor .zero
  | ⟨8, _⟩ => decodePythonColor .zero
  | ⟨9, _⟩ => decodePythonColor .one
  | ⟨10, _⟩ => decodePythonColor .three

def childRow2 : Fin 11 → TrominoState
  | ⟨0, _⟩ => decodePythonColor .zero
  | ⟨1, _⟩ => decodePythonColor .three
  | ⟨2, _⟩ => decodePythonColor .one
  | ⟨3, _⟩ => decodePythonColor .one
  | ⟨4, _⟩ => decodePythonColor .one
  | ⟨5, _⟩ => decodePythonColor .zero
  | ⟨6, _⟩ => decodePythonColor .three
  | ⟨7, _⟩ => decodePythonColor .zero
  | ⟨8, _⟩ => decodePythonColor .zero
  | ⟨9, _⟩ => decodePythonColor .one
  | ⟨10, _⟩ => decodePythonColor .three

def childRow3 : Fin 11 → TrominoState
  | ⟨0, _⟩ => decodePythonColor .zero
  | ⟨1, _⟩ => decodePythonColor .three
  | ⟨2, _⟩ => decodePythonColor .one
  | ⟨3, _⟩ => decodePythonColor .one
  | ⟨4, _⟩ => decodePythonColor .one
  | ⟨5, _⟩ => decodePythonColor .zero
  | ⟨6, _⟩ => decodePythonColor .three
  | ⟨7, _⟩ => decodePythonColor .one
  | ⟨8, _⟩ => decodePythonColor .zero
  | ⟨9, _⟩ => decodePythonColor .one
  | ⟨10, _⟩ => decodePythonColor .three

def childProjection : ChildState → Fin 11 → TrominoState
  | .c0 => childRow0
  | .c1 => childRow1
  | .c2 => childRow2
  | .c3 => childRow3

def parentProjection : ParentState → Fin 11 → TrominoState
  | .p8 => childRow0
  | .p10 => childRow1
  | .p12 => childRow2
  | .p14 => childRow3

def project : ChildState → ParentState
  | .c0 => .p8
  | .c1 => .p10
  | .c2 => .p12
  | .c3 => .p14

def childStep : ChildState → ChildState → Prop
  | .c0, .c3 => True
  | .c1, .c2 => True
  | .c2, .c1 => True
  | .c2, .c3 => True
  | .c3, .c0 => True
  | .c3, .c2 => True
  | _, _ => False

def parentStep : ParentState → ParentState → Prop
  | .p8, .p14 => True
  | .p10, .p12 => True
  | .p12, .p10 => True
  | .p12, .p14 => True
  | .p14, .p8 => True
  | .p14, .p12 => True
  | _, _ => False

def parentAdmissible (_ : ParentState) : Prop := True

theorem project_injective : Function.Injective project := by
  intro c d h
  cases c <;> cases d <;> simp [project] at h ⊢

theorem neighbor01_edge_exact : ∀ c d, childStep c d ↔ parentStep (project c) (project d) := by
  intro c d
  cases c <;> cases d <;> simp [childStep, parentStep, project]

theorem neighbor01_projection_rows : ∀ c, parentProjection (project c) = childProjection c := by
  intro c
  cases c <;> rfl

theorem neighbor01_transport : RootedChamberTransport
    ChildState ParentState childStep parentStep parentAdmissible project .c2 .p12 where
  project_injective := project_injective
  root_project := rfl
  parent_root_admissible := trivial
  map_step := by
    intro c d h
    have hedges := (neighbor01_edge_exact c d).mp h
    exact ⟨trivial, trivial, hedges⟩
  lift_step := by
    intro c p h
    cases c with
    | c0 =>
        cases p with
        | p8 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p10 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p12 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p14 => exact ⟨.c3, by simp [childStep], rfl⟩
    | c1 =>
        cases p with
        | p8 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p10 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p12 => exact ⟨.c2, by simp [childStep], rfl⟩
        | p14 => simp [Restricted, project, parentStep, parentAdmissible] at h
    | c2 =>
        cases p with
        | p8 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p10 => exact ⟨.c1, by simp [childStep], rfl⟩
        | p12 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p14 => exact ⟨.c3, by simp [childStep], rfl⟩
    | c3 =>
        cases p with
        | p8 => exact ⟨.c0, by simp [childStep], rfl⟩
        | p10 => simp [Restricted, project, parentStep, parentAdmissible] at h
        | p12 => exact ⟨.c2, by simp [childStep], rfl⟩
        | p14 => simp [Restricted, project, parentStep, parentAdmissible] at h

theorem child_root_reaches_all : ∀ c, Reachable childStep .c2 c := by
  have hc23 : childStep .c2 .c3 := by simp [childStep]
  have hc31 : childStep .c3 .c0 := by simp [childStep]
  have hc21 : childStep .c2 .c1 := by simp [childStep]
  intro c
  cases c with
  | c0 =>
      refine ⟨2, ?_⟩
      exact Steps.prepend hc23 (Steps.prepend hc31 (Steps.zero _))
  | c1 =>
      exact ⟨1, Steps.prepend hc21 (Steps.zero _)⟩
  | c2 =>
      exact ⟨0, Steps.zero _⟩
  | c3 =>
      exact ⟨1, Steps.prepend hc23 (Steps.zero _)⟩

theorem parent_root_reaches_all : ∀ p, Reachable parentStep .p12 p := by
  have hp1214 : parentStep .p12 .p14 := by simp [parentStep]
  have hp148 : parentStep .p14 .p8 := by simp [parentStep]
  have hp1210 : parentStep .p12 .p10 := by simp [parentStep]
  intro p
  cases p with
  | p8 =>
      refine ⟨2, ?_⟩
      exact Steps.prepend hp1214 (Steps.prepend hp148 (Steps.zero _))
  | p10 =>
      exact ⟨1, Steps.prepend hp1210 (Steps.zero _)⟩
  | p12 =>
      exact ⟨0, Steps.zero _⟩
  | p14 =>
      exact ⟨1, Steps.prepend hp1214 (Steps.zero _)⟩

theorem neighbor01_chamber_equivalence :
    ∀ c, Reachable childStep .c2 c ↔
      AdmissibleChamber parentStep parentAdmissible .p12 (project c) := by
  intro c
  exact RootedChamberTransport.reachable_iff_admissibleChamber neighbor01_transport

theorem neighbor01_parent_component_exact :
    ∀ p, AdmissibleChamber parentStep parentAdmissible .p12 p := by
  intro p
  cases p with
  | p8 =>
      simpa [project] using
        (neighbor01_chamber_equivalence .c0).mp (child_root_reaches_all .c0)
  | p10 =>
      simpa [project] using
        (neighbor01_chamber_equivalence .c1).mp (child_root_reaches_all .c1)
  | p12 =>
      simpa [project] using
        (neighbor01_chamber_equivalence .c2).mp (child_root_reaches_all .c2)
  | p14 =>
      simpa [project] using
        (neighbor01_chamber_equivalence .c3).mp (child_root_reaches_all .c3)

theorem neighbor01_child_component_exact :
    ∀ c, Reachable childStep .c2 c := child_root_reaches_all

def obs019Neighbor01Seed : Nat := 11000009
def obs019Neighbor01Step : Nat := 16
def obs019Neighbor01Move : List Nat := [4, 21, 5, 17]
def obs019Neighbor01MutableVertices : List Nat :=
  [4, 5, 8, 9, 10, 12, 13, 14, 15, 17, 18]
def obs019Neighbor01ChildEdges : List (Nat × Nat) := [(0, 3), (1, 2), (2, 3)]
def obs019Neighbor01ParentEdges : List (Nat × Nat) := [(8, 14), (10, 12), (12, 14)]
def obs019Neighbor01ParentHeight : ParentState → Nat
  | .p8 => 9
  | .p10 => 9
  | .p12 => 10
  | .p14 => 9

theorem obs019Neighbor01_baseline_maps_to_parent12 :
    project .c2 = .p12 ∧ parentStateId (project .c2) = 12 := by
  exact ⟨rfl, rfl⟩

theorem obs019Neighbor01_provenance :
    obs019Neighbor01Seed = 11000009 ∧ obs019Neighbor01Step = 16 ∧
      obs019Neighbor01Move = [4, 21, 5, 17] := by
  exact ⟨rfl, rfl, rfl⟩

theorem obs019Neighbor01_frozen_parent_heights :
    obs019Neighbor01ParentHeight .p8 = 9 ∧
      obs019Neighbor01ParentHeight .p10 = 9 ∧
        obs019Neighbor01ParentHeight .p12 = 10 ∧
          obs019Neighbor01ParentHeight .p14 = 9 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end DkMathTest.Tromino
