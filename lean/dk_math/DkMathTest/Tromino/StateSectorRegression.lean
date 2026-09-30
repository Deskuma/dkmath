/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateSector

#print "file: DkMathTest.Tromino.StateSectorRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

inductive SectorState
  | root
  | allowed
  | blocked
  | other
  deriving DecidableEq

def parentStep : SectorState → SectorState → Prop
  | .root, .allowed => True
  | .allowed, .root => True
  | .root, .blocked => True
  | .blocked, .root => True
  | .blocked, .other => True
  | .other, .blocked => True
  | _, _ => False

def admissible : SectorState → Prop
  | .root => True
  | .allowed => True
  | _ => False

def childStep : SectorState → SectorState → Prop :=
  Restricted parentStep admissible

theorem childStep_eq_restricted : ∀ x y,
    childStep x y ↔ Restricted parentStep admissible x y := by
  intro x y
  rfl

theorem allowed_in_root_chamber :
    Reachable childStep .root .allowed := by
  refine ⟨1, ?_⟩
  exact Steps.prepend (x := SectorState.root) (y := SectorState.allowed)
    (z := SectorState.allowed)
    ⟨by trivial, by trivial, by trivial⟩ (Steps.zero _)

theorem restricted_path_ends_admissible
    {R : SectorState → SectorState → Prop} {A : SectorState → Prop}
    {root x : SectorState} (hroot : A root) :
    Reachable (Restricted R A) root x → A x := by
  rintro ⟨n, hpath⟩
  induction hpath with
  | zero =>
      exact hroot
  | prepend hstep hrest ih =>
      exact ih hstep.2.1

theorem blocked_outside_root_chamber :
    ¬ Reachable childStep .root .blocked := by
  intro hreach
  have hadm : admissible .blocked :=
    restricted_path_ends_admissible (R := parentStep) (A := admissible)
      (root := .root) (x := .blocked) trivial
      ((reachable_iff_restricted childStep_eq_restricted).mp hreach)
  exact hadm

theorem sectorization_regression :
    Reachable childStep .root .allowed ↔
      Reachable (Restricted parentStep admissible) .root .allowed := by
  exact chamber_sectorization childStep_eq_restricted .root .allowed

end DkMathTest.Tromino
