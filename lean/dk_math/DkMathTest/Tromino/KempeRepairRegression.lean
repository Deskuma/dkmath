/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.KempeRepair

#print "file: DkMathTest.Tromino.KempeRepairRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

abbrev TinyVertex := Fin 2

def TinyGraph : SimpleGraph TinyVertex := ⊤

theorem tiny_zero_ne_01 :
    (0 : TrominoState) ≠ ⟨0, 1⟩ := by
  intro h
  have hsnd := congrArg Prod.snd h
  norm_num at hsnd

theorem tiny_10_ne_01 :
    (⟨1, 0⟩ : TrominoState) ≠ ⟨0, 1⟩ := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

def tinySource : TinyGraph.Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun v => if v = 0 then 0 else ⟨0, 1⟩)
    (by
      intro v w h
      fin_cases v <;> fin_cases w <;> simp_all [TinyGraph]
      all_goals exact tiny_zero_ne_01)

def tinyTarget : TinyGraph.Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun v => if v = 0 then ⟨1, 0⟩ else ⟨0, 1⟩)
    (by
      intro v w h
      fin_cases v <;> fin_cases w <;> simp_all [TinyGraph]
      all_goals exact tiny_10_ne_01)

def tinyMutable : TinyVertex → Prop := fun _ => True

theorem tiny_changed : tinySource 0 ≠ tinyTarget 0 := by
  change (0 : TrominoState) ≠ ⟨1, 0⟩
  intro h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

theorem tiny_away : ∀ u, u ≠ 0 → tinyTarget u = tinySource u := by
  intro u hu
  fin_cases u
  · exact (hu rfl).elim
  · change (⟨0, 1⟩ : TrominoState) = ⟨0, 1⟩
    rfl

theorem tiny_onePoint :
    OnePointRecolor TinyGraph tinyMutable tinySource tinyTarget := by
  exact ⟨0, trivial, tiny_changed, tiny_away⟩

theorem tiny_singleton_component :
    ∀ u, KempeReachable TinyGraph tinySource
      (tinySource 0) (tinyTarget 0) 0 u ↔ u = 0 := by
  intro u
  constructor
  · intro hreach
    rcases hreach with ⟨n, hpath⟩
    cases hpath with
    | zero =>
        rfl
    | @prepend n x y z hstep hrest =>
        exact (not_twoColorStep_at_onePoint tiny_away hstep).elim
  · intro hu
    subst u
    exact reachable_refl
      (TwoColorStep TinyGraph tinySource (tinySource 0) (tinyTarget 0)) 0

theorem tiny_exchange_bridge :
    ∃! delta, delta ≠ 0 ∧ exchange delta (tinySource 0) = tinyTarget 0 := by
  exact existsUnique_nonzero_exchange_to tiny_changed

theorem tiny_singleton_move :
    SingletonKempeMove TinyGraph tinyMutable tinySource tinyTarget := by
  exact onePointRecolor_singletonKempeMove tiny_onePoint

def tinyExit (_ : TinyGraph.Coloring TrominoState) : Prop := True

theorem tiny_reachable (c : TinyGraph.Coloring TrominoState) :
    ∃ n, CanExitAt (SingletonKempeStep TinyGraph tinyMutable) tinyExit n c := by
  exact ⟨0, c, trivial, Steps.zero _⟩

theorem tiny_repair_height_unit_slope :
    repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinySource
        (tiny_reachable tinySource) ≤
        repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinyTarget
        (tiny_reachable tinyTarget) + 1 ∧
      repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinyTarget
        (tiny_reachable tinyTarget) ≤
        repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinySource
        (tiny_reachable tinySource) + 1 := by
  exact singletonKempe_repairHeight_unit_slope TinyGraph tinyMutable tinyExit
    tiny_singleton_move (tiny_reachable tinySource) (tiny_reachable tinyTarget)

end DkMathTest.Tromino
