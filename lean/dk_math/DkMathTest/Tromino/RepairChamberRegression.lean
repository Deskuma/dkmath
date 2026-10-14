/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairChamber
import DkMathTest.Tromino.KempeRepairRegression

#print "file: DkMathTest.Tromino.RepairChamberRegression"

namespace DkMathTest.Tromino

open DkMath.Tromino

theorem tiny_zero_ne_10 :
    (0 : TrominoState) ≠ ⟨1, 0⟩ := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

def tinyThird : TinyGraph.Coloring TrominoState :=
  SimpleGraph.Coloring.mk
    (fun v => if v = 0 then 0 else ⟨1, 0⟩)
    (by
      intro v w h
      fin_cases v <;> fin_cases w
      · simp [TinyGraph] at h
      · exact tiny_zero_ne_10
      · exact Ne.symm tiny_zero_ne_10
      · simp [TinyGraph] at h)

def tinyAdmissible : TinyGraph.Coloring TrominoState → Prop :=
  fun c => c 1 = ⟨0, 1⟩

theorem tinySource_admissible : tinyAdmissible tinySource := by
  change (⟨0, 1⟩ : TrominoState) = ⟨0, 1⟩
  rfl

theorem tinyTarget_admissible : tinyAdmissible tinyTarget := by
  change (⟨0, 1⟩ : TrominoState) = ⟨0, 1⟩
  rfl

theorem tinyThird_not_admissible : ¬ tinyAdmissible tinyThird := by
  intro h
  change (⟨1, 0⟩ : TrominoState) = ⟨0, 1⟩ at h
  have hfst := congrArg Prod.fst h
  norm_num at hfst

theorem tiny_source_chamber :
    SingletonKempeRepairChamber TinyGraph tinyMutable tinyAdmissible
      tinySource tinySource := by
  rw [singletonKempeRepairChamber_root_iff]
  exact tinySource_admissible

theorem tiny_third_raw_zero_step_reachable :
    Reachable
      (Restricted (SingletonKempeStep TinyGraph tinyMutable) tinyAdmissible)
      tinyThird tinyThird := by
  exact reachable_refl _ tinyThird

theorem tiny_third_not_in_chamber :
    ¬ SingletonKempeRepairChamber TinyGraph tinyMutable tinyAdmissible
      tinyThird tinyThird := by
  intro h
  exact tinyThird_not_admissible h.1

theorem tiny_admissible_singleton_step :
    AdmissibleSingletonKempeStep TinyGraph tinyMutable tinyAdmissible
      tinySource tinyTarget := by
  exact onePointRecolor_admissibleSingletonKempeStep tiny_onePoint
    tinySource_admissible tinyTarget_admissible

theorem tiny_inadmissible_endpoint_blocks_step :
    ¬ AdmissibleSingletonKempeStep TinyGraph tinyMutable tinyAdmissible
      tinySource tinyThird := by
  intro h
  exact tinyThird_not_admissible h.2.1

def tinyChildStep :
    TinyGraph.Coloring TrominoState → TinyGraph.Coloring TrominoState → Prop :=
  AdmissibleSingletonKempeStep TinyGraph tinyMutable tinyAdmissible

theorem tiny_child_sectorization_interface :
    Reachable tinyChildStep tinySource tinyTarget ↔
      SingletonKempeRepairChamber TinyGraph tinyMutable tinyAdmissible
        tinySource tinyTarget := by
  exact childStep_reachable_iff_singletonKempeRepairChamber
    tinySource_admissible (by
      intro source target
      rfl)

theorem tiny_full_repair_height_unit_slope :
    repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinySource
        (tiny_reachable tinySource) ≤
        repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinyTarget
        (tiny_reachable tinyTarget) + 1 ∧
      repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinyTarget
        (tiny_reachable tinyTarget) ≤
        repairHeight (SingletonKempeStep TinyGraph tinyMutable) tinyExit tinySource
        (tiny_reachable tinySource) + 1 := by
  exact admissibleSingletonKempeStep_repairHeight_unit_slope TinyGraph
    tinyMutable tinyAdmissible tinyExit tiny_admissible_singleton_step
    (tiny_reachable tinySource) (tiny_reachable tinyTarget)

end DkMathTest.Tromino
