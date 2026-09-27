/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RecursiveMacro
import DkMath.CosmicFormula.CoreBeamGap
import DkMath.CosmicFormula.Mass.BodyGapSplit

#print "file: DkMath.Tromino.RecursiveCosmicBridge"

namespace DkMath.Tromino

open DkMath.CosmicFormula.CoreBeamGap
open DkMath.CosmicFormula.Mass
open DkMath.CosmicFormulaBinom

/-! The recursive Tromino mass split is calibrated componentwise with the
degree-two equal-axis CosmicFormula. No positional Core/Beam interpretation
is introduced here. -/

def macroSideScale (k : Nat) : Nat := 2 ^ (k + 1)

theorem macroSideScale_sq (k : Nat) :
    macroSideScale k ^ 2 = 4 ^ (k + 1) := by
  unfold macroSideScale
  calc
    (2 ^ (k + 1)) ^ 2 = 2 ^ ((k + 1) * 2) := by
      rw [← pow_mul]
    _ = 2 ^ (2 * (k + 1)) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ (k + 1) := by rw [pow_mul]
    _ = 4 ^ (k + 1) := by norm_num

theorem macroSideScale_zero : macroSideScale 0 = 2 := by decide

theorem macroSideScale_one : macroSideScale 1 = 4 := by decide

def recursiveMassSplit (k : Nat) (M : ScaledMacroCell (k + 1)) :
    BodyGapSplit Nat where
  big := atomicMass (k + 1) M
  body := bodyAtomicMass k M
  gap := gapAtomicMass k M
  split := (body_gap_mass_split k M).symm

@[simp] theorem recursiveMassSplit_big
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).big = atomicMass (k + 1) M := rfl

@[simp] theorem recursiveMassSplit_body
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).body = bodyAtomicMass k M := rfl

@[simp] theorem recursiveMassSplit_gap
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).gap = gapAtomicMass k M := rfl

def recursiveCosmicSplit (k : Nat) : BodyGapSplit Nat where
  big := DkMath.CosmicFormula.CoreBeamGap.Big 2
    (macroSideScale k) (macroSideScale k)
  body := DkMath.CosmicFormulaBinom.BodyN 2
    (macroSideScale k) (macroSideScale k)
  gap := DkMath.CosmicFormula.CoreBeamGap.Gap 2 (macroSideScale k)
  split := DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap 2
    (macroSideScale k) (macroSideScale k)

@[simp] theorem recursiveCosmicSplit_gap (k : Nat) :
    (recursiveCosmicSplit k).gap = 4 ^ (k + 1) := by
  change macroSideScale k ^ 2 = 4 ^ (k + 1)
  exact macroSideScale_sq k

theorem recursiveCosmicSplit_big_eq_four_mul_pow (k : Nat) :
    (recursiveCosmicSplit k).big = 4 * 4 ^ (k + 1) := by
  change (macroSideScale k + macroSideScale k) ^ 2 = _
  rw [show macroSideScale k + macroSideScale k =
      2 * macroSideScale k by ring]
  rw [mul_pow, macroSideScale_sq]
  ring

@[simp] theorem recursiveCosmicSplit_big (k : Nat) :
    (recursiveCosmicSplit k).big = 4 ^ (k + 2) := by
  rw [recursiveCosmicSplit_big_eq_four_mul_pow]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

theorem recursiveCosmicSplit_body (k : Nat) :
    (recursiveCosmicSplit k).body = 3 * 4 ^ (k + 1) := by
  have hsplit := (recursiveCosmicSplit k).split
  rw [recursiveCosmicSplit_big_eq_four_mul_pow,
    recursiveCosmicSplit_gap] at hsplit
  change 4 * 4 ^ (k + 1) =
    CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k) +
      4 ^ (k + 1) at hsplit
  change CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k) = _
  have hadd :
      CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k) +
          4 ^ (k + 1) = 3 * 4 ^ (k + 1) + 4 ^ (k + 1) := by
    calc
      CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k) +
          4 ^ (k + 1) = 4 * 4 ^ (k + 1) := hsplit.symm
      _ = 3 * 4 ^ (k + 1) + 4 ^ (k + 1) := by ring
  exact Nat.add_right_cancel hadd

theorem recursiveMassSplit_big_formula
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).big = 4 ^ (k + 2) := by
  change atomicMass (k + 1) M = 4 ^ (k + 2)
  rw [atomicMass_eq_pow_succ]

theorem recursiveMassSplit_body_formula
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).body = 3 * 4 ^ (k + 1) := by
  rw [recursiveMassSplit_body]
  exact bodyAtomicMass_eq_three_mul_pow k M

theorem recursiveMassSplit_gap_formula
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).gap = 4 ^ (k + 1) := by
  rw [recursiveMassSplit_gap]
  exact gapAtomicMass_eq_pow k M

theorem recursive_threeWay_cosmic_calibration
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).big = (recursiveCosmicSplit k).big ∧
      (recursiveMassSplit k M).body = (recursiveCosmicSplit k).body ∧
      (recursiveMassSplit k M).gap = (recursiveCosmicSplit k).gap := by
  constructor
  · rw [recursiveMassSplit_big_formula, recursiveCosmicSplit_big]
  constructor
  · rw [recursiveMassSplit_body_formula, recursiveCosmicSplit_body]
  · rw [recursiveMassSplit_gap_formula, recursiveCosmicSplit_gap]

theorem recursiveCosmicSplit_core (k : Nat) :
    DkMath.CosmicFormula.CoreBeamGap.Core 2 (macroSideScale k) =
      4 ^ (k + 1) := by
  change macroSideScale k ^ 2 = _
  exact macroSideScale_sq k

theorem recursiveCosmicSplit_beam (k : Nat) :
    DkMath.CosmicFormula.CoreBeamGap.Beam 2
        (macroSideScale k) (macroSideScale k) =
      2 * 4 ^ (k + 1) := by
  have hsplit := DkMath.CosmicFormula.CoreBeamGap.body_eq_core_add_beam
    (R := Nat) (d := 2) (by norm_num)
      (macroSideScale k) (macroSideScale k)
  have hbody := recursiveCosmicSplit_body k
  change CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k) = _ at hbody
  have hcore := recursiveCosmicSplit_core k
  change DkMath.CosmicFormula.CoreBeamGap.Core 2 (macroSideScale k) = _ at hcore
  rw [hbody, hcore] at hsplit
  omega

theorem recursiveCosmicSplit_big_core_beam_gap (k : Nat) :
    (recursiveCosmicSplit k).big =
      DkMath.CosmicFormula.CoreBeamGap.Core 2 (macroSideScale k) +
        DkMath.CosmicFormula.CoreBeamGap.Beam 2
          (macroSideScale k) (macroSideScale k) +
          DkMath.CosmicFormula.CoreBeamGap.Gap 2 (macroSideScale k) := by
  have hgap : DkMath.CosmicFormula.CoreBeamGap.Gap 2
      (macroSideScale k) = 4 ^ (k + 1) := by
    change macroSideScale k ^ 2 = _
    exact macroSideScale_sq k
  rw [recursiveCosmicSplit_big, recursiveCosmicSplit_core,
    recursiveCosmicSplit_beam, hgap]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

theorem bodyAtomicMass_eq_three_mul_gapAtomicMass
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    bodyAtomicMass k M = 3 * gapAtomicMass k M := by
  rw [bodyAtomicMass_eq_three_mul_pow, gapAtomicMass_eq_pow]

theorem atomicMass_successor_eq_four_mul_gapAtomicMass
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    atomicMass (k + 1) M = 4 * gapAtomicMass k M := by
  rw [atomicMass_successor_eq_four_mul_pow, gapAtomicMass_eq_pow]

theorem recursiveCosmicSplit_zero_big :
    (recursiveCosmicSplit 0).big = 16 := by
  simp

theorem recursiveCosmicSplit_zero_body :
    (recursiveCosmicSplit 0).body = 12 := by
  simpa using recursiveCosmicSplit_body 0

theorem recursiveCosmicSplit_zero_gap :
    (recursiveCosmicSplit 0).gap = 4 := by
  simp

theorem recursiveCosmicSplit_one_big :
    (recursiveCosmicSplit 1).big = 64 := by
  simp

theorem recursiveCosmicSplit_one_body :
    (recursiveCosmicSplit 1).body = 48 := by
  simpa using recursiveCosmicSplit_body 1

theorem recursiveCosmicSplit_one_gap :
    (recursiveCosmicSplit 1).gap = 16 := by
  simp

end DkMath.Tromino
