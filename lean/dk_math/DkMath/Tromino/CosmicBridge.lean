/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.State
import DkMath.Tromino.Exchange
import DkMath.Tromino
import DkMath.CosmicFormula.Mass.BodyGapSplit
import DkMath.CosmicFormula.CoreBeamGap

#print "file: DkMath.Tromino.CosmicBridge"

namespace DkMath.Tromino

open DkMath.CosmicFormula.CoreBeamGap
open DkMath.CosmicFormula.Mass

/-!
# Three-way Body/Gap calibration

This module records the shared finite signature `4 = 3 + 1` in three neutral
`BodyGapSplit ℕ` packets. The packets remain separate: this is a numerical
calibration, not an identification of the state, geometric, and CosmicFormula
worlds.
-/

/-- The state-layer Body/Gap packet at a current state `x`. -/
noncomputable def stateSplit (x : TrominoState) : BodyGapSplit ℕ where
  big := Nat.card TrominoState
  body := (waitingStates x).card
  gap := 1
  split := by
    rw [card_state, card_waitingStates]

@[simp] theorem stateSplit_big (x : TrominoState) :
    (stateSplit x).big = 4 := by
  simp [stateSplit]

@[simp] theorem stateSplit_body (x : TrominoState) :
    (stateSplit x).body = 3 := by
  simp [stateSplit, card_waitingStates]

@[simp] theorem stateSplit_gap (x : TrominoState) :
    (stateSplit x).gap = 1 := by
  rfl

/-- The state carrier has one current slot in addition to its three waiting slots. -/
theorem state_card_eq_waiting_add_one (x : TrominoState) :
    Nat.card TrominoState = (waitingStates x).card + 1 := by
  exact (stateSplit x).split

/-- The geometric `2 × 2` block / L-tromino / hole packet. -/
def geometricSplit : BodyGapSplit ℕ where
  big := DkMath.Polyomino.area DkMath.Polyomino.Tromino.block2
  body := DkMath.Polyomino.area DkMath.Polyomino.Tromino.L_tromino
  gap := DkMath.Polyomino.area DkMath.Polyomino.Tromino.hole2
  split := DkMath.Polyomino.Tromino.area_block2_eq_area_L_add_area_hole

@[simp] theorem geometricSplit_big :
    geometricSplit.big = 4 := by
  change DkMath.Polyomino.area DkMath.Polyomino.Tromino.block2 = 4
  exact DkMath.Polyomino.Tromino.area_block2

@[simp] theorem geometricSplit_body :
    geometricSplit.body = 3 := by
  change DkMath.Polyomino.area DkMath.Polyomino.Tromino.L_tromino = 3
  exact DkMath.Polyomino.Tromino.area_L_tromino

@[simp] theorem geometricSplit_gap :
    geometricSplit.gap = 1 := by
  change DkMath.Polyomino.area DkMath.Polyomino.Tromino.hole2 = 1
  exact DkMath.Polyomino.Tromino.area_hole2

/-- The degree-two unit-square CosmicFormula packet. -/
def cosmicUnitSquareSplit : BodyGapSplit ℕ where
  big := DkMath.CosmicFormula.CoreBeamGap.Big (R := ℕ) 2 1 1
  body := DkMath.CosmicFormulaBinom.BodyN 2 1 1
  gap := DkMath.CosmicFormula.CoreBeamGap.Gap (R := ℕ) 2 1
  split := DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap (R := ℕ) 2 1 1

theorem cosmicUnitSquare_big :
    cosmicUnitSquareSplit.big = 4 := by
  norm_num [cosmicUnitSquareSplit, DkMath.CosmicFormula.CoreBeamGap.Big,
    DkMath.CosmicFormulaBinom.BigN]

theorem cosmicUnitSquare_gap :
    cosmicUnitSquareSplit.gap = 1 := by
  norm_num [cosmicUnitSquareSplit, DkMath.CosmicFormula.CoreBeamGap.Gap,
    DkMath.CosmicFormulaBinom.GapN]

theorem cosmicUnitSquare_body :
    cosmicUnitSquareSplit.body = 3 := by
  have hsplit :=
    DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap (R := ℕ) 2 1 1
  have hbig :
      DkMath.CosmicFormula.CoreBeamGap.Big (R := ℕ) 2 1 1 = 4 := by
    norm_num [DkMath.CosmicFormula.CoreBeamGap.Big,
      DkMath.CosmicFormulaBinom.BigN]
  have hgap :
      DkMath.CosmicFormula.CoreBeamGap.Gap (R := ℕ) 2 1 = 1 := by
    norm_num [DkMath.CosmicFormula.CoreBeamGap.Gap,
      DkMath.CosmicFormulaBinom.GapN]
  rw [hbig, hgap] at hsplit
  change DkMath.CosmicFormulaBinom.BodyN 2 1 1 = 3
  omega

/-!
The public calibration is componentwise. Equality of the packets themselves
would also compare their proof fields and would add no mathematical content.
-/

theorem threeWay_big (x : TrominoState) :
    (stateSplit x).big = geometricSplit.big ∧
      geometricSplit.big = cosmicUnitSquareSplit.big := by
  constructor
  · rw [stateSplit_big, geometricSplit_big]
  · rw [geometricSplit_big, cosmicUnitSquare_big]

theorem threeWay_body (x : TrominoState) :
    (stateSplit x).body = geometricSplit.body ∧
      geometricSplit.body = cosmicUnitSquareSplit.body := by
  constructor
  · rw [stateSplit_body, geometricSplit_body]
  · rw [geometricSplit_body, cosmicUnitSquare_body]

theorem threeWay_gap (x : TrominoState) :
    (stateSplit x).gap = geometricSplit.gap ∧
      geometricSplit.gap = cosmicUnitSquareSplit.gap := by
  constructor
  · rw [stateSplit_gap, geometricSplit_gap]
  · rw [geometricSplit_gap, cosmicUnitSquare_gap]

theorem threeWay_calibration (x : TrominoState) :
    ((stateSplit x).big = geometricSplit.big ∧
        geometricSplit.big = cosmicUnitSquareSplit.big) ∧
      ((stateSplit x).body = geometricSplit.body ∧
        geometricSplit.body = cosmicUnitSquareSplit.body) ∧
      ((stateSplit x).gap = geometricSplit.gap ∧
        geometricSplit.gap = cosmicUnitSquareSplit.gap) := by
  exact ⟨threeWay_big x, threeWay_body x, threeWay_gap x⟩

end DkMath.Tromino
