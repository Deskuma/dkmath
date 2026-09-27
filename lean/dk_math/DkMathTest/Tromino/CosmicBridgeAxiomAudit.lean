/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.CosmicBridge

#print "file: DkMathTest.Tromino.CosmicBridgeAxiomAudit"

namespace DkMathTest.Tromino.CosmicBridgeAxiomAudit

open DkMath.Tromino

example (x : TrominoState) :
    Nat.card TrominoState = (waitingStates x).card + 1 :=
  state_card_eq_waiting_add_one x

example (x : TrominoState) :
    (stateSplit x).big = 4 ∧ (stateSplit x).body = 3 ∧
      (stateSplit x).gap = 1 := by
  simp

example :
    geometricSplit.big = 4 ∧ geometricSplit.body = 3 ∧
      geometricSplit.gap = 1 := by
  simp

example :
    cosmicUnitSquareSplit.big = 4 ∧ cosmicUnitSquareSplit.body = 3 ∧
      cosmicUnitSquareSplit.gap = 1 := by
  exact ⟨cosmicUnitSquare_big, cosmicUnitSquare_body, cosmicUnitSquare_gap⟩

example (x : TrominoState) :
    ((stateSplit x).big = geometricSplit.big ∧
        geometricSplit.big = cosmicUnitSquareSplit.big) ∧
      ((stateSplit x).body = geometricSplit.body ∧
        geometricSplit.body = cosmicUnitSquareSplit.body) ∧
      ((stateSplit x).gap = geometricSplit.gap ∧
        geometricSplit.gap = cosmicUnitSquareSplit.gap) :=
  threeWay_calibration x

#print axioms DkMath.Tromino.state_card_eq_waiting_add_one
#print axioms DkMath.Tromino.geometricSplit_big
#print axioms DkMath.Tromino.cosmicUnitSquare_body
#print axioms DkMath.Tromino.threeWay_calibration

end DkMathTest.Tromino.CosmicBridgeAxiomAudit
