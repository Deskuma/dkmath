/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RecursiveCosmicBridge

#print "file: DkMathTest.Tromino.RecursiveCosmicBridgeAxiomAudit"

namespace DkMathTest.Tromino.RecursiveCosmicBridgeAxiomAudit

open DkMath.Tromino
open DkMath.CosmicFormula.CoreBeamGap

example : macroSideScale 0 = 2 := macroSideScale_zero

example : macroSideScale 1 = 4 := macroSideScale_one

example (k : Nat) : macroSideScale k ^ 2 = 4 ^ (k + 1) :=
  macroSideScale_sq k

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).big = atomicMass (k + 1) M :=
  recursiveMassSplit_big k M

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).body = bodyAtomicMass k M :=
  recursiveMassSplit_body k M

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).gap = gapAtomicMass k M :=
  recursiveMassSplit_gap k M

example : (recursiveCosmicSplit 0).big = 16 :=
  recursiveCosmicSplit_zero_big

example : (recursiveCosmicSplit 0).body = 12 :=
  recursiveCosmicSplit_zero_body

example : (recursiveCosmicSplit 0).gap = 4 :=
  recursiveCosmicSplit_zero_gap

example : (recursiveCosmicSplit 1).big = 64 :=
  recursiveCosmicSplit_one_big

example : (recursiveCosmicSplit 1).body = 48 :=
  recursiveCosmicSplit_one_body

example : (recursiveCosmicSplit 1).gap = 16 :=
  recursiveCosmicSplit_one_gap

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    (recursiveMassSplit k M).big = (recursiveCosmicSplit k).big ∧
      (recursiveMassSplit k M).body = (recursiveCosmicSplit k).body ∧
      (recursiveMassSplit k M).gap = (recursiveCosmicSplit k).gap :=
  recursive_threeWay_cosmic_calibration k M

example (k : Nat) : Core 2 (macroSideScale k) = 4 ^ (k + 1) :=
  recursiveCosmicSplit_core k

example (k : Nat) :
    Beam 2 (macroSideScale k) (macroSideScale k) = 2 * 4 ^ (k + 1) :=
  recursiveCosmicSplit_beam k

example (k : Nat) : Gap 2 (macroSideScale k) = 4 ^ (k + 1) := by
  change macroSideScale k ^ 2 = 4 ^ (k + 1)
  exact macroSideScale_sq k

example (k : Nat) :
    (recursiveCosmicSplit k).big =
      Core 2 (macroSideScale k) +
        Beam 2 (macroSideScale k) (macroSideScale k) +
          Gap 2 (macroSideScale k) :=
  recursiveCosmicSplit_big_core_beam_gap k

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    bodyAtomicMass k M = 3 * gapAtomicMass k M :=
  bodyAtomicMass_eq_three_mul_gapAtomicMass k M

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    atomicMass (k + 1) M = 4 * gapAtomicMass k M :=
  atomicMass_successor_eq_four_mul_gapAtomicMass k M

#print axioms DkMath.Tromino.macroSideScale_sq
#print axioms DkMath.Tromino.recursiveMassSplit
#print axioms DkMath.Tromino.recursiveCosmicSplit
#print axioms DkMath.Tromino.recursive_threeWay_cosmic_calibration
#print axioms DkMath.Tromino.recursiveCosmicSplit_core
#print axioms DkMath.Tromino.recursiveCosmicSplit_beam
#print axioms DkMath.Tromino.recursiveCosmicSplit_big_core_beam_gap
#print axioms DkMath.Tromino.bodyAtomicMass_eq_three_mul_gapAtomicMass
#print axioms DkMath.Tromino.atomicMass_successor_eq_four_mul_gapAtomicMass

end DkMathTest.Tromino.RecursiveCosmicBridgeAxiomAudit
