/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RecursiveMacro

#print "file: DkMathTest.Tromino.RecursiveMacroAxiomAudit"

namespace DkMathTest.Tromino.RecursiveMacroAxiomAudit

open DkMath.Tromino

example : Nat.card Block2Pos = 4 :=
  card_Block2Pos

example : bodyPositions.card = 3 :=
  card_bodyPositions

example : gapPositions.card = 1 :=
  card_gapPositions

example : bodyPositions ∪ gapPositions = Finset.univ :=
  bodyPositions_union_gapPositions

example : Disjoint bodyPositions gapPositions :=
  disjoint_bodyPositions_gapPositions

example : bodyPositions.card + gapPositions.card = 4 :=
  card_bodyPositions_add_gapPositions

example : atomicMass 0 (canonicalScaledMacroCell 0) = 4 :=
  atomicMass_canonical_zero

example : atomicMass 1 (canonicalScaledMacroCell 1) = 16 :=
  atomicMass_canonical_one

example : atomicMass 2 (canonicalScaledMacroCell 2) = 64 :=
  atomicMass_canonical_two

example : bodyAtomicMass 0 (canonicalScaledMacroCell 1) = 12 :=
  bodyAtomicMass_canonical_one

example : gapAtomicMass 0 (canonicalScaledMacroCell 1) = 4 :=
  gapAtomicMass_canonical_one

example : bodyAtomicMass 1 (canonicalScaledMacroCell 2) = 48 :=
  bodyAtomicMass_canonical_two

example : gapAtomicMass 1 (canonicalScaledMacroCell 2) = 16 :=
  gapAtomicMass_canonical_two

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    bodyAtomicMass k M + gapAtomicMass k M = atomicMass (k + 1) M :=
  body_gap_mass_split k M

example (k : Nat) (M : ScaledMacroCell k) :
    exchangeScaledMacroCell 0 k M = M :=
  exchangeScaledMacroCell_zero k M

example (delta : TrominoState) (k : Nat) (M : ScaledMacroCell k) :
    exchangeScaledMacroCell delta k
        (exchangeScaledMacroCell delta k M) = M :=
  exchangeScaledMacroCell_involutive delta k M

example (delta : TrominoState) (k : Nat) (M : ScaledMacroCell k) :
    atomicMass k (exchangeScaledMacroCell delta k M) = atomicMass k M :=
  atomicMass_exchangeScaledMacroCell delta k M

example (k : Nat) (M : ScaledMacroCell (k + 1)) :
    gapChild k M = M gapPosition :=
  gapChild_spec k M

#print axioms DkMath.Tromino.card_Block2Pos
#print axioms DkMath.Tromino.atomicMass_eq_pow_succ
#print axioms DkMath.Tromino.bodyAtomicMass_eq_three_mul_pow
#print axioms DkMath.Tromino.gapAtomicMass_eq_pow
#print axioms DkMath.Tromino.body_gap_mass_split
#print axioms DkMath.Tromino.exchangeScaledMacroCell_zero
#print axioms DkMath.Tromino.exchangeScaledMacroCell_involutive
#print axioms DkMath.Tromino.atomicMass_exchangeScaledMacroCell

end DkMathTest.Tromino.RecursiveMacroAxiomAudit
