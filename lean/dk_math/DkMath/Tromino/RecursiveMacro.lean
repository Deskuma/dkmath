/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.MacroTromino

#print "file: DkMath.Tromino.RecursiveMacro"

namespace DkMath.Tromino

open DkMath.Polyomino
open DkMath.Polyomino.Tromino

/-!
# Recursive scaled macro levels

This module iterates the already established four-cell macro unit.  Its
coordinates are finite block positions and its only quantitative observer is
atomic mass.  It deliberately stops before boundary, graph, or physical
flattening data.
-/

/-- A position in the fixed two-by-two macro block. -/
def Block2Pos := {c : Cell // c ∈ block2} deriving Fintype, DecidableEq

/-- The typed two-by-two block has four admissible positions. -/
theorem card_Block2Pos_fintype : Fintype.card Block2Pos = 4 := by
  decide

/-- The cardinality of the typed block position carrier is four. -/
theorem card_Block2Pos : Nat.card Block2Pos = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact card_Block2Pos_fintype

/-- The three retained positions of the block, expressed in the typed carrier. -/
def bodyPositions : Finset Block2Pos :=
  Finset.univ.filter (fun p => p.1 ∈ L_tromino)

/-- The one missing position of the block, expressed in the typed carrier. -/
def gapPositions : Finset Block2Pos :=
  Finset.univ.filter (fun p => p.1 ∈ hole2)

/-- Exactly three block positions belong to the retained L-shaped body. -/
theorem card_bodyPositions : bodyPositions.card = 3 := by
  decide

/-- Exactly one block position is the geometric gap. -/
theorem card_gapPositions : gapPositions.card = 1 := by
  decide

/-- The retained body and gap positions cover the whole block. -/
theorem bodyPositions_union_gapPositions :
    bodyPositions ∪ gapPositions = Finset.univ := by
  decide

/-- The retained body and gap positions are disjoint. -/
theorem disjoint_bodyPositions_gapPositions :
    Disjoint bodyPositions gapPositions := by
  decide

/-- The body/gap cardinalities reproduce the four positions of the block. -/
theorem card_bodyPositions_add_gapPositions :
    bodyPositions.card + gapPositions.card = 4 := by
  rw [card_bodyPositions, card_gapPositions]

/-- The unique typed hole position. -/
def gapPosition : Block2Pos :=
  ⟨(1, 1), by simp [block2]⟩

/-- The chosen typed gap position belongs to the gap-position set. -/
theorem gapPosition_mem : gapPosition ∈ gapPositions := by
  decide

/-- The level-indexed recursive carrier: four level-`k` children make level `k+1`. -/
def ScaledMacroCell : Nat → Type
  | 0 => FourColorMacroCell
  | k + 1 => Block2Pos → ScaledMacroCell k

/-- The canonical cell at every recursive level. -/
def canonicalScaledMacroCell : (k : Nat) → ScaledMacroCell k
  | 0 => atomicFourColorMacroCell
  | k + 1 => fun _ => canonicalScaledMacroCell k

/-- Atomic mass of a recursive cell. -/
def atomicMass : (k : Nat) → ScaledMacroCell k → Nat
  | 0, M => atomicCellCount M
  | k + 1, M => Finset.sum Finset.univ (fun p => atomicMass k (M p))

/-- Every level-`k` recursive carrier contains `4^(k+1)` atomic cells. -/
theorem atomicMass_eq_pow_succ :
    ∀ (k : Nat) (M : ScaledMacroCell k), atomicMass k M = 4 ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro M
      simpa [atomicMass] using atomicCellCount_eq_four M
  | succ k ih =>
      intro M
      simp [atomicMass, ih, card_Block2Pos_fintype, pow_succ,
        Nat.mul_comm]

/-- The canonical level-zero carrier has atomic mass `4`. -/
theorem atomicMass_canonical_zero :
    atomicMass 0 (canonicalScaledMacroCell 0) = 4 := by
  simpa using atomicMass_eq_pow_succ 0 (canonicalScaledMacroCell 0)

/-- The canonical level-one carrier has atomic mass `16`. -/
theorem atomicMass_canonical_one :
    atomicMass 1 (canonicalScaledMacroCell 1) = 16 := by
  simpa using atomicMass_eq_pow_succ 1 (canonicalScaledMacroCell 1)

/-- The canonical level-two carrier has atomic mass `64`. -/
theorem atomicMass_canonical_two :
    atomicMass 2 (canonicalScaledMacroCell 2) = 64 := by
  simpa using atomicMass_eq_pow_succ 2 (canonicalScaledMacroCell 2)

/-- The mass in the retained three-child body at a successor level. -/
def bodyAtomicMass (k : Nat) (M : ScaledMacroCell (k + 1)) : Nat :=
  Finset.sum bodyPositions (fun p => atomicMass k (M p))

/-- The mass in the one-child gap at a successor level. -/
def gapAtomicMass (k : Nat) (M : ScaledMacroCell (k + 1)) : Nat :=
  Finset.sum gapPositions (fun p => atomicMass k (M p))

/-- The retained recursive body has mass `3 · 4^(k+1)`. -/
theorem bodyAtomicMass_eq_three_mul_pow
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    bodyAtomicMass k M = 3 * 4 ^ (k + 1) := by
  unfold bodyAtomicMass
  calc
    Finset.sum bodyPositions (fun p => atomicMass k (M p)) =
        Finset.sum bodyPositions (fun _ => 4 ^ (k + 1)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact atomicMass_eq_pow_succ k (M p)
    _ = 3 * 4 ^ (k + 1) := by simp [card_bodyPositions]

/-- The recursive gap child has mass `4^(k+1)`. -/
theorem gapAtomicMass_eq_pow
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    gapAtomicMass k M = 4 ^ (k + 1) := by
  unfold gapAtomicMass
  calc
    Finset.sum gapPositions (fun p => atomicMass k (M p)) =
        Finset.sum gapPositions (fun _ => 4 ^ (k + 1)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact atomicMass_eq_pow_succ k (M p)
    _ = 4 ^ (k + 1) := by simp [card_gapPositions]

/-- A successor-level carrier has total mass `4 · 4^(k+1)`. -/
theorem atomicMass_successor_eq_four_mul_pow
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    atomicMass (k + 1) M = 4 * 4 ^ (k + 1) := by
  rw [atomicMass_eq_pow_succ (k + 1) M, pow_succ]
  ring

/-- The successor-level mass splits into body mass plus gap mass. -/
theorem body_gap_mass_split
    (k : Nat) (M : ScaledMacroCell (k + 1)) :
    bodyAtomicMass k M + gapAtomicMass k M = atomicMass (k + 1) M := by
  rw [bodyAtomicMass_eq_three_mul_pow, gapAtomicMass_eq_pow,
    atomicMass_successor_eq_four_mul_pow]
  ring

/-- The corresponding finite cardinality identity is `3 + 1 = 4`. -/
theorem body_gap_mass_split_three_plus_one :
    3 + 1 = 4 := by norm_num

/-- The canonical level-one body has mass `12`. -/
theorem bodyAtomicMass_canonical_one :
    bodyAtomicMass 0 (canonicalScaledMacroCell 1) = 12 := by
  simpa using bodyAtomicMass_eq_three_mul_pow 0 (canonicalScaledMacroCell 1)

/-- The canonical level-one gap has mass `4`. -/
theorem gapAtomicMass_canonical_one :
    gapAtomicMass 0 (canonicalScaledMacroCell 1) = 4 := by
  simpa using gapAtomicMass_eq_pow 0 (canonicalScaledMacroCell 1)

/-- The canonical level-two body has mass `48`. -/
theorem bodyAtomicMass_canonical_two :
    bodyAtomicMass 1 (canonicalScaledMacroCell 2) = 48 := by
  simpa using bodyAtomicMass_eq_three_mul_pow 1 (canonicalScaledMacroCell 2)

/-- The canonical level-two gap has mass `16`. -/
theorem gapAtomicMass_canonical_two :
    gapAtomicMass 1 (canonicalScaledMacroCell 2) = 16 := by
  simpa using gapAtomicMass_eq_pow 1 (canonicalScaledMacroCell 2)

/-- The typed gap child at a successor level. -/
def gapChild (k : Nat) (M : ScaledMacroCell (k + 1)) : ScaledMacroCell k :=
  M gapPosition

/-- The typed gap child is evaluation at the canonical gap position. -/
theorem gapChild_spec (k : Nat) (M : ScaledMacroCell (k + 1)) :
    gapChild k M = M gapPosition :=
  rfl

/-- Uniform recursive exchange, pointwise above level zero. -/
def exchangeScaledMacroCell (delta : TrominoState) :
    (k : Nat) → ScaledMacroCell k → ScaledMacroCell k
  | 0, M => exchangeFourColorMacroCell delta M
  | k + 1, M => fun p => exchangeScaledMacroCell delta k (M p)

/-- The zero exchange acts trivially at every recursive level. -/
theorem exchangeScaledMacroCell_zero :
    ∀ (k : Nat) (M : ScaledMacroCell k),
      exchangeScaledMacroCell 0 k M = M := by
  intro k
  induction k with
  | zero =>
      intro M
      exact exchangeFourColorMacroCell_zero M
  | succ k ih =>
      intro M
      funext p
      exact ih (M p)

/-- Applying the same recursive exchange twice returns the original carrier. -/
theorem exchangeScaledMacroCell_involutive
    (delta : TrominoState) :
    ∀ (k : Nat) (M : ScaledMacroCell k),
      exchangeScaledMacroCell delta k
          (exchangeScaledMacroCell delta k M) = M := by
  intro k
  induction k with
  | zero =>
      intro M
      exact exchangeFourColorMacroCell_involutive delta M
  | succ k ih =>
      intro M
      funext p
      exact ih (M p)

/-- Recursive exchange preserves atomic mass at every level. -/
theorem atomicMass_exchangeScaledMacroCell
    (delta : TrominoState) :
    ∀ (k : Nat) (M : ScaledMacroCell k),
      atomicMass k (exchangeScaledMacroCell delta k M) = atomicMass k M := by
  intro k
  induction k with
  | zero =>
      intro M
      exact atomicCellCount_exchangeFourColorMacroCell delta M
  | succ k ih =>
      intro M
      unfold atomicMass
      apply Finset.sum_congr rfl
      intro p hp
      exact ih (M p)

/-- Exchanging the canonical carrier preserves its expected power-of-four mass. -/
theorem atomicMass_exchangeScaledMacroCell_canonical
    (delta : TrominoState) (k : Nat) :
    atomicMass k (exchangeScaledMacroCell delta k
      (canonicalScaledMacroCell k)) = 4 ^ (k + 1) := by
  rw [atomicMass_exchangeScaledMacroCell delta k]
  exact atomicMass_eq_pow_succ k (canonicalScaledMacroCell k)

end DkMath.Tromino
