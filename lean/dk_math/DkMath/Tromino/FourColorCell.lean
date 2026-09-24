/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino
import DkMath.Tromino.PieceExchange

#print "file: DkMath.Tromino.FourColorCell"

namespace DkMath.Tromino

open DkMath.Polyomino
open DkMath.Polyomino.Tromino

/-!
# Atomic four-state colored cells

This module is the first geometric colored layer above the state-only
exchange calculus. It deliberately stops at one finite 2x2 block.
-/

/-- A finite geometric shape with a state assigned to every lattice cell. -/
structure ColoredShape where
  shape : Shape
  color : Cell → TrominoState

@[ext] theorem ColoredShape.ext'
    {P Q : ColoredShape} (hshape : P.shape = Q.shape)
    (hcolor : P.color = Q.color) : P = Q := by
  cases P
  cases Q
  simp_all

/-- The number of cells of a shape carrying a specified state. -/
def stateMultiplicity (P : ColoredShape) (s : TrominoState) : ℕ :=
  (P.shape.filter (fun c => P.color c = s)).card

/-- The four states are the image of the shape, with the shape having four cells. -/
def CompleteFourState (P : ColoredShape) : Prop :=
  P.shape.card = 4 ∧
    P.shape.image P.color = (Finset.univ : Finset TrominoState)

/-- Complete four-state data gives a unique cell for every state. -/
theorem completeFourState_existsUnique_cell
    {P : ColoredShape} (hP : CompleteFourState P) (s : TrominoState) :
    ∃! c, c ∈ P.shape ∧ P.color c = s := by
  have hmem : s ∈ P.shape.image P.color := by
    rw [hP.2]
    simp
  rcases Finset.mem_image.mp hmem with ⟨c, hc, hcs⟩
  have hcard_image : (P.shape.image P.color).card = P.shape.card := by
    rw [hP.2, hP.1]
    simp
  have hinj : Set.InjOn P.color P.shape :=
    Finset.card_image_iff.mp hcard_image
  refine ⟨c, ⟨hc, hcs⟩, ?_⟩
  intro d hd
  exact (hinj hc hd.1 (hcs.trans hd.2.symm)).symm

/-- Complete four-state data has multiplicity one for every state. -/
theorem completeFourState_stateMultiplicity
    {P : ColoredShape} (hP : CompleteFourState P) (s : TrominoState) :
    stateMultiplicity P s = 1 := by
  rcases completeFourState_existsUnique_cell hP s with
    ⟨c, hc, hunique⟩
  have hfilter : P.shape.filter (fun d => P.color d = s) = {c} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hd
      exact hunique d hd
    · intro hd
      subst d
      exact hc
  rw [stateMultiplicity, hfilter]
  simp

/-- Distinct cells of a complete four-state shape have distinct states. -/
def PairwiseDistinctOnShape (P : ColoredShape) : Prop :=
  ∀ ⦃c₁ c₂ : Cell⦄,
    c₁ ∈ P.shape → c₂ ∈ P.shape → P.color c₁ = P.color c₂ → c₁ = c₂

theorem completeFourState_pairwiseDistinct
    {P : ColoredShape} (hP : CompleteFourState P) :
    PairwiseDistinctOnShape P := by
  intro c₁ c₂ hc₁ hc₂ hcolor
  rcases completeFourState_existsUnique_cell hP (P.color c₁) with
    ⟨c, hc, hunique⟩
  have hc₁' : c₁ ∈ P.shape ∧ P.color c₁ = P.color c₁ := ⟨hc₁, rfl⟩
  have hc₂' : c₂ ∈ P.shape ∧ P.color c₂ = P.color c₁ :=
    ⟨hc₂, hcolor.symm⟩
  exact (hunique c₁ hc₁').trans (hunique c₂ hc₂').symm

/-- Apply one exchange delta to every state of a colored shape. -/
def uniformExchangeColoredShape
    (delta : TrominoState) (P : ColoredShape) : ColoredShape :=
  { shape := P.shape
    color := fun c => uniformExchange delta P.color c }

@[simp] theorem uniformExchangeColoredShape_shape
    (delta : TrominoState) (P : ColoredShape) :
    (uniformExchangeColoredShape delta P).shape = P.shape := rfl

@[simp] theorem uniformExchangeColoredShape_color
    (delta : TrominoState) (P : ColoredShape) (c : Cell) :
    (uniformExchangeColoredShape delta P).color c =
      uniformExchange delta P.color c := rfl

/-- Uniform exchange preserves equality and inequality of stored states. -/
theorem uniformExchangeColoredShape_ne_iff
    (delta : TrominoState) (P : ColoredShape) (c₁ c₂ : Cell) :
    (uniformExchangeColoredShape delta P).color c₁ ≠
        (uniformExchangeColoredShape delta P).color c₂ ↔
      P.color c₁ ≠ P.color c₂ := by
  exact uniformExchange_ne_iff delta P.color c₁ c₂

/-- Uniform exchange reindexes state multiplicity by the same exchange. -/
theorem stateMultiplicity_uniformExchangeColoredShape
    (delta : TrominoState) (P : ColoredShape) (s : TrominoState) :
    stateMultiplicity (uniformExchangeColoredShape delta P) s =
      stateMultiplicity P (exchange delta s) := by
  apply congrArg Finset.card
  ext c
  constructor
  · intro hc
    have hmem := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨hmem.1, ?_⟩
    have h := congrArg (exchange delta) hmem.2
    simpa [uniformExchange, exchange_self_inverse] using h
  · intro hc
    have hmem := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨hmem.1, ?_⟩
    have h := congrArg (exchange delta) hmem.2
    simpa [uniformExchange, exchange_self_inverse] using h

/-- Complete four-state structure is preserved by a uniform exchange. -/
theorem completeFourState_uniformExchangeColoredShape
    {P : ColoredShape} (hP : CompleteFourState P) (delta : TrominoState) :
    CompleteFourState (uniformExchangeColoredShape delta P) := by
  refine ⟨?_, ?_⟩
  · simp [uniformExchangeColoredShape, hP.1]
  · ext s
    constructor
    · intro hs
      simp
    · intro _
      have hs' : exchange delta s ∈ P.shape.image P.color := by
        rw [hP.2]
        simp
      rcases Finset.mem_image.mp hs' with ⟨c, hc, hcs⟩
      apply Finset.mem_image.mpr
      refine ⟨c, hc, ?_⟩
      change exchange delta (P.color c) = s
      rw [hcs]
      exact exchange_self_inverse delta s

/-- Pairwise state distinctness is preserved by a uniform exchange. -/
theorem pairwiseDistinct_uniformExchangeColoredShape
    {P : ColoredShape} (hP : PairwiseDistinctOnShape P) (delta : TrominoState) :
    PairwiseDistinctOnShape (uniformExchangeColoredShape delta P) := by
  intro c₁ c₂ hc₁ hc₂ hcolor
  apply hP hc₁ hc₂
  exact (uniformExchange_eq_iff delta P.color c₁ c₂).mp hcolor

/-- Grid-neighbor relation for the local colored-cell layer. -/
def gridAdjacent (c₁ c₂ : Cell) : Prop :=
  (c₁.1 = c₂.1 ∧ (c₁.2 + 1 = c₂.2 ∨ c₂.2 + 1 = c₁.2)) ∨
    (c₁.2 = c₂.2 ∧ (c₁.1 + 1 = c₂.1 ∨ c₂.1 + 1 = c₁.1))

/-- Properness restricted to adjacent cells of the given finite shape. -/
def internalProper (P : ColoredShape) : Prop :=
  ∀ ⦃c₁ c₂ : Cell⦄,
    c₁ ∈ P.shape → c₂ ∈ P.shape → gridAdjacent c₁ c₂ →
      P.color c₁ ≠ P.color c₂

theorem gridAdjacent_ne {c₁ c₂ : Cell} (h : gridAdjacent c₁ c₂) : c₁ ≠ c₂ := by
  intro heq
  subst c₂
  rcases h with h | h
  · rcases h with ⟨_, h | h⟩ <;> omega
  · rcases h with ⟨_, h | h⟩ <;> omega

/-- Internal properness is preserved by a uniform exchange. -/
theorem internalProper_uniformExchangeColoredShape
    {P : ColoredShape} (hP : internalProper P) (delta : TrominoState) :
    internalProper (uniformExchangeColoredShape delta P) := by
  intro c₁ c₂ hc₁ hc₂ hadj hcolor
  apply hP hc₁ hc₂ hadj
  exact (uniformExchange_eq_iff delta P.color c₁ c₂).mp hcolor

/-- Fixed algebraic state assignment on the four coordinates of `block2`. -/
def atomicColor (c : Cell) : TrominoState :=
  if c = (0, 0) then (0, 0)
  else if c = (1, 0) then (1, 0)
  else if c = (0, 1) then (0, 1)
  else (1, 1)

/-- The canonical four-state coloring of the existing 2x2 footprint. -/
def atomicFourColorCell : ColoredShape :=
  { shape := block2
    color := atomicColor }

@[simp] theorem atomicFourColorCell_shape :
    atomicFourColorCell.shape = block2 := rfl

theorem atomicFourColorCell_card : atomicFourColorCell.shape.card = 4 := by
  simpa [atomicFourColorCell, area] using area_block2

theorem atomicFourColorCell_complete :
    CompleteFourState atomicFourColorCell := by
  refine ⟨by decide, ?_⟩
  ext s
  fin_cases s <;> decide

theorem atomicFourColorCell_pairwiseDistinct :
    PairwiseDistinctOnShape atomicFourColorCell :=
  completeFourState_pairwiseDistinct atomicFourColorCell_complete

theorem atomicFourColorCell_internalProper :
    internalProper atomicFourColorCell := by
  intro c₁ c₂ hc₁ hc₂ hadj hcolor
  exact gridAdjacent_ne hadj
    (atomicFourColorCell_pairwiseDistinct hc₁ hc₂ hcolor)

/-- Zero exchange leaves every colored shape unchanged. -/
theorem uniformExchangeColoredShape_zero (P : ColoredShape) :
    uniformExchangeColoredShape 0 P = P := by
  apply ColoredShape.ext'
  · rfl
  · funext c
    simp [uniformExchangeColoredShape, uniformExchange]

/-- Every exchange is an involution on colored shapes. -/
theorem uniformExchangeColoredShape_involutive
    (delta : TrominoState) (P : ColoredShape) :
    uniformExchangeColoredShape delta
        (uniformExchangeColoredShape delta P) = P := by
  apply ColoredShape.ext'
  · rfl
  · funext c
    simp [uniformExchangeColoredShape, uniformExchange,
      exchange_self_inverse]

/-- The canonical cell remains complete after any uniform exchange. -/
theorem atomicFourColorCell_exchange_complete (delta : TrominoState) :
    CompleteFourState
      (uniformExchangeColoredShape delta atomicFourColorCell) :=
  completeFourState_uniformExchangeColoredShape
    atomicFourColorCell_complete delta

/-- Different deltas give different colorings on every nonempty shape. -/
theorem uniformExchangeColoredShape_injective_of_nonempty
    {P : ColoredShape} (hP : P.shape.Nonempty) :
    Function.Injective (fun delta => uniformExchangeColoredShape delta P) := by
  intro delta₁ delta₂ hdelta
  rcases hP with ⟨c, hc⟩
  have hcolor := congrArg (fun Q : ColoredShape => Q.color c) hdelta
  have hsum : P.color c + delta₁ = P.color c + delta₂ := by
    simpa [uniformExchangeColoredShape, uniformExchange, exchange] using hcolor
  exact add_left_cancel hsum

end DkMath.Tromino
