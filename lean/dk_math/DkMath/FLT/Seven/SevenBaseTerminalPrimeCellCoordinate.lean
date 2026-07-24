/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalPrimeCoordinate

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPrimeCellCoordinate"

namespace DkMath.FLT.Seven

/-- One of the nine explicit cells on a fixed terminal routing board. -/
structure AwaySevenBaseTerminalCellCoordinate : Type where
  row : AwaySevenBaseTerminalFactorRow
  column : AwaySevenBaseTerminalRootColumn
  deriving DecidableEq, Repr

/-- The routing-cell value selected by an explicit terminal row/column
coordinate. -/
def awaySevenBaseTerminalRoutingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : ℕ :=
  match coordinate.row with
  | .carrier =>
      match coordinate.column with
      | .vPart => packet.routing.c11
      | .leftPart => packet.routing.c12
      | .rightPart => packet.routing.c13
  | .unselected =>
      match coordinate.column with
      | .vPart => packet.routing.c21
      | .leftPart => packet.routing.c22
      | .rightPart => packet.routing.c23
  | .companion =>
      match coordinate.column with
      | .vPart => packet.routing.c31
      | .leftPart => packet.routing.c32
      | .rightPart => packet.routing.c33

/-- A flattened terminal prime coordinate records its endpoint-side row and its
single explicit routing cell on the common fixed board. -/
def AwaySevenBaseTerminalPrimeCellCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) (q : ℕ) : Prop :=
  q ∣ awaySevenBaseTerminalFactorRowValue packet coordinate.row ∧
    AwaySevenBaseTerminalFixedPrimeCoordinate packet
      coordinate.row coordinate.column q

/-- A global flattened prime coordinate is the unique one of the nine terminal
routing cells carrying the prime. -/
def AwaySevenBaseTerminalGlobalPrimeCellCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (q : ℕ) : Prop :=
  ∃! coordinate : AwaySevenBaseTerminalCellCoordinate,
    AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q

/-- An explicit fixed row/column coordinate recovers the corresponding
row-local disjunctive prime address. -/
theorem AwaySevenBaseTerminalRoutingPacket.fixedPrimeAddress_of_fixedPrimeCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow)
    (column : AwaySevenBaseTerminalRootColumn) {q : ℕ}
    (h : AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q) :
    AwaySevenBaseTerminalFixedPrimeAddress packet row q := by
  cases row <;> cases column <;>
    simp only [AwaySevenBaseTerminalFixedPrimeCoordinate] at h <;>
    simp only [AwaySevenBaseTerminalFixedPrimeAddress]
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The explicit coordinate proposition exposes divisibility of the selected
routing-cell accessor. -/
theorem AwaySevenBaseTerminalRoutingPacket.fixedPrimeCoordinate_dvd_routingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (row : AwaySevenBaseTerminalFactorRow)
    (column : AwaySevenBaseTerminalRootColumn) {q : ℕ}
    (h : AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q) :
    q ∣ awaySevenBaseTerminalRoutingCell packet ⟨row, column⟩ := by
  cases row <;> cases column <;>
    simp only [AwaySevenBaseTerminalFixedPrimeCoordinate] at h <;>
    simpa [awaySevenBaseTerminalRoutingCell] using h.1

/-- A flattened prime-cell coordinate directly exposes divisibility of its
selected routing cell. -/
theorem AwaySevenBaseTerminalRoutingPacket.primeCellCoordinate_dvd_routingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (h : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    q ∣ awaySevenBaseTerminalRoutingCell packet coordinate := by
  exact packet.fixedPrimeCoordinate_dvd_routingCell
    coordinate.row coordinate.column h.2

/-- Every prime dividing the terminal cubic root load has one unique flattened
coordinate among the nine cells of the fixed terminal routing board. -/
theorem AwaySevenBaseTerminalRoutingPacket.prime_dvd_cubicRootLoad_unique_global_cellCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    q ≠ 7 ∧ AwaySevenBaseTerminalGlobalPrimeCellCoordinate packet q := by
  have hglobal :=
    packet.prime_dvd_cubicRootLoad_unique_global_coordinate hq hqLoad
  refine ⟨hglobal.1, ?_⟩
  rcases hglobal.2 with ⟨row, hrow, hrowUnique⟩
  rcases hrow.2.2 with ⟨column, hcolumn, hcolumnUnique⟩
  let coordinate : AwaySevenBaseTerminalCellCoordinate := ⟨row, column⟩
  refine ⟨coordinate, ?_, ?_⟩
  · simpa [AwaySevenBaseTerminalPrimeCellCoordinate, coordinate] using
      (show q ∣ awaySevenBaseTerminalFactorRowValue packet row ∧
          AwaySevenBaseTerminalFixedPrimeCoordinate packet row column q from
        ⟨hrow.1, hcolumn⟩)
  · intro other hother
    rcases other with ⟨otherRow, otherColumn⟩
    change q ∣ awaySevenBaseTerminalFactorRowValue packet otherRow ∧
      AwaySevenBaseTerminalFixedPrimeCoordinate packet
        otherRow otherColumn q at hother
    have hotherAddress :=
      packet.fixedPrimeAddress_of_fixedPrimeCoordinate
        otherRow otherColumn hother.2
    have hotherColumns :=
      packet.existsUnique_rootColumn_of_fixedPrimeAddress
        otherRow hotherAddress
    have hrowEq : otherRow = row :=
      hrowUnique otherRow ⟨hother.1, hotherAddress, hotherColumns⟩
    subst otherRow
    have hcolumnEq : otherColumn = column :=
      hcolumnUnique otherColumn hother.2
    subst otherColumn
    rfl

end DkMath.FLT.Seven
