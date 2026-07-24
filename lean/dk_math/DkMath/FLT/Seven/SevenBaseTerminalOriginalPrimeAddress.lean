/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalOriginalRoutingProjection

#print "file: DkMath.FLT.Seven.SevenBaseTerminalOriginalPrimeAddress"

namespace DkMath.FLT.Seven

private theorem exists_rootColumn_cell_of_prime_dvd_endpointFactor
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q) (row : EndpointRoutingRow)
    (hrow : q ∣ endpointRoutingFactorNat y z row) :
    ∃ column : RootRoutingColumn,
      q ∣ routingCell r.routing row column := by
  cases row with
  | y =>
      have hproduct : q ∣ r.routing.c11 * r.routing.c12 * r.routing.c13 := by
        rw [← r.routing.row1]
        simpa [endpointRoutingFactorNat] using hrow
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h12 | h13
      · rcases (Nat.Prime.dvd_mul hq).mp h12 with h11 | h12
        · exact ⟨.sevenV, by simpa [routingCell] using h11⟩
        · exact ⟨.leftCubic, by simpa [routingCell] using h12⟩
      · exact ⟨.rightCubic, by simpa [routingCell] using h13⟩
  | z =>
      have hproduct : q ∣ r.routing.c21 * r.routing.c22 * r.routing.c23 := by
        rw [← r.routing.row2]
        simpa [endpointRoutingFactorNat] using hrow
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h22 | h23
      · rcases (Nat.Prime.dvd_mul hq).mp h22 with h21 | h22
        · exact ⟨.sevenV, by simpa [routingCell] using h21⟩
        · exact ⟨.leftCubic, by simpa [routingCell] using h22⟩
      · exact ⟨.rightCubic, by simpa [routingCell] using h23⟩
  | sum =>
      have hproduct : q ∣ r.routing.c31 * r.routing.c32 * r.routing.c33 := by
        rw [← r.routing.row3]
        simpa [endpointRoutingFactorNat] using hrow
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h32 | h33
      · rcases (Nat.Prime.dvd_mul hq).mp h32 with h31 | h32
        · exact ⟨.sevenV, by simpa [routingCell] using h31⟩
        · exact ⟨.leftCubic, by simpa [routingCell] using h32⟩
      · exact ⟨.rightCubic, by simpa [routingCell] using h33⟩

private theorem exists_endpointRow_cell_of_prime_dvd_rootFactor
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q) (column : RootRoutingColumn)
    (hcolumn : q ∣ rootRoutingFactorNat r column) :
    ∃ row : EndpointRoutingRow,
      q ∣ routingCell r.routing row column := by
  cases column with
  | sevenV =>
      have hproduct : q ∣ r.routing.c11 * r.routing.c21 * r.routing.c31 := by
        rw [← r.routing.col1]
        simpa [rootRoutingFactorNat] using hcolumn
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h21 | h31
      · rcases (Nat.Prime.dvd_mul hq).mp h21 with h11 | h21
        · exact ⟨.y, by simpa [routingCell] using h11⟩
        · exact ⟨.z, by simpa [routingCell] using h21⟩
      · exact ⟨.sum, by simpa [routingCell] using h31⟩
  | leftCubic =>
      have hproduct : q ∣ r.routing.c12 * r.routing.c22 * r.routing.c32 := by
        rw [← r.routing.col2]
        simpa [rootRoutingFactorNat] using hcolumn
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h22 | h32
      · rcases (Nat.Prime.dvd_mul hq).mp h22 with h12 | h22
        · exact ⟨.y, by simpa [routingCell] using h12⟩
        · exact ⟨.z, by simpa [routingCell] using h22⟩
      · exact ⟨.sum, by simpa [routingCell] using h32⟩
  | rightCubic =>
      have hproduct : q ∣ r.routing.c13 * r.routing.c23 * r.routing.c33 := by
        rw [← r.routing.col3]
        simpa [rootRoutingFactorNat] using hcolumn
      rcases (Nat.Prime.dvd_mul hq).mp hproduct with h23 | h33
      · rcases (Nat.Prime.dvd_mul hq).mp h23 with h13 | h23
        · exact ⟨.y, by simpa [routingCell] using h13⟩
        · exact ⟨.z, by simpa [routingCell] using h23⟩
      · exact ⟨.sum, by simpa [routingCell] using h33⟩

/-- If a prime divides one original endpoint factor and one original root factor,
then it divides their unique intersection cell in the original routing grid. -/
theorem AwayCubicRoutingPacket.prime_dvd_routingCell_of_dvd_factors
    {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z)
    (hq : Nat.Prime q) (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
    (hrow : q ∣ endpointRoutingFactorNat y z row)
    (hcolumn : q ∣ rootRoutingFactorNat r column) :
    q ∣ routingCell r.routing row column := by
  rcases exists_rootColumn_cell_of_prime_dvd_endpointFactor r hq row hrow with
    ⟨rowColumn, hrowCell⟩
  rcases exists_endpointRow_cell_of_prime_dvd_rootFactor r hq column hcolumn with
    ⟨columnRow, hcolumnCell⟩
  have hunique := r.prime_address_unique hq hrowCell hcolumnCell
  simpa [hunique.2] using hrowCell

/-- A terminal prime-cell coordinate determines an actual specialized prime
address on the original routing grid. -/
def AwaySevenBaseTerminalRoutingPacket.originalPrimeAddressOfCoordinate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) {q : ℕ}
    (hq : Nat.Prime q)
    (hcoordinate : AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q) :
    AwayRoutingPrimeAddress r := by
  let row := awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row
  let column := awaySevenBaseTerminalOriginalRootColumn coordinate.column
  have hrow : q ∣ endpointRoutingFactorNat y z row := by
    simpa [row] using
      packet.primeCellCoordinate_dvd_originalEndpointFactor coordinate hcoordinate
  have hcolumn : q ∣ rootRoutingFactorNat r column := by
    simpa [column] using
      packet.primeCellCoordinate_dvd_originalRootFactor coordinate hcoordinate
  have hcell : q ∣ routingCell r.routing row column :=
    r.prime_dvd_routingCell_of_dvd_factors hq row column hrow hcolumn
  exact {
    q := q
    q_prime := hq
    row := row
    column := column
    q_dvd_cell := hcell
    unique := by
      intro row' column' h
      have hunique := r.prime_address_unique hq hcell h
      exact ⟨hunique.1.symm, hunique.2.symm⟩ }

/-- A projection packet canonically re-enters the original specialized
prime-address layer. -/
def AwaySevenBaseTerminalOriginalRoutingPrimeProjection.toOriginalPrimeAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    (projection : AwaySevenBaseTerminalOriginalRoutingPrimeProjection packet) :
    AwayRoutingPrimeAddress r :=
  packet.originalPrimeAddressOfCoordinate projection.coordinate
    projection.q_prime projection.prime_cell

/-- Every prime dividing the terminal cubic root load is realized as a
non-seven specialized prime address on the original routing grid. -/
theorem AwaySevenBaseTerminalRoutingPacket
    .exists_originalPrimeAddress_of_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    {q : ℕ} (hq : Nat.Prime q)
    (hqLoad : q ∣ awaySevenBaseTerminalCubicRootLoad r) :
    ∃ address : AwayRoutingPrimeAddress r,
      address.q = q ∧ address.q ≠ 7 := by
  have hglobal :=
    packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate hq hqLoad
  rcases hglobal.2 with ⟨coordinate, hcoordinate, _⟩
  let address := packet.originalPrimeAddressOfCoordinate coordinate hq hcoordinate
  refine ⟨address, rfl, ?_⟩
  change q ≠ 7
  exact hglobal.1

end DkMath.FLT.Seven
