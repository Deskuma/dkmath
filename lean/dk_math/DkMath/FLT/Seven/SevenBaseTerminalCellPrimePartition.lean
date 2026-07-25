/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalGlobalCoordinateEquations

#print "file: DkMath.FLT.Seven.SevenBaseTerminalCellPrimePartition"

namespace DkMath.FLT.Seven

/-- Every cell of the positive terminal routing board is nonzero. -/
theorem AwaySevenBaseTerminalRoutingPacket.routingCell_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    awaySevenBaseTerminalRoutingCell packet coordinate ≠ 0 := by
  have hunselectedPos :
      0 < awaySevenBaseTerminalUnselectedEndpointNat p.row y z := by
    cases p.row <;>
      simp only [awaySevenBaseTerminalUnselectedEndpointNat]
    · exact r.cubic.endpointTriple.second_pos
    · exact r.cubic.endpointTriple.first_pos
    · exact r.cubic.endpointTriple.first_pos
  have hcompanionPos :
      0 < awaySevenBaseTerminalCompanionEndpointNat p.row y z := by
    cases p.row <;>
      simp only [awaySevenBaseTerminalCompanionEndpointNat]
    · exact r.cubic.endpointTriple.third_pos
    · exact r.cubic.endpointTriple.third_pos
    · exact r.cubic.endpointTriple.second_pos
  rcases coordinate with ⟨row, column⟩
  cases row <;> cases column <;>
    simp only [awaySevenBaseTerminalRoutingCell]
  all_goals
    intro h
  · have hrow := packet.routing.row1
    rw [h] at hrow
    simp only [zero_mul] at hrow
    exact packet.core.carrier.carrierUnit_pos.ne' hrow
  · have hrow := packet.routing.row1
    rw [h] at hrow
    simp only [zero_mul, mul_zero] at hrow
    exact packet.core.carrier.carrierUnit_pos.ne' hrow
  · have hrow := packet.routing.row1
    rw [h] at hrow
    simp only [mul_zero] at hrow
    exact packet.core.carrier.carrierUnit_pos.ne' hrow
  · have hrow := packet.routing.row2
    rw [h] at hrow
    simp only [zero_mul] at hrow
    exact hunselectedPos.ne' hrow
  · have hrow := packet.routing.row2
    rw [h] at hrow
    simp only [zero_mul, mul_zero] at hrow
    exact hunselectedPos.ne' hrow
  · have hrow := packet.routing.row2
    rw [h] at hrow
    simp only [mul_zero] at hrow
    exact hunselectedPos.ne' hrow
  · have hrow := packet.routing.row3
    rw [h] at hrow
    simp only [zero_mul] at hrow
    exact hcompanionPos.ne' hrow
  · have hrow := packet.routing.row3
    rw [h] at hrow
    simp only [zero_mul, mul_zero] at hrow
    exact hcompanionPos.ne' hrow
  · have hrow := packet.routing.row3
    rw [h] at hrow
    simp only [mul_zero] at hrow
    exact hcompanionPos.ne' hrow

private theorem not_dvd_second_of_cell_coprime {q a b : ℕ}
    (hq : Nat.Prime q) (hab : Nat.Coprime a b) (ha : q ∣ a) :
    ¬ q ∣ b := by
  intro hb
  exact hq.not_dvd_one (by simpa [hab.gcd_eq_one] using Nat.dvd_gcd ha hb)

/-- For a prime, divisibility of one fixed routing cell already determines the
complete row/column coordinate predicate. -/
theorem AwaySevenBaseTerminalRoutingPacket.primeCellCoordinate_iff
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate)
    (hq : Nat.Prime q) :
    AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q ↔
      q ∣ awaySevenBaseTerminalRoutingCell packet coordinate := by
  constructor
  · exact packet.primeCellCoordinate_dvd_routingCell coordinate
  · intro hcell
    rcases coordinate with ⟨row, column⟩
    cases row <;> cases column
    all_goals
      simp only [AwaySevenBaseTerminalPrimeCellCoordinate,
        awaySevenBaseTerminalFactorRowValue,
        AwaySevenBaseTerminalFixedPrimeCoordinate,
        awaySevenBaseTerminalRoutingCell] at hcell ⊢
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row1_coprime.1 hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row1_coprime.2.1 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c11_dvd_row1
      · exact hcell.trans packet.routing.c11_dvd_col1
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row1_coprime.1.symm hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row1_coprime.2.2 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c12_dvd_row1
      · exact hcell.trans packet.routing.c12_dvd_col2
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row1_coprime.2.1.symm hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row1_coprime.2.2.symm hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c13_dvd_row1
      · exact hcell.trans packet.routing.c13_dvd_col3
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row2_coprime.1 hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row2_coprime.2.1 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c21_dvd_row2
      · exact hcell.trans packet.routing.c21_dvd_col1
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row2_coprime.1.symm hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row2_coprime.2.2 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c22_dvd_row2
      · exact hcell.trans packet.routing.c22_dvd_col2
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row2_coprime.2.1.symm hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row2_coprime.2.2.symm hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c23_dvd_row2
      · exact hcell.trans packet.routing.c23_dvd_col3
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row3_coprime.1 hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row3_coprime.2.1 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c31_dvd_row3
      · exact hcell.trans packet.routing.c31_dvd_col1
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row3_coprime.1.symm hcell,
        not_dvd_second_of_cell_coprime hq packet.routing.row3_coprime.2.2 hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c32_dvd_row3
      · exact hcell.trans packet.routing.c32_dvd_col2
    · refine ⟨?_, hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row3_coprime.2.1.symm hcell,
        not_dvd_second_of_cell_coprime hq
          packet.routing.row3_coprime.2.2.symm hcell,
        ?_⟩
      · exact hcell.trans packet.routing.c33_dvd_row3
      · exact hcell.trans packet.routing.c33_dvd_col3

/-- Every terminal routing cell divides the complete cubic-root load. -/
theorem AwaySevenBaseTerminalRoutingPacket.routingCell_dvd_cubicRootLoad
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    awaySevenBaseTerminalRoutingCell packet coordinate ∣
      awaySevenBaseTerminalCubicRootLoad r := by
  have hv :
      r.cubic.rootTriple.vPart ∣
        r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
          r.cubic.rootTriple.rightPart :=
    ⟨r.cubic.rootTriple.leftPart * r.cubic.rootTriple.rightPart, by ring⟩
  have hl :
      r.cubic.rootTriple.leftPart ∣
        r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
          r.cubic.rootTriple.rightPart :=
    ⟨r.cubic.rootTriple.vPart * r.cubic.rootTriple.rightPart, by ring⟩
  have hr :
      r.cubic.rootTriple.rightPart ∣
        r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
          r.cubic.rootTriple.rightPart :=
    ⟨r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart, by ring⟩
  rcases coordinate with ⟨row, column⟩
  cases row <;> cases column <;>
    simp only [awaySevenBaseTerminalRoutingCell,
      awaySevenBaseTerminalCubicRootLoad]
  · exact packet.routing.c11_dvd_col1.trans hv
  · exact packet.routing.c12_dvd_col2.trans hl
  · exact packet.routing.c13_dvd_col3.trans hr
  · exact packet.routing.c21_dvd_col1.trans hv
  · exact packet.routing.c22_dvd_col2.trans hl
  · exact packet.routing.c23_dvd_col3.trans hr
  · exact packet.routing.c31_dvd_col1.trans hv
  · exact packet.routing.c32_dvd_col2.trans hl
  · exact packet.routing.c33_dvd_col3.trans hr

/-- The canonical prime support of one of the nine terminal cells. -/
def awaySevenBaseTerminalCellPrimeSupport
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : Finset ℕ :=
  Nat.primeFactors (awaySevenBaseTerminalRoutingCell packet coordinate)

theorem mem_awaySevenBaseTerminalCellPrimeSupport_iff
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {coordinate : AwaySevenBaseTerminalCellCoordinate} :
    q ∈ awaySevenBaseTerminalCellPrimeSupport packet coordinate ↔
      Nat.Prime q ∧
        AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q := by
  rw [awaySevenBaseTerminalCellPrimeSupport, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hcell, _⟩
    exact ⟨hq, (packet.primeCellCoordinate_iff coordinate hq).mpr hcell⟩
  · rintro ⟨hq, hcoordinate⟩
    exact ⟨hq,
      (packet.primeCellCoordinate_iff coordinate hq).mp hcoordinate,
      packet.routingCell_ne_zero coordinate⟩

/-- The prime-power product internal to one terminal cell. -/
def awaySevenBaseTerminalCellCombinedModulus
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : ℕ :=
  ∏ q : (awaySevenBaseTerminalCellPrimeSupport packet coordinate),
    q.1 ^ padicValNat q.1
      (awaySevenBaseTerminalRoutingCell packet coordinate)

/-- The complete prime-power product of a cell reconstructs exactly that cell,
including the value-one cells whose support is empty. -/
theorem awaySevenBaseTerminalCellCombinedModulus_eq_routingCell
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    awaySevenBaseTerminalCellCombinedModulus packet coordinate =
      awaySevenBaseTerminalRoutingCell packet coordinate := by
  rw [awaySevenBaseTerminalCellCombinedModulus]
  change
    (∏ q :
        (awaySevenBaseTerminalRoutingCell packet coordinate).primeFactors,
      q.1 ^ padicValNat q.1
        (awaySevenBaseTerminalRoutingCell packet coordinate)) =
      awaySevenBaseTerminalRoutingCell packet coordinate
  calc
    _ = ∏ q :
        (awaySevenBaseTerminalRoutingCell packet coordinate).primeFactors,
        q.1 ^ (awaySevenBaseTerminalRoutingCell packet coordinate).factorization
          q.1 := by
      apply Fintype.prod_congr
      intro q
      rw [Nat.factorization_def _
        (Nat.prime_of_mem_primeFactors q.2)]
    _ = awaySevenBaseTerminalRoutingCell packet coordinate :=
      (Nat.prod_pow_primeFactors_factorization
        (packet.routingCell_ne_zero coordinate)).symm

/-- TERM-005 partition packet. Every prime of the full load is assigned to its
unique cell, and each cell has an exact prime-power modulus reconstruction. -/
structure AwaySevenBaseTerminalCellPrimePartitionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    Type where
  coordinateOf :
    AwaySevenBaseTerminalPrimeIndex r →
      AwaySevenBaseTerminalCellCoordinate
  coordinate_spec :
    ∀ q, AwaySevenBaseTerminalPrimeCellCoordinate packet (coordinateOf q) q.1
  coordinate_unique :
    ∀ q coordinate,
      AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q.1 →
        coordinate = coordinateOf q
  cell_modulus_exact :
    ∀ coordinate,
      awaySevenBaseTerminalCellCombinedModulus packet coordinate =
        awaySevenBaseTerminalRoutingCell packet coordinate

/-- Choose the already proved unique cell coordinate for every supported
terminal prime. -/
noncomputable def
    AwaySevenBaseTerminalRoutingPacket.cellPrimePartitionPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) :
    AwaySevenBaseTerminalCellPrimePartitionPacket packet := by
  let coordinateOf :=
    fun q : AwaySevenBaseTerminalPrimeIndex r =>
      Classical.choose
        (packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate
          q.prime q.dvd_cubicRootLoad).2
  refine {
    coordinateOf := coordinateOf
    coordinate_spec := ?_
    coordinate_unique := ?_
    cell_modulus_exact :=
      awaySevenBaseTerminalCellCombinedModulus_eq_routingCell packet }
  · intro q
    exact (Classical.choose_spec
      (packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate
        q.prime q.dvd_cubicRootLoad).2).1
  · intro q coordinate hcoordinate
    exact (Classical.choose_spec
      (packet.prime_dvd_cubicRootLoad_unique_global_cellCoordinate
        q.prime q.dvd_cubicRootLoad).2).2 coordinate hcoordinate

end DkMath.FLT.Seven
