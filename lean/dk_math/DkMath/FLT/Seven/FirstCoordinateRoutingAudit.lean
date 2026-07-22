/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.RoutingSevenPivot

#print "file: DkMath.FLT.Seven.FirstCoordinateRoutingAudit"

namespace DkMath.FLT.Seven

set_option linter.unnecessarySeqFocus false

theorem intCast_dvd_of_dvd_natAbs {d : ℕ} {a : ℤ}
    (h : d ∣ Int.natAbs a) : (d : ℤ) ∣ a :=
  Int.natCast_dvd.mpr h

private theorem cell_dvd_leftCubic {x y z d : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (h : d ∣ r.cubic.rootTriple.leftPart) :
    (d : ℤ) ∣ seventhPowerSndLeftCubic
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
  apply intCast_dvd_of_dvd_natAbs
  rwa [← r.cubic.rootTriple.leftPart_eq]

private theorem cell_dvd_rightCubic {x y z d : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (h : d ∣ r.cubic.rootTriple.rightPart) :
    (d : ℤ) ∣ seventhPowerSndRightCubic
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
  apply intCast_dvd_of_dvd_natAbs
  rwa [← r.cubic.rootTriple.rightPart_eq]

private theorem fst_eq_for_routing {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    cyclotomicSevenFst (z : ℤ) (y : ℤ) = seventhPowerFst
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd :=
  r.cubic.rootTriple.normal.fst_eq

structure AwayFirstCoordinateRoutingConstraints {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  rootSector : AwayRootResidueSector x y z r.cubic.transfer.normal
  sevenPivot : AwayRoutingSevenPivot r
  c12_constraint : (r.routing.c12 : ℤ) ∣
    (z : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd
  c22_constraint : (r.routing.c22 : ℤ) ∣
    49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd - (y : ℤ) ^ 3
  c32_constraint : (r.routing.c32 : ℤ) ∣
    49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd - (y : ℤ) ^ 3
  c13_constraint : (r.routing.c13 : ℤ) ∣
    (z : ℤ) ^ 3 - 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd
  c23_constraint : (r.routing.c23 : ℤ) ∣
    (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd
  c33_constraint : (r.routing.c33 : ℤ) ∣
    (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd
  c11_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c11 →
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 - (z : ℤ) ^ 3
  c21_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c21 →
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3
  c31_nonSeven_constraint : ∀ q, Nat.Prime q → q ≠ 7 → q ∣ r.routing.c31 →
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3

private theorem left_constraint_y {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c12 : ℤ) ∣
      (z : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        leftFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
  have hrow : (r.routing.c12 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c12_dvd_row1).trans
      (leftEndpoint_dvd_fst_sub_right_cube (z : ℤ) (y : ℤ))
  have hcol := (cell_dvd_leftCubic r r.routing.c12_dvd_col2).trans
    (leftCubic_dvd_fst_add_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hcol.sub hrow using 1 <;> ring

private theorem left_constraint_z {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c22 : ℤ) ∣
      49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        leftFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd - (y : ℤ) ^ 3 := by
  have hrow : (r.routing.c22 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c22_dvd_row2).trans
      (rightEndpoint_dvd_fst_add_left_cube (z : ℤ) (y : ℤ))
  have hcol := (cell_dvd_leftCubic r r.routing.c22_dvd_col2).trans
    (leftCubic_dvd_fst_add_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hcol.sub hrow using 1 <;> ring

private theorem left_constraint_sum {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c32 : ℤ) ∣
      49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        leftFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd - (y : ℤ) ^ 3 := by
  have hrow : (r.routing.c32 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c32_dvd_row3).trans (by
      convert endpointSum_dvd_fst_add_left_cube (z : ℤ) (y : ℤ) using 1 <;> norm_num
      ring)
  have hcol := (cell_dvd_leftCubic r r.routing.c32_dvd_col2).trans
    (leftCubic_dvd_fst_add_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hcol.sub hrow using 1 <;> ring

private theorem right_constraint_y {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c13 : ℤ) ∣
      (z : ℤ) ^ 3 - 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        rightFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
  have hrow : (r.routing.c13 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c13_dvd_row1).trans
      (leftEndpoint_dvd_fst_sub_right_cube (z : ℤ) (y : ℤ))
  have hcol := (cell_dvd_rightCubic r r.routing.c13_dvd_col3).trans
    (rightCubic_dvd_fst_sub_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hcol.sub hrow using 1 <;> ring

private theorem right_constraint_z {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c23 : ℤ) ∣
      (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        rightFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
  have hrow : (r.routing.c23 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c23_dvd_row2).trans
      (rightEndpoint_dvd_fst_add_left_cube (z : ℤ) (y : ℤ))
  have hcol := (cell_dvd_rightCubic r r.routing.c23_dvd_col3).trans
    (rightCubic_dvd_fst_sub_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hrow.sub hcol using 1 <;> ring

private theorem right_constraint_sum {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : (r.routing.c33 : ℤ) ∣
      (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
        rightFstCorrection r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd := by
  have hrow : (r.routing.c33 : ℤ) ∣
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr r.routing.c33_dvd_row3).trans (by
      convert endpointSum_dvd_fst_add_left_cube (z : ℤ) (y : ℤ) using 1 <;> norm_num
      ring)
  have hcol := (cell_dvd_rightCubic r r.routing.c33_dvd_col3).trans
    (rightCubic_dvd_fst_sub_correction
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  rw [← fst_eq_for_routing r] at hcol
  convert hrow.sub hcol using 1 <;> ring

private theorem prime_dvd_rootSnd_of_dvd_col1 {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q) (hq7 : q ≠ 7)
    {c : ℕ} (hc : c ∣ 7 * r.cubic.rootTriple.vPart) (hqc : q ∣ c) :
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
  have hqprod := hqc.trans hc
  have hnq7 : ¬ q ∣ 7 := by
    intro h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq7 hqeq
  have hqv : q ∣ r.cubic.rootTriple.vPart :=
    (hq.dvd_mul.mp hqprod).resolve_left hnq7
  apply intCast_dvd_of_dvd_natAbs
  rwa [← r.cubic.rootTriple.vPart_eq]

private theorem col1_constraint_y {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hqc : q ∣ r.routing.c11) :
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 - (z : ℤ) ^ 3 := by
  have hv := prime_dvd_rootSnd_of_dvd_col1 r hq hq7 r.routing.c11_dvd_col1 hqc
  have hroot := hv.trans (rootSnd_dvd_fst_sub_u_seven
    r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  have hrow : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr (hqc.trans r.routing.c11_dvd_row1)).trans
      (leftEndpoint_dvd_fst_sub_right_cube (z : ℤ) (y : ℤ))
  rw [fst_eq_for_routing r] at hrow
  convert hrow.sub hroot using 1 <;> ring

private theorem col1_constraint_z {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hqc : q ∣ r.routing.c21) :
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3 := by
  have hv := prime_dvd_rootSnd_of_dvd_col1 r hq hq7 r.routing.c21_dvd_col1 hqc
  have hroot := hv.trans (rootSnd_dvd_fst_sub_u_seven
    r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  have hrow : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr (hqc.trans r.routing.c21_dvd_row2)).trans
      (rightEndpoint_dvd_fst_add_left_cube (z : ℤ) (y : ℤ))
  rw [fst_eq_for_routing r] at hrow
  convert hrow.sub hroot using 1 <;> ring

private theorem col1_constraint_sum {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hqc : q ∣ r.routing.c31) :
    (q : ℤ) ∣ r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3 := by
  have hv := prime_dvd_rootSnd_of_dvd_col1 r hq hq7 r.routing.c31_dvd_col1 hqc
  have hroot := hv.trans (rootSnd_dvd_fst_sub_u_seven
    r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
  have hrow : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
    (Int.natCast_dvd_natCast.mpr (hqc.trans r.routing.c31_dvd_row3)).trans
      (by
        convert endpointSum_dvd_fst_add_left_cube (z : ℤ) (y : ℤ) using 1 <;> norm_num
        ring)
  rw [fst_eq_for_routing r] at hrow
  convert hrow.sub hroot using 1 <;> ring

theorem nonempty_awayFirstCoordinateRoutingConstraints {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nonempty (AwayFirstCoordinateRoutingConstraints r) := by
  exact ⟨{
    rootSector := by
      rw [r.cubic.normal_eq]
      exact awayRootResidueSector_of_packet r.cubic.rootTriple.normal
    sevenPivot := awayRoutingSevenPivot_of_packet r
    c12_constraint := left_constraint_y r
    c22_constraint := left_constraint_z r
    c32_constraint := left_constraint_sum r
    c13_constraint := right_constraint_y r
    c23_constraint := right_constraint_z r
    c33_constraint := right_constraint_sum r
    c11_nonSeven_constraint := fun q hq hq7 h => col1_constraint_y r hq hq7 h
    c21_nonSeven_constraint := fun q hq hq7 h => col1_constraint_z r hq hq7 h
    c31_nonSeven_constraint := fun q hq hq7 h => col1_constraint_sum r hq hq7 h }⟩

inductive EndpointRoutingRow | y | z | sum
  deriving DecidableEq
inductive RootRoutingColumn | sevenV | leftCubic | rightCubic
  deriving DecidableEq

def routingCell {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃)
    (row : EndpointRoutingRow) (column : RootRoutingColumn) : ℕ :=
  match row, column with
  | .y, .sevenV => r.c11 | .y, .leftCubic => r.c12 | .y, .rightCubic => r.c13
  | .z, .sevenV => r.c21 | .z, .leftCubic => r.c22 | .z, .rightCubic => r.c23
  | .sum, .sevenV => r.c31 | .sum, .leftCubic => r.c32 | .sum, .rightCubic => r.c33

def endpointRoutingFactor (y z : ℕ) : EndpointRoutingRow → ℤ
  | .y => y | .z => z | .sum => y + z

def rootRoutingFactor {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    RootRoutingColumn → ℤ
  | .sevenV => r.cubic.rootTriple.normal.root.snd
  | .leftCubic => seventhPowerSndLeftCubic
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd
  | .rightCubic => seventhPowerSndRightCubic
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd

def routingFirstCoordinateValue {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    EndpointRoutingRow → RootRoutingColumn → ℤ
  | .y, .sevenV => r.cubic.rootTriple.normal.root.fst ^ 7 - (z : ℤ) ^ 3
  | .z, .sevenV => r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3
  | .sum, .sevenV => r.cubic.rootTriple.normal.root.fst ^ 7 + (y : ℤ) ^ 3
  | .y, .leftCubic => (z : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd
  | .z, .leftCubic => 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd -
        (y : ℤ) ^ 3
  | .sum, .leftCubic => 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      leftFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd -
        (y : ℤ) ^ 3
  | .y, .rightCubic => (z : ℤ) ^ 3 - 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd
  | .z, .rightCubic => (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd
  | .sum, .rightCubic => (y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
      rightFstCorrection r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd

theorem routingCell_dvd_endpoint {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (row : EndpointRoutingRow) (column : RootRoutingColumn) :
    routingCell r.routing row column ∣ Int.natAbs (endpointRoutingFactor y z row) := by
  cases row <;> cases column
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c11_dvd_row1
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c12_dvd_row1
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c13_dvd_row1
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c21_dvd_row2
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c22_dvd_row2
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c23_dvd_row2
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c31_dvd_row3
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c32_dvd_row3
  · simpa [routingCell, endpointRoutingFactor] using r.routing.c33_dvd_row3

theorem routingCell_dvd_column {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (row : EndpointRoutingRow) (column : RootRoutingColumn) :
    routingCell r.routing row column ∣
      match column with
      | .sevenV => 7 * r.cubic.rootTriple.vPart
      | .leftCubic => r.cubic.rootTriple.leftPart
      | .rightCubic => r.cubic.rootTriple.rightPart := by
  cases row <;> cases column
  · exact r.routing.c11_dvd_col1
  · exact r.routing.c12_dvd_col2
  · exact r.routing.c13_dvd_col3
  · exact r.routing.c21_dvd_col1
  · exact r.routing.c22_dvd_col2
  · exact r.routing.c23_dvd_col3
  · exact r.routing.c31_dvd_col1
  · exact r.routing.c32_dvd_col2
  · exact r.routing.c33_dvd_col3

structure AwayRoutingPrimeWitness {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r.routing row column
  endpoint_condition : (q : ℤ) ∣ endpointRoutingFactor y z row
  root_condition : q = 7 ∨ (q : ℤ) ∣ rootRoutingFactor r column
  firstCoordinate_condition :
    q = 7 ∨ (q : ℤ) ∣ routingFirstCoordinateValue r row column
  seven_pivot : q = 7 → AwayRoutingSevenPivot r

theorem routingPrimeWitness_of_cell_ne_one {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (_constraints : AwayFirstCoordinateRoutingConstraints r)
    (row : EndpointRoutingRow) (column : RootRoutingColumn)
    (hcell : routingCell r.routing row column ≠ 1) :
    Nonempty (AwayRoutingPrimeWitness r) := by
  rcases Nat.exists_prime_and_dvd hcell with ⟨q, hq, hqcell⟩
  have hend : (q : ℤ) ∣ endpointRoutingFactor y z row := by
    exact intCast_dvd_of_dvd_natAbs
      (hqcell.trans (routingCell_dvd_endpoint r row column))
  have hroot : q = 7 ∨ (q : ℤ) ∣ rootRoutingFactor r column := by
    by_cases hq7 : q = 7
    · exact Or.inl hq7
    · right
      cases column with
      | sevenV =>
          exact prime_dvd_rootSnd_of_dvd_col1 r hq hq7
            (routingCell_dvd_column r row .sevenV) hqcell
      | leftCubic =>
          exact cell_dvd_leftCubic r
            (hqcell.trans (routingCell_dvd_column r row .leftCubic))
      | rightCubic =>
          exact cell_dvd_rightCubic r
            (hqcell.trans (routingCell_dvd_column r row .rightCubic))
  have hfirst : q = 7 ∨ (q : ℤ) ∣ routingFirstCoordinateValue r row column := by
    by_cases hq7 : q = 7
    · exact Or.inl hq7
    · right
      cases row <;> cases column
      · exact _constraints.c11_nonSeven_constraint q hq hq7 hqcell
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c12_constraint
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c13_constraint
      · exact _constraints.c21_nonSeven_constraint q hq hq7 hqcell
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c22_constraint
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c23_constraint
      · exact _constraints.c31_nonSeven_constraint q hq hq7 hqcell
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c32_constraint
      · exact (Int.natCast_dvd_natCast.mpr hqcell).trans _constraints.c33_constraint
  exact ⟨{
    q := q, q_prime := hq, row := row, column := column
    q_dvd_cell := hqcell, endpoint_condition := hend, root_condition := hroot
    firstCoordinate_condition := hfirst
    seven_pivot := fun _ => awayRoutingSevenPivot_of_packet r }⟩

/-- Signed reconstruction data genuinely sufficient to build the next packet.
It is stronger than a routing permutation: it supplies the endpoint equation,
primitivity, an away route, and identifies its carrier with the old root
second coordinate. -/
structure AwayFirstCoordinateClosureResolution {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  signedCarrierCompatibility :
    nextRoute.carrier = Int.natAbs r.cubic.transfer.normal.root.snd

theorem awayDescentClosureProvider_of_firstCoordinateResolution {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z)
    (resolution : AwayFirstCoordinateClosureResolution r) :
    Nonempty (AwayDescentClosureProvider x y z r.cubic.transfer) :=
  ⟨{
    nextX := resolution.nextX
    nextY := resolution.nextY
    nextZ := resolution.nextZ
    nextPack := resolution.nextPack
    nextRoute := resolution.nextRoute
    carrier_match := resolution.signedCarrierCompatibility }⟩

inductive FirstCoordinateClosureAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayClosed (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (provider : AwayDescentClosureProvider x y z routing.cubic.transfer)
  | awayConstrained (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)

theorem firstCoordinateClosureAuditResult_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (FirstCoordinateClosureAuditResult x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified p => exact ⟨.ramified p⟩
  | away p =>
      rcases nonempty_awayCubicRoutingPacket p with ⟨routing⟩
      rcases nonempty_awayFirstCoordinateRoutingConstraints routing with ⟨constraints⟩
      exact ⟨.awayConstrained routing constraints⟩

end DkMath.FLT.Seven
