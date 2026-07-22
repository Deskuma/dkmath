/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.LocalObstructionAudit

#print "file: DkMath.FLT.Seven.SpecializedPrimeAddress"

namespace DkMath.FLT.Seven

theorem AwayCubicRoutingPacket.endpoint_y_z_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Nat.Coprime y z :=
  r.cubic.endpointTriple.coprime_first_second

theorem AwayCubicRoutingPacket.endpoint_y_sum_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Nat.Coprime y (y + z) :=
  r.cubic.endpointTriple.coprime_first_third

theorem AwayCubicRoutingPacket.endpoint_z_sum_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Nat.Coprime z (y + z) :=
  r.cubic.endpointTriple.coprime_second_third

private theorem seven_coprime_leftPart {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime 7 r.cubic.rootTriple.leftPart := by
  apply (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
  intro h
  have hprod : 7 ∣ r.cubic.rootTriple.leftPart * r.cubic.rootTriple.rightPart :=
    dvd_mul_of_dvd_left h _
  rw [r.cubic.rootTriple.leftPart_eq, r.cubic.rootTriple.rightPart_eq,
    ← Int.natAbs_mul, ← seventhPowerSndCore_factor] at hprod
  exact r.cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore hprod

private theorem seven_coprime_rightPart {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime 7 r.cubic.rootTriple.rightPart := by
  apply (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
  intro h
  have hprod : 7 ∣ r.cubic.rootTriple.leftPart * r.cubic.rootTriple.rightPart :=
    dvd_mul_of_dvd_right h _
  rw [r.cubic.rootTriple.leftPart_eq, r.cubic.rootTriple.rightPart_eq,
    ← Int.natAbs_mul, ← seventhPowerSndCore_factor] at hprod
  exact r.cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore hprod

theorem AwayCubicRoutingPacket.column_sevenV_left_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime (7 * r.cubic.rootTriple.vPart) r.cubic.rootTriple.leftPart :=
  (seven_coprime_leftPart r).mul_left r.cubic.rootTriple.coprime_v_left

theorem AwayCubicRoutingPacket.column_sevenV_right_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime (7 * r.cubic.rootTriple.vPart) r.cubic.rootTriple.rightPart :=
  (seven_coprime_rightPart r).mul_left r.cubic.rootTriple.coprime_v_right

theorem AwayCubicRoutingPacket.column_left_right_coprime {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) :
    Nat.Coprime r.cubic.rootTriple.leftPart r.cubic.rootTriple.rightPart :=
  r.cubic.rootTriple.coprime_left_right

def endpointRoutingFactorNat (y z : ℕ) : EndpointRoutingRow → ℕ
  | .y => y
  | .z => z
  | .sum => y + z

def rootRoutingFactorNat {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :
    RootRoutingColumn → ℕ
  | .sevenV => 7 * r.cubic.rootTriple.vPart
  | .leftCubic => r.cubic.rootTriple.leftPart
  | .rightCubic => r.cubic.rootTriple.rightPart

theorem routingCell_dvd_endpointRoutingFactorNat {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) (row : EndpointRoutingRow)
    (column : RootRoutingColumn) :
    routingCell r.routing row column ∣ endpointRoutingFactorNat y z row := by
  cases row <;> cases column
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c11_dvd_row1
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c12_dvd_row1
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c13_dvd_row1
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c21_dvd_row2
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c22_dvd_row2
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c23_dvd_row2
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c31_dvd_row3
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c32_dvd_row3
  · simpa [routingCell, endpointRoutingFactorNat] using r.routing.c33_dvd_row3

theorem routingCell_dvd_rootRoutingFactorNat {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) (row : EndpointRoutingRow)
    (column : RootRoutingColumn) :
    routingCell r.routing row column ∣ rootRoutingFactorNat r column := by
  simpa [rootRoutingFactorNat] using routingCell_dvd_column r row column

private theorem prime_not_dvd_second_of_coprime {q a b : ℕ} (hq : Nat.Prime q)
    (hab : Nat.Coprime a b) (ha : q ∣ a) : ¬ q ∣ b := by
  intro hb
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hab ha hb)

theorem AwayCubicRoutingPacket.row_eq_of_prime_dvd_cells {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) : row₁ = row₂ := by
  have hrow₁ := h₁.trans (routingCell_dvd_endpointRoutingFactorNat r row₁ column₁)
  have hrow₂ := h₂.trans (routingCell_dvd_endpointRoutingFactorNat r row₂ column₂)
  cases row₁ <;> cases row₂ <;> try rfl
  all_goals simp only [endpointRoutingFactorNat] at hrow₁ hrow₂
  · exact False.elim ((prime_not_dvd_second_of_coprime hq r.endpoint_y_z_coprime hrow₁) hrow₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq r.endpoint_y_sum_coprime hrow₁) hrow₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq r.endpoint_y_z_coprime.symm hrow₁) hrow₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq r.endpoint_z_sum_coprime hrow₁) hrow₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.endpoint_y_sum_coprime.symm hrow₁) hrow₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.endpoint_z_sum_coprime.symm hrow₁) hrow₂)

theorem AwayCubicRoutingPacket.column_eq_of_prime_dvd_cells {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) : column₁ = column₂ := by
  have hcol₁ := h₁.trans (routingCell_dvd_rootRoutingFactorNat r row₁ column₁)
  have hcol₂ := h₂.trans (routingCell_dvd_rootRoutingFactorNat r row₂ column₂)
  cases column₁ <;> cases column₂ <;> try rfl
  all_goals simp only [rootRoutingFactorNat] at hcol₁ hcol₂
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_sevenV_left_coprime hcol₁) hcol₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_sevenV_right_coprime hcol₁) hcol₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_sevenV_left_coprime.symm hcol₁) hcol₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_left_right_coprime hcol₁) hcol₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_sevenV_right_coprime.symm hcol₁) hcol₂)
  · exact False.elim ((prime_not_dvd_second_of_coprime hq
      r.column_left_right_coprime.symm hcol₁) hcol₂)

theorem AwayCubicRoutingPacket.prime_address_unique {x y z q : ℕ}
    (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) :
    row₁ = row₂ ∧ column₁ = column₂ :=
  ⟨r.row_eq_of_prime_dvd_cells hq h₁ h₂,
    r.column_eq_of_prime_dvd_cells hq h₁ h₂⟩

structure AwayRoutingPrimeAddress {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  q : ℕ
  q_prime : Nat.Prime q
  row : EndpointRoutingRow
  column : RootRoutingColumn
  q_dvd_cell : q ∣ routingCell r.routing row column
  unique : ∀ row' column', q ∣ routingCell r.routing row' column' →
    row' = row ∧ column' = column

theorem nonempty_awayRoutingPrimeAddress_of_cell_ne_one {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) (row : EndpointRoutingRow)
    (column : RootRoutingColumn) (hcell : routingCell r.routing row column ≠ 1) :
    Nonempty (AwayRoutingPrimeAddress r) := by
  rcases Nat.exists_prime_and_dvd hcell with ⟨q, hq, hd⟩
  exact ⟨{
    q := q
    q_prime := hq
    row := row
    column := column
    q_dvd_cell := hd
    unique := fun row' column' h => r.prime_address_unique hq h hd }⟩

theorem AwayRoutingPrimeAddress.not_dvd_other_column {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (a : AwayRoutingPrimeAddress r)
    {column' : RootRoutingColumn} (hne : column' ≠ a.column) :
    ¬ a.q ∣ routingCell r.routing a.row column' := by
  intro h
  exact hne (a.unique a.row column' h).2

theorem AwayRoutingPrimeAddress.not_dvd_other_row {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (a : AwayRoutingPrimeAddress r)
    {row' : EndpointRoutingRow} (hne : row' ≠ a.row) :
    ¬ a.q ∣ routingCell r.routing row' a.column := by
  intro h
  exact hne (a.unique row' a.column h).1

private theorem routingCell_ne_zero {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (row : EndpointRoutingRow) (column : RootRoutingColumn) :
    routingCell r.routing row column ≠ 0 := by
  intro h
  have hd := routingCell_dvd_endpointRoutingFactorNat r row column
  rw [h] at hd
  have hz : endpointRoutingFactorNat y z row = 0 := by simpa using hd
  cases row with
  | y =>
      apply Nat.ne_of_gt r.cubic.endpointTriple.first_pos
      simpa [endpointRoutingFactorNat] using hz
  | z =>
      apply Nat.ne_of_gt r.cubic.endpointTriple.second_pos
      simpa [endpointRoutingFactorNat] using hz
  | sum =>
      apply Nat.ne_of_gt r.cubic.endpointTriple.third_pos
      simpa [endpointRoutingFactorNat] using hz

private theorem first_depth_eq_product {q a b c : ℕ} (hq : Nat.Prime q)
    (ha : q ∣ a) (hab : Nat.Coprime a b) (hac : Nat.Coprime a c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q a = padicValNat q (a * b * c) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hb := prime_not_dvd_second_of_coprime hq hab ha
  have hc := prime_not_dvd_second_of_coprime hq hac ha
  rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0, padicValNat.mul ha0 hb0,
    padicValNat.eq_zero_of_not_dvd hb, padicValNat.eq_zero_of_not_dvd hc]
  omega

private theorem middle_depth_eq_product {q a b c : ℕ} (hq : Nat.Prime q)
    (hb : q ∣ b) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q b = padicValNat q (a * b * c) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have ha := prime_not_dvd_second_of_coprime hq hab.symm hb
  have hc := prime_not_dvd_second_of_coprime hq hbc hb
  rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0, padicValNat.mul ha0 hb0,
    padicValNat.eq_zero_of_not_dvd ha, padicValNat.eq_zero_of_not_dvd hc]
  omega

private theorem last_depth_eq_product {q a b c : ℕ} (hq : Nat.Prime q)
    (hc : q ∣ c) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q c = padicValNat q (a * b * c) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have ha := prime_not_dvd_second_of_coprime hq hac.symm hc
  have hb := prime_not_dvd_second_of_coprime hq hbc.symm hc
  rw [padicValNat.mul (mul_ne_zero ha0 hb0) hc0, padicValNat.mul ha0 hb0,
    padicValNat.eq_zero_of_not_dvd ha, padicValNat.eq_zero_of_not_dvd hb]
  omega

private theorem first_depth_eq_factor {q d a b c : ℕ} (hq : Nat.Prime q)
    (hd : d = a * b * c) (ha : q ∣ a) (hab : Nat.Coprime a b)
    (hac : Nat.Coprime a c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q a = padicValNat q d :=
  (first_depth_eq_product hq ha hab hac ha0 hb0 hc0).trans
    (congrArg (padicValNat q) hd.symm)

private theorem middle_depth_eq_factor {q d a b c : ℕ} (hq : Nat.Prime q)
    (hd : d = a * b * c) (hb : q ∣ b) (hab : Nat.Coprime a b)
    (hbc : Nat.Coprime b c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q b = padicValNat q d :=
  (middle_depth_eq_product hq hb hab hbc ha0 hb0 hc0).trans
    (congrArg (padicValNat q) hd.symm)

private theorem last_depth_eq_factor {q d a b c : ℕ} (hq : Nat.Prime q)
    (hd : d = a * b * c) (hc : q ∣ c) (hac : Nat.Coprime a c)
    (hbc : Nat.Coprime b c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    padicValNat q c = padicValNat q d :=
  (last_depth_eq_product hq hc hac hbc ha0 hb0 hc0).trans
    (congrArg (padicValNat q) hd.symm)

theorem AwayRoutingPrimeAddress.cell_depth_eq_endpoint_depth {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (endpointRoutingFactorNat y z a.row) := by
  have cell0 := routingCell_ne_zero (r := r) a.row a.column
  have hqcell := a.q_dvd_cell
  have c11 : r.routing.c11 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .sevenV
  have c12 : r.routing.c12 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .leftCubic
  have c13 : r.routing.c13 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .rightCubic
  have c21 : r.routing.c21 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .sevenV
  have c22 : r.routing.c22 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .leftCubic
  have c23 : r.routing.c23 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .rightCubic
  have c31 : r.routing.c31 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .sevenV
  have c32 : r.routing.c32 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .leftCubic
  have c33 : r.routing.c33 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .rightCubic
  cases hr : a.row <;> cases hc : a.column
  all_goals simp only [hr, hc, routingCell, endpointRoutingFactorNat] at hqcell cell0 ⊢
  · exact first_depth_eq_factor a.q_prime r.routing.row1 hqcell
      r.routing.row1_coprime.1 r.routing.row1_coprime.2.1 cell0
      c12 c13
  · exact middle_depth_eq_factor a.q_prime r.routing.row1 hqcell
      r.routing.row1_coprime.1 r.routing.row1_coprime.2.2
      c11 cell0 c13
  · exact last_depth_eq_factor a.q_prime r.routing.row1 hqcell
      r.routing.row1_coprime.2.1 r.routing.row1_coprime.2.2
      c11 c12 cell0
  · exact first_depth_eq_factor a.q_prime r.routing.row2 hqcell
      r.routing.row2_coprime.1 r.routing.row2_coprime.2.1 cell0
      c22 c23
  · exact middle_depth_eq_factor a.q_prime r.routing.row2 hqcell
      r.routing.row2_coprime.1 r.routing.row2_coprime.2.2
      c21 cell0 c23
  · exact last_depth_eq_factor a.q_prime r.routing.row2 hqcell
      r.routing.row2_coprime.2.1 r.routing.row2_coprime.2.2
      c21 c22 cell0
  · exact first_depth_eq_factor a.q_prime r.routing.row3 hqcell
      r.routing.row3_coprime.1 r.routing.row3_coprime.2.1 cell0
      c32 c33
  · exact middle_depth_eq_factor a.q_prime r.routing.row3 hqcell
      r.routing.row3_coprime.1 r.routing.row3_coprime.2.2
      c31 cell0 c33
  · exact last_depth_eq_factor a.q_prime r.routing.row3 hqcell
      r.routing.row3_coprime.2.1 r.routing.row3_coprime.2.2
      c31 c32 cell0

theorem AwayRoutingPrimeAddress.cell_depth_eq_root_depth {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (rootRoutingFactorNat r a.column) := by
  have cell0 := routingCell_ne_zero (r := r) a.row a.column
  have hqcell := a.q_dvd_cell
  have c11 : r.routing.c11 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .sevenV
  have c12 : r.routing.c12 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .leftCubic
  have c13 : r.routing.c13 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .y .rightCubic
  have c21 : r.routing.c21 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .sevenV
  have c22 : r.routing.c22 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .leftCubic
  have c23 : r.routing.c23 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .z .rightCubic
  have c31 : r.routing.c31 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .sevenV
  have c32 : r.routing.c32 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .leftCubic
  have c33 : r.routing.c33 ≠ 0 := by
    simpa [routingCell] using routingCell_ne_zero (r := r) .sum .rightCubic
  cases hc : a.column <;> cases hr : a.row
  all_goals simp only [hr, hc, routingCell, rootRoutingFactorNat] at hqcell cell0 ⊢
  · exact first_depth_eq_factor a.q_prime r.routing.col1 hqcell
      r.routing.col1_coprime.1 r.routing.col1_coprime.2.1 cell0
      c21 c31
  · exact middle_depth_eq_factor a.q_prime r.routing.col1 hqcell
      r.routing.col1_coprime.1 r.routing.col1_coprime.2.2
      c11 cell0 c31
  · exact last_depth_eq_factor a.q_prime r.routing.col1 hqcell
      r.routing.col1_coprime.2.1 r.routing.col1_coprime.2.2
      c11 c21 cell0
  · exact first_depth_eq_factor a.q_prime r.routing.col2 hqcell
      r.routing.col2_coprime.1 r.routing.col2_coprime.2.1 cell0
      c22 c32
  · exact middle_depth_eq_factor a.q_prime r.routing.col2 hqcell
      r.routing.col2_coprime.1 r.routing.col2_coprime.2.2
      c12 cell0 c32
  · exact last_depth_eq_factor a.q_prime r.routing.col2 hqcell
      r.routing.col2_coprime.2.1 r.routing.col2_coprime.2.2
      c12 c22 cell0
  · exact first_depth_eq_factor a.q_prime r.routing.col3 hqcell
      r.routing.col3_coprime.1 r.routing.col3_coprime.2.1 cell0
      c23 c33
  · exact middle_depth_eq_factor a.q_prime r.routing.col3 hqcell
      r.routing.col3_coprime.1 r.routing.col3_coprime.2.2
      c13 cell0 c33
  · exact last_depth_eq_factor a.q_prime r.routing.col3 hqcell
      r.routing.col3_coprime.2.1 r.routing.col3_coprime.2.2
      c13 c23 cell0

structure AwayRoutingPrimeDepthPacket {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  address : AwayRoutingPrimeAddress r
  exponent : ℕ
  exponent_eq_cell : exponent = padicValNat address.q
    (routingCell r.routing address.row address.column)
  exponent_pos : 0 < exponent
  endpoint_depth_eq : padicValNat address.q
    (endpointRoutingFactorNat y z address.row) = exponent
  root_depth_eq : padicValNat address.q
    (rootRoutingFactorNat r address.column) = exponent

def AwayRoutingPrimeAddress.toDepthPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (a : AwayRoutingPrimeAddress r) :
    AwayRoutingPrimeDepthPacket r where
  address := a
  exponent := padicValNat a.q (routingCell r.routing a.row a.column)
  exponent_eq_cell := rfl
  exponent_pos := by
    letI : Fact (Nat.Prime a.q) := ⟨a.q_prime⟩
    exact one_le_padicValNat_of_dvd (routingCell_ne_zero a.row a.column) a.q_dvd_cell
  endpoint_depth_eq := a.cell_depth_eq_endpoint_depth.symm
  root_depth_eq := a.cell_depth_eq_root_depth.symm

end DkMath.FLT.Seven
