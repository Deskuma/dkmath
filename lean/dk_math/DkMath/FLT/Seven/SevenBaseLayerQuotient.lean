/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenPivotDescentAudit

#print "file: DkMath.FLT.Seven.SevenBaseLayerQuotient"

namespace DkMath.FLT.Seven

/-- The unique seven-primary address attached to the pivot packet. -/
def AwaySevenPivotDepthPacket.sevenPrimeAddress {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    AwayRoutingPrimeAddress r where
  q := 7
  q_prime := by norm_num
  row := p.row
  column := .sevenV
  q_dvd_cell := by
    simpa [p.pivot_eq] using p.seven_dvd_pivot
  unique := by
    intro row' column' h
    have hu := r.prime_address_unique (by norm_num : Nat.Prime 7)
      (by simpa [p.pivot_eq] using p.seven_dvd_pivot) h
    exact ⟨hu.1.symm, hu.2.symm⟩

/-- The selected endpoint factor has exactly the pivot's seven-adic depth. -/
theorem AwaySevenPivotDepthPacket.endpoint_depth_eq_exponent {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    padicValNat 7 (endpointRoutingFactorNat y z p.row) = p.exponent := by
  have hcell :
      padicValNat 7 (routingCell r.routing p.row .sevenV) =
        padicValNat 7 (endpointRoutingFactorNat y z p.row) := by
    simpa [AwaySevenPivotDepthPacket.sevenPrimeAddress] using
      p.sevenPrimeAddress.cell_depth_eq_endpoint_depth
  calc
    padicValNat 7 (endpointRoutingFactorNat y z p.row) =
        padicValNat 7 (routingCell r.routing p.row .sevenV) := hcell.symm
    _ = padicValNat 7 p.pivot :=
      (congrArg (padicValNat 7) p.pivot_eq).symm
    _ = p.exponent := p.exponent_eq_pivot.symm

private theorem AwaySevenPivotDepthPacket.endpoint_factor_pos {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    0 < endpointRoutingFactorNat y z p.row := by
  cases hrow : p.row with
  | y =>
      simpa [endpointRoutingFactorNat, hrow] using
        r.cubic.endpointTriple.first_pos
  | z =>
      simpa [endpointRoutingFactorNat, hrow] using
        r.cubic.endpointTriple.second_pos
  | sum =>
      simpa [endpointRoutingFactorNat, hrow] using
        r.cubic.endpointTriple.third_pos

/-- At terminal depth, the selected endpoint factor is seven times a positive
seven-adic unit. -/
structure AwaySevenBaseCarrierQuotient {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) : Type where
  depth_eq_one : p.exponent = 1
  carrierUnit : ℕ
  carrier_eq : endpointRoutingFactorNat y z p.row = 7 * carrierUnit
  carrierUnit_pos : 0 < carrierUnit
  seven_not_dvd_carrierUnit : ¬ 7 ∣ carrierUnit

/-- Exact extraction of the one visible factor seven from a terminal pivot row. -/
theorem nonempty_awaySevenBaseCarrierQuotient {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (hbase : p.exponent = 1) : Nonempty (AwaySevenBaseCarrierQuotient p) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let endpoint := endpointRoutingFactorNat y z p.row
  have endpoint_pos : 0 < endpoint := by
    simpa [endpoint] using p.endpoint_factor_pos
  have endpoint_ne : endpoint ≠ 0 := endpoint_pos.ne'
  have endpoint_depth : padicValNat 7 endpoint = 1 := by
    simpa [endpoint, hbase] using p.endpoint_depth_eq_exponent
  have seven_dvd_endpoint : 7 ∣ endpoint := by
    apply (@padicValNat_dvd_iff_le 7 inferInstance endpoint 1 endpoint_ne).mpr
    rw [endpoint_depth]
  rcases seven_dvd_endpoint with ⟨carrierUnit, carrier_eq⟩
  have carrierUnit_pos : 0 < carrierUnit := by
    omega
  have seven_not_dvd_carrierUnit : ¬ 7 ∣ carrierUnit := by
    intro hseven
    rcases hseven with ⟨d, hd⟩
    have h49 : 7 ^ 2 ∣ endpoint := by
      refine ⟨d, ?_⟩
      rw [carrier_eq, hd]
      norm_num
      ring
    have htwo : 2 ≤ padicValNat 7 endpoint :=
      (@padicValNat_dvd_iff_le 7 inferInstance endpoint 2 endpoint_ne).mp h49
    rw [endpoint_depth] at htwo
    omega
  exact ⟨{
    depth_eq_one := hbase
    carrierUnit := carrierUnit
    carrier_eq := by simpa [endpoint] using carrier_eq
    carrierUnit_pos := carrierUnit_pos
    seven_not_dvd_carrierUnit := seven_not_dvd_carrierUnit }⟩

/-- The integer quotient left after extracting the single visible factor seven
from the ramified first-coordinate residual. -/
def sevenRamifiedResidualQuotient (u v : ℤ) : ℤ :=
  -2 * v ^ 2 * (u + v) * sevenRamifiedResidualPolynomial u v

/-- Exact first-order residual factorization.  The factor seven is extracted in
`ℤ`, before any reduction modulo a seven power. -/
theorem seventhPowerFst_sub_sevenRamifiedCore_eq_seven_mul_quotient
    (u v : ℤ) :
    seventhPowerFst u v - (u ^ 7 + 4 * v ^ 7) =
      7 * sevenRamifiedResidualQuotient u v := by
  rw [seventhPowerFst_eq_sevenRamifiedCore_add_residual]
  simp [sevenRamifiedResidualQuotient]
  ring

/-- The exact row-specific endpoint identity after the unique visible factor
seven has been extracted from the selected endpoint. -/
def AwaySevenBaseEndpointQuotientEquation
    (row : EndpointRoutingRow) (carrierUnit y z : ℕ) : Prop :=
  match row with
  | .y =>
      cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 =
        7 * ((carrierUnit : ℤ) * ((z : ℤ) - (y : ℤ)) * ((z : ℤ) + (y : ℤ)))
  | .z =>
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 =
        7 * ((carrierUnit : ℤ) * (z : ℤ) * ((z : ℤ) + (y : ℤ)))
  | .sum =>
      cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 =
        7 * ((carrierUnit : ℤ) * (z : ℤ) ^ 2)

/-- The carrier quotient supplies the exact endpoint quotient identity in each
of the three terminal pivot rows. -/
theorem AwaySevenBaseCarrierQuotient.endpoint_quotient_eq {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (q : AwaySevenBaseCarrierQuotient p) :
    AwaySevenBaseEndpointQuotientEquation p.row q.carrierUnit y z := by
  cases hrow : p.row with
  | y =>
      have hcarrier : (y : ℤ) = 7 * (q.carrierUnit : ℤ) := by
        have h := congrArg (fun n : ℕ => (n : ℤ)) q.carrier_eq
        simpa [endpointRoutingFactorNat, hrow] using h
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow]
      rw [cyclotomicSevenFst_sub_right_cube, hcarrier]
      ring
  | z =>
      have hcarrier : (z : ℤ) = 7 * (q.carrierUnit : ℤ) := by
        have h := congrArg (fun n : ℕ => (n : ℤ)) q.carrier_eq
        simpa [endpointRoutingFactorNat, hrow] using h
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow]
      rw [cyclotomicSevenFst_add_left_cube, hcarrier]
      ring
  | sum =>
      have hcarrier : (y : ℤ) + (z : ℤ) = 7 * (q.carrierUnit : ℤ) := by
        have h := congrArg (fun n : ℕ => (n : ℤ)) q.carrier_eq
        simpa [endpointRoutingFactorNat, hrow, Nat.cast_add] using h
      have hcarrier' : (z : ℤ) + (y : ℤ) = 7 * (q.carrierUnit : ℤ) := by
        linear_combination hcarrier
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow]
      rw [cyclotomicSevenFst_add_left_cube, hcarrier']
      ring

/-- The row-specific endpoint quotient after removing the visible factor seven. -/
def awaySevenBaseEndpointQuotientValue
    (row : EndpointRoutingRow) (carrierUnit y z : ℕ) : ℤ :=
  match row with
  | .y => (carrierUnit : ℤ) * ((z : ℤ) - (y : ℤ)) * ((z : ℤ) + (y : ℤ))
  | .z => (carrierUnit : ℤ) * (z : ℤ) * ((z : ℤ) + (y : ℤ))
  | .sum => (carrierUnit : ℤ) * (z : ℤ) ^ 2

/-- The first-order ramified core appearing before division by seven. -/
def awaySevenBaseFirstOrderCore
    (row : EndpointRoutingRow) (u v : ℤ) (y z : ℕ) : ℤ :=
  match row with
  | .y => u ^ 7 + 4 * v ^ 7 - (z : ℤ) ^ 3
  | .z | .sum => u ^ 7 + 4 * v ^ 7 + (y : ℤ) ^ 3

/-- Exact first-order terminal identity in `ℤ`.  It is obtained by subtracting
the residual quotient identity from the selected endpoint quotient identity,
without cancelling seven in `ZMod 49`. -/
theorem AwaySevenBaseCarrierQuotient.first_order_core_eq {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (q : AwaySevenBaseCarrierQuotient p) :
    awaySevenBaseFirstOrderCore p.row
        r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd y z =
      7 * (awaySevenBaseEndpointQuotientValue p.row q.carrierUnit y z -
        sevenRamifiedResidualQuotient r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd) := by
  have hend := q.endpoint_quotient_eq
  have hres := seventhPowerFst_sub_sevenRamifiedCore_eq_seven_mul_quotient
    r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd
  rw [r.cubic.rootTriple.normal.fst_eq] at hend
  cases hrow : p.row with
  | y =>
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow,
        awaySevenBaseFirstOrderCore, awaySevenBaseEndpointQuotientValue] at hend ⊢
      linear_combination hend - hres
  | z =>
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow,
        awaySevenBaseFirstOrderCore, awaySevenBaseEndpointQuotientValue] at hend ⊢
      linear_combination hend - hres
  | sum =>
      simp only [AwaySevenBaseEndpointQuotientEquation, hrow,
        awaySevenBaseFirstOrderCore, awaySevenBaseEndpointQuotientValue] at hend ⊢
      linear_combination hend - hres

/-- Signed root-second-coordinate data specialized to the terminal seven layer. -/
structure AwaySevenBaseSignedKernel {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) : Type where
  depth_eq_one : p.exponent = 1
  unitPart : ℤ
  unitPart_not_seven_dvd : ¬ (7 : ℤ) ∣ unitPart
  rootSnd_eq : r.cubic.rootTriple.normal.root.snd = unitPart
  unitPart_isUnit_modSeven : IsUnit (unitPart : ZMod 7)

/-- At depth one the ramified kernel has no remaining factor seven: its signed
unit part is exactly the actual root second coordinate. -/
theorem nonempty_awaySevenBaseSignedKernel {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r)
    (hbase : p.exponent = 1) : Nonempty (AwaySevenBaseSignedKernel p) := by
  rcases nonempty_awaySevenRamifiedKernelPacket p with ⟨kernel⟩
  have hsnd : r.cubic.rootTriple.normal.root.snd = kernel.unitPart := by
    simpa [hbase] using kernel.rootSnd_eq
  have hunit : IsUnit (kernel.unitPart : ZMod 7) := by
    simpa [AwaySevenPivotDepthPacket.upperModulus, hbase] using kernel.unitPart_isUnit
  exact ⟨{
    depth_eq_one := hbase
    unitPart := kernel.unitPart
    unitPart_not_seven_dvd := kernel.unitPart_not_seven_dvd
    rootSnd_eq := hsnd
    unitPart_isUnit_modSeven := hunit }⟩

end DkMath.FLT.Seven
