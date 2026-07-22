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

end DkMath.FLT.Seven
