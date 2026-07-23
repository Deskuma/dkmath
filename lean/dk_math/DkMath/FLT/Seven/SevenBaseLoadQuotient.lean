/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseLayerQuotient

#print "file: DkMath.FLT.Seven.SevenBaseLoadQuotient"

namespace DkMath.FLT.Seven

/-- The two nonaddressed endpoint factors left after removing the unique visible
factor seven from the terminal cubic load. -/
def awaySevenBaseLoadQuotientValue
    (row : EndpointRoutingRow) (carrierUnit y z : ℕ) : ℕ :=
  match row with
  | .y => carrierUnit * z * (y + z)
  | .z => y * carrierUnit * (y + z)
  | .sum => y * z * carrierUnit

/-- At terminal depth, cancellation of the single visible factor seven is
performed in `ℕ`, where cancellation is valid.  The resulting equality retains
the selected endpoint row and the complete three-factor root load. -/
theorem AwaySevenBaseCarrierQuotient.load_quotient_eq {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (q : AwaySevenBaseCarrierQuotient p) :
    awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
      r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart := by
  cases hrow : p.row with
  | y =>
      have hcarrier : y = 7 * q.carrierUnit := by
        simpa [endpointRoutingFactorNat, hrow] using q.carrier_eq
      have hseven :
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
            7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by
        calc
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
              (7 * q.carrierUnit) * z * (y + z) := by
                simp [awaySevenBaseLoadQuotientValue, hrow]
                ring
          _ = y * z * (y + z) := by rw [← hcarrier]
          _ = 7 * r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart := r.cubic.product_eq
          _ = 7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by ring
      exact Nat.mul_left_cancel hseven
  | z =>
      have hcarrier : z = 7 * q.carrierUnit := by
        simpa [endpointRoutingFactorNat, hrow] using q.carrier_eq
      have hseven :
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
            7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by
        calc
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
              y * (7 * q.carrierUnit) * (y + z) := by
                simp [awaySevenBaseLoadQuotientValue, hrow]
                ring
          _ = y * z * (y + z) := by rw [← hcarrier]
          _ = 7 * r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart := r.cubic.product_eq
          _ = 7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by ring
      exact Nat.mul_left_cancel hseven
  | sum =>
      have hcarrier : y + z = 7 * q.carrierUnit := by
        simpa [endpointRoutingFactorNat, hrow] using q.carrier_eq
      have hseven :
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
            7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by
        calc
          7 * awaySevenBaseLoadQuotientValue p.row q.carrierUnit y z =
              y * z * (7 * q.carrierUnit) := by
                simp [awaySevenBaseLoadQuotientValue, hrow]
                ring
          _ = y * z * (y + z) := by rw [← hcarrier]
          _ = 7 * r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart := r.cubic.product_eq
          _ = 7 * (r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
              r.cubic.rootTriple.rightPart) := by ring
      exact Nat.mul_left_cancel hseven

end DkMath.FLT.Seven
