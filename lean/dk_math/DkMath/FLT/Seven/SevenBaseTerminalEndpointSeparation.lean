/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalLoadDivisibility

#print "file: DkMath.FLT.Seven.SevenBaseTerminalEndpointSeparation"

namespace DkMath.FLT.Seven

/-- After extracting the unique visible factor seven from the selected endpoint,
the remaining carrier unit is still coprime to the row-sensitive unselected
endpoint. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.unselected_endpoint_coprime_carrierUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    Nat.Coprime (awaySevenBaseTerminalUnselectedEndpointNat p.row y z)
      packet.carrier.carrierUnit := by
  have hcopYZ : IsCoprime (y : ℤ) (z : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using r.cubic.endpointTriple.coprime_first_second
  have hcopSelected :
      IsCoprime
        (awaySevenBaseTerminalUnselectedEndpointNat p.row y z : ℤ)
        (endpointRoutingFactorNat y z p.row : ℤ) := by
    cases hrow : p.row with
    | y =>
        simpa [awaySevenBaseTerminalUnselectedEndpointNat,
          endpointRoutingFactorNat, hrow] using hcopYZ.symm
    | z =>
        simpa [awaySevenBaseTerminalUnselectedEndpointNat,
          endpointRoutingFactorNat, hrow] using hcopYZ
    | sum =>
        rcases hcopYZ with ⟨a, b, hab⟩
        refine ⟨a - b, b, ?_⟩
        calc
          (a - b) * (y : ℤ) + b * ((y : ℤ) + (z : ℤ)) =
              a * (y : ℤ) + b * (z : ℤ) := by ring
          _ = 1 := hab
  have hcarrier := congrArg (fun n : ℕ => (n : ℤ)) packet.carrier.carrier_eq
  push_cast at hcarrier
  rcases hcopSelected with ⟨a, b, hab⟩
  have hcopCarrier :
      IsCoprime
        (awaySevenBaseTerminalUnselectedEndpointNat p.row y z : ℤ)
        (packet.carrier.carrierUnit : ℤ) := by
    refine ⟨a, 7 * b, ?_⟩
    rw [hcarrier] at hab
    calc
      a * (awaySevenBaseTerminalUnselectedEndpointNat p.row y z : ℤ) +
          (7 * b) * (packet.carrier.carrierUnit : ℤ) =
        a * (awaySevenBaseTerminalUnselectedEndpointNat p.row y z : ℤ) +
          b * (7 * (packet.carrier.carrierUnit : ℤ)) := by ring
      _ = 1 := hab
  rw [Int.isCoprime_iff_nat_coprime] at hcopCarrier
  simpa using hcopCarrier

/-- The second endpoint factor left outside the selected terminal row.  Together
with `awaySevenBaseTerminalUnselectedEndpointNat`, it gives the two endpoint
factors remaining after the selected factor is replaced by its carrier unit. -/
def awaySevenBaseTerminalCompanionEndpointNat
    (row : EndpointRoutingRow) (y z : ℕ) : ℕ :=
  match row with
  | .y | .z => y + z
  | .sum => z

/-- The second endpoint remaining outside the selected row is also coprime to
the carrier unit left after extracting the unique factor seven. -/
theorem AwaySevenBaseTerminalQuotientCorePacket.companion_endpoint_coprime_carrierUnit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalQuotientCorePacket source r p) :
    Nat.Coprime (awaySevenBaseTerminalCompanionEndpointNat p.row y z)
      packet.carrier.carrierUnit := by
  have hcopSelected :
      IsCoprime
        (awaySevenBaseTerminalCompanionEndpointNat p.row y z : ℤ)
        (endpointRoutingFactorNat y z p.row : ℤ) := by
    cases hrow : p.row with
    | y =>
        rw [Int.isCoprime_iff_nat_coprime]
        simpa [awaySevenBaseTerminalCompanionEndpointNat,
          endpointRoutingFactorNat, hrow] using
          r.cubic.endpointTriple.coprime_first_third.symm
    | z =>
        rw [Int.isCoprime_iff_nat_coprime]
        simpa [awaySevenBaseTerminalCompanionEndpointNat,
          endpointRoutingFactorNat, hrow] using
          r.cubic.endpointTriple.coprime_second_third.symm
    | sum =>
        rw [Int.isCoprime_iff_nat_coprime]
        simpa [awaySevenBaseTerminalCompanionEndpointNat,
          endpointRoutingFactorNat, hrow] using
          r.cubic.endpointTriple.coprime_second_third
  have hcarrier := congrArg (fun n : ℕ => (n : ℤ)) packet.carrier.carrier_eq
  push_cast at hcarrier
  rcases hcopSelected with ⟨a, b, hab⟩
  have hcopCarrier :
      IsCoprime
        (awaySevenBaseTerminalCompanionEndpointNat p.row y z : ℤ)
        (packet.carrier.carrierUnit : ℤ) := by
    refine ⟨a, 7 * b, ?_⟩
    rw [hcarrier] at hab
    calc
      a * (awaySevenBaseTerminalCompanionEndpointNat p.row y z : ℤ) +
          (7 * b) * (packet.carrier.carrierUnit : ℤ) =
        a * (awaySevenBaseTerminalCompanionEndpointNat p.row y z : ℤ) +
          b * (7 * (packet.carrier.carrierUnit : ℤ)) := by ring
      _ = 1 := hab
  rw [Int.isCoprime_iff_nat_coprime] at hcopCarrier
  simpa using hcopCarrier

end DkMath.FLT.Seven
