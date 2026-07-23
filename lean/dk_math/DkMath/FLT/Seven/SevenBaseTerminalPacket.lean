/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseLoadQuotient
import DkMath.FLT.Seven.SevenBaseUnitSectorClassification

#print "file: DkMath.FLT.Seven.SevenBaseTerminalPacket"

namespace DkMath.FLT.Seven

/-- The currently proved exact data at the terminal seven-primary layer.

This packet deliberately stops before claiming a terminal contradiction.  It
combines the actual base solution, the exact one-factor carrier quotient, the
signed root unit, the first-order integer identity, and the cubic-load quotient.
-/
structure AwaySevenBaseTerminalQuotientCorePacket {x y z : ℕ}
    (source : CounterexamplePack x y z) (r : AwayCubicRoutingPacket x y z)
    (p : AwaySevenPivotDepthPacket r) : Type where
  depth_eq_one : p.exponent = 1
  baseLayer : AwaySevenBaseLayerPacket p
  carrier : AwaySevenBaseCarrierQuotient p
  kernel : AwaySevenBaseSignedKernel p
  endpoint_quotient_eq :
    AwaySevenBaseEndpointQuotientEquation p.row carrier.carrierUnit y z
  first_order_core_eq :
    awaySevenBaseFirstOrderCore p.row
        r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd y z =
      7 * (awaySevenBaseEndpointQuotientValue p.row carrier.carrierUnit y z -
        sevenRamifiedResidualQuotient r.cubic.rootTriple.normal.root.fst
          r.cubic.rootTriple.normal.root.snd)
  load_quotient_eq :
    awaySevenBaseLoadQuotientValue p.row carrier.carrierUnit y z =
      r.cubic.rootTriple.vPart * r.cubic.rootTriple.leftPart *
        r.cubic.rootTriple.rightPart

/-- Every actual depth-one pivot produces the complete exact quotient core
currently available for the terminal arithmetic attack. -/
theorem nonempty_awaySevenBaseTerminalQuotientCorePacket {x y z : ℕ}
    (source : CounterexamplePack x y z) (r : AwayCubicRoutingPacket x y z)
    (p : AwaySevenPivotDepthPacket r) (hbase : p.exponent = 1) :
    Nonempty (AwaySevenBaseTerminalQuotientCorePacket source r p) := by
  rcases nonempty_awaySevenBaseCarrierQuotient p hbase with ⟨carrier⟩
  rcases nonempty_awaySevenBaseSignedKernel p hbase with ⟨kernel⟩
  exact ⟨{
    depth_eq_one := hbase
    baseLayer := p.toBaseLayerPacket hbase
    carrier := carrier
    kernel := kernel
    endpoint_quotient_eq := carrier.endpoint_quotient_eq
    first_order_core_eq := carrier.first_order_core_eq
    load_quotient_eq := carrier.load_quotient_eq }⟩

/-- The exact terminal quotient/load core together with its finite unit-sector
equation.  This packet joins the integer and `ZMod 7` layers without asserting a
terminal exclusion. -/
structure AwaySevenBaseTerminalUnitSectorPacket {x y z : ℕ}
    (source : CounterexamplePack x y z) (r : AwayCubicRoutingPacket x y z)
    (p : AwaySevenPivotDepthPacket r) : Type where
  core : AwaySevenBaseTerminalQuotientCorePacket source r p
  unitSector : AwaySevenBaseUnitEquationPacket p

/-- Every actual depth-one pivot simultaneously carries the exact quotient/load
core and the normalized binary unit-sector equation. -/
theorem nonempty_awaySevenBaseTerminalUnitSectorPacket {x y z : ℕ}
    (source : CounterexamplePack x y z) (r : AwayCubicRoutingPacket x y z)
    (p : AwaySevenPivotDepthPacket r) (hbase : p.exponent = 1) :
    Nonempty (AwaySevenBaseTerminalUnitSectorPacket source r p) := by
  rcases nonempty_awaySevenBaseTerminalQuotientCorePacket source r p hbase with ⟨core⟩
  rcases nonempty_awaySevenBaseUnitEquationPacket core.carrier with ⟨unitSector⟩
  exact ⟨{ core := core, unitSector := unitSector }⟩

end DkMath.FLT.Seven