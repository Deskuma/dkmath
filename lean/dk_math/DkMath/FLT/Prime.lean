/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Prime.CounterexampleRouting
import DkMath.FLT.Prime.AdicPowerSplit
import DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
import DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
import DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
import DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
import DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
import DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
import DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
import DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver

/-!
# Public FLT prime architecture facade

This file is an import-only discovery facade for the bounded odd-prime
TraceOne architecture.  It exposes the honest two-branch counterexample route,
the adic/coordinate and conditional ideal-power APIs, and the calibrated
p = 3, 5, 7 and real-sector receivers.

The facade is an architecture boundary, not a proof of general FLT.  The
ramified branch enters a `PrimeAdicFactorPacket`; the away branch stops at the
simultaneous `p`-th-power split.  The imaginary generic route still has the
class-group coprimality frontier, while the real route retains its sector
obstruction and the p = 5 packet-to-Golden bridge frontier.
-/

#print "file: DkMath.FLT.Prime"
