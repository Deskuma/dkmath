/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.MassBridge
import DkMath.ABC.ValuationFlowBridge

#print "file: DkMath.ABC.Bridge"

/-!
Public-facing aggregator for the Erdos #1196 bridge layer.

This file intentionally re-exports only the thin bridge surface:

- `supportMass`
- prime-channel-family lower bounds on `supportMass`
- primitive-witness-family lower bounds on diff support mass
- `PrimitiveWitnessFamily` and its packaged bridge API
-/
