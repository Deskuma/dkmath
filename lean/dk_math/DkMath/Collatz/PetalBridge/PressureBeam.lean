/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureBeam.Pulse

#print "file: DkMath.Collatz.PetalBridge.PressureBeam"

namespace DkMath.Collatz

/-
Public aggregator for the Beam-facing pressure boundary.

Checkpoint 225 mechanically split the former monolithic `PressureBeam.lean`
without changing public theorem names or theorem statements:

* `PressureBeam.Core` keeps the seed, addressed-depth, and mass-balance core;
* `PressureBeam.Edge` keeps crossing/falling edge vocabulary and edge bridges;
* `PressureBeam.Pulse` keeps local pulse packaging and diagnostic projections.

This file remains the public import surface.  No new mathematical strength is
introduced here.
-/

end DkMath.Collatz
