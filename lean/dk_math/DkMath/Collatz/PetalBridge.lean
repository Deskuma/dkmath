/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Basic
import DkMath.Collatz.PetalBridge.Residues
import DkMath.Collatz.PetalBridge.Profiles
import DkMath.Collatz.PetalBridge.Counts
import DkMath.Collatz.PetalBridge.Ratios
import DkMath.Collatz.PetalBridge.Mass
import DkMath.Collatz.PetalBridge.PressureCore
import DkMath.Collatz.PetalBridge.PressureCounts
import DkMath.Collatz.PetalBridge.HeightBudget
import DkMath.Collatz.PetalBridge.TailSplits
import DkMath.Collatz.PetalBridge.TailGrammar
import DkMath.Collatz.PetalBridge.DriftBudget
import DkMath.Collatz.PetalBridge.PressureDecay
import DkMath.Collatz.PetalBridge.PressureFrontier
import DkMath.Collatz.PetalBridge.PressureAccounting
import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction
import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis
import DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition
import DkMath.Collatz.PetalBridge.PressureAutomaton
import DkMath.Collatz.PetalBridge.PressureBeam
import DkMath.Collatz.PetalBridge.PressureState
import DkMath.Collatz.PetalBridge.OneCycle
import DkMath.Collatz.PetalBridge.ValuationFlowBridge
import DkMath.Collatz.PetalBridge.Collision

#print "file: DkMath.Collatz.PetalBridge"

/-!
# Collatz Petal Bridge

This file is a small observation window between the accelerated Collatz
dynamics and the Petal range-family API.

The bridge is intentionally thin.  It does not claim any Collatz convergence
or nontrivial cycle theorem.  It only fixes the common language:

```text
accelerated Collatz orbit segment
  -> range-indexed labels
  -> either pairwise separated, or a collision closes that route as False
```

For Petal/ABC routes, a repeated label means that a proposed independent
range-family cannot be counted as `k` independent carriers.  For Collatz
dynamics, the same collision is not merely a failure: it is the observable
shape of a merge, fold, or cycle candidate.

## Checkpoint 125 trajectory correction

This file is now treated as the finite observation and pressure/margin surface.
Do not keep adding low-level Collatz vocabulary here by default.  The revised
low-level subject is:

```text
Odd gnomon correction
  n + (2n+1) = 3n+1

Pow2 alignment evaluation
  v2 (3n+1)

Residual shape extraction
  (3n+1) / 2^height

Relative scale update
  the residual odd shape becomes the next state
```

That vocabulary starts in `DkMath.Collatz.GnomonEvaluation`.  The role of this
file is to observe finite windows of those shapes and compare retention versus
continuation masses.

Important warning for future agents: pressure selection is **not** a raw
carrier-membership nesting statement.  The carrier sets are nested, but
pressure compares two changing masses:

```text
retention(depth) < 2 * continuation(depth)
```

Therefore the selected pressure depths need not form an unconditional prefix.
Checkpoint 125 adds explicit prefix-failure predicates below so those cases
remain first-class evidence instead of being erased by an unsafe monotonicity
assumption.
-/

namespace DkMath.Collatz

--

end DkMath.Collatz
