/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.GEisensteinBridge
import DkMath.FLT.Kummer
import DkMath.FLT.Main
import DkMath.FLT.PrimeProvider
import DkMath.FLT.Samples
import DkMath.FLT.Five
import DkMath.FLT.Seven
import DkMath.FLT.QuadraticEssence

#print "file: DkMath.FLT"

set_option linter.style.longLine false

/-!
# DkMath FLT historical broad aggregator

`DkMath.FLT` is a broad compatibility/research aggregator that predates the
independent completed exponent-three public surface.  It still imports legacy
`Main`, Kummer/provider research, FLT5, FLT7 research, and related bridge
modules, so it is intentionally **not** the canonical discovery import for the
current standalone FLT3 proof.

For completed exponent-specific public results, prefer explicit imports:

```lean
import DkMath.FLT.Three
import DkMath.FLT.Five
```

with endpoints:

- `DkMath.FLT.Three.fermatThree_no_positive_solution`
- `DkMath.FLT.Five.fermatFive_no_positive_solution`

For the current odd-prime generalization architecture, see `DkMath.FLT.Prime.*`
and `docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`.

For neutral reusable mathematics extracted from FLT and other research owners,
prefer `DkMath.Lib` where an appropriate promoted API exists.

No import semantics are changed by this documentation note: in particular,
`DkMath.FLT.Three` remains an explicit independent import rather than being
silently added to this historical aggregator.
-/
