/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic
import DkMath.Petal.Forms
import DkMath.Petal.RelPolygon
import DkMath.Petal.CoreUnit
import DkMath.Petal.Counting
import DkMath.Petal.Address
import DkMath.Petal.GNBridge
import DkMath.Petal.GcdBridge
import DkMath.Petal.PadicBridge
import DkMath.Petal.PrimitiveBridge
import DkMath.Petal.ReducedSupport
import DkMath.Petal.Anchor
import DkMath.Petal.BoundaryD3
import DkMath.Petal.EisensteinBridge
import DkMath.Petal.ZsigmondyD3Bridge
import DkMath.Petal.PrimitiveD3ValuationBridge

#print "file: DkMath.Petal"

/-!
# DkMath Petal Package

Petal collects the relative polygon / `S0` / `GN` bridge surface.

The first phase is intentionally thin: it exposes the existing FLT and
UnitCycle theorem base through a stable package path, then adds focused bridge
theorems that will support primitive-factor and Zsigmondy-facing work.

The import order is arranged as the public story of the package:

```text
basic forms / relative polygon vocabulary
  -> counting and address layers
  -> GN/GCD/p-adic/primitive bridges
  -> reduced support and anchored carriers
  -> BoundaryD3 cubic branch split
  -> shifted Eisenstein norm bridge
  -> Zsigmondy d = 3 primitive-divisor bridge
  -> squarefree GN3 valuation bridge
```

This is not a claim that every import is logically minimal.  Some files still
carry temporary dependencies that are documented at their module headers and
should be reconsidered during the planned `DkMath.Lib.*` promotion refactor.
-/

namespace DkMath
namespace Petal

-- Package namespace.

end Petal
end DkMath
