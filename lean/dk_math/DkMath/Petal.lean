/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic
import DkMath.Petal.ReducedSupport
import DkMath.Petal.Counting
import DkMath.Petal.Address
import DkMath.Petal.Forms
import DkMath.Petal.RelPolygon
import DkMath.Petal.CoreUnit
import DkMath.Petal.GNBridge
import DkMath.Petal.GcdBridge
import DkMath.Petal.PadicBridge
import DkMath.Petal.PrimitiveBridge
import DkMath.Petal.Anchor
import DkMath.Petal.BoundaryD3
import DkMath.Petal.EisensteinBridge

#print "file: DkMath.Petal"

/-!
# DkMath Petal Package

Petal collects the relative polygon / `S0` / `GN` bridge surface.

The first phase is intentionally thin: it exposes the existing FLT and
UnitCycle theorem base through a stable package path, then adds focused bridge
theorems that will support primitive-factor and Zsigmondy-facing work.
-/

namespace DkMath
namespace Petal

-- Package namespace.

end Petal
end DkMath
