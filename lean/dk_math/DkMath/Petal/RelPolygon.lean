/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.UnitCycle.RelPolygon

#print "file: DkMath.Petal.RelPolygon"

/-!
# Petal Relative Polygon Surface

This file gives the relative polygon state model a Petal-facing import path.

The implementation is currently owned by `DkMath.UnitCycle.RelPolygon`; this
module is the stable package surface for future Petal refactoring.
-/

namespace DkMath
namespace Petal

/-- Petal-facing alias for the current relative polygon state type. -/
abbrev RelPolygonState := DkMath.UnitCycle.RelPolygon.RPState

end Petal
end DkMath
