/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalCoreUnit

#print "file: DkMath.Petal.CoreUnit"

/-!
# Petal Core Unit Surface

This file gives the current Petal unit and phase vocabulary a stable
`DkMath.Petal.*` import path.
-/

namespace DkMath
namespace Petal

/-- Petal-facing alias for the current core-unit state. -/
abbrev CoreUnit := DkMath.FLT.PetalCoreUnit

end Petal
end DkMath
