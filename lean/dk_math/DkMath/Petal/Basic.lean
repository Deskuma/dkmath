/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalDetect

#print "file: DkMath.Petal.Basic"

/-!
# Petal Basics

This file starts the `DkMath.Petal.*` package.

The first implementation phase keeps the existing FLT files in place and gives
the Petal viewpoint a stable import path.  The package can then grow by adding
Petal-facing bridge theorem names without disrupting downstream FLT files.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect

/-- Petal-facing alias for the natural-number completed phase form. -/
abbrev S0Nat (a b : ℕ) : ℕ := S0_nat a b

/-- Petal-facing alias for the natural-number full square phase form. -/
abbrev S1Nat (a b : ℕ) : ℕ := S1_nat a b

end Petal
end DkMath
