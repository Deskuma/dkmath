/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveBeam

#print "file: DkMath.NumberTheory.PrimitiveBeamExamples"

set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.PrimitiveBeamExamples

open DkMath.NumberTheory.PrimitiveBeam
open DkMath.CosmicFormulaBinom

/-- Smallest clean Beam example: `2^5 - 1 = GN 5 1 1 = 31`. -/
example : GN 5 1 1 = 31 := by
  decide

/-- `3^5 - 1 = (3 - 1) * GN 5 2 1 = 2 * 121`. -/
example : GN 5 2 1 = 121 := by
  decide

example : 11 ∣ GN 5 2 1 := by
  decide

example : ¬ 11 ∣ 2 := by
  decide

end DkMath.NumberTheory.PrimitiveBeamExamples
