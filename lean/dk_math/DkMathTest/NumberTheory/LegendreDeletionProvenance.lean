/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreDeletion1031Calibration
import DkMathTest.NumberTheory.LegendreSqrtQuotientCalibration

#print "file: DkMathTest.NumberTheory.LegendreDeletionProvenance"

namespace DkMathTest.LegendreDeletionProvenance

open DkMath.NumberTheory.Legendre

/-- The same existential conclusion is preserved via two separately named routes. -/
theorem both1031_named_routes :
    (∃ p, p.Prime ∧ SquareCell 1031 p) ∧ (∃ p, p.Prime ∧ SquareCell 1031 p) :=
  ⟨DkMathTest.LegendreDeletion1031Calibration.exists_prime_squareCell_1031_of_coarseTownDeletion,
    DkMathTest.LegendreSqrtQuotientCalibration.quotient1031_structural_endpoint⟩

end DkMathTest.LegendreDeletionProvenance
