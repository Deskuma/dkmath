/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.PortTriangularReduction

#print "file: DkMathTest.Tromino.PortTriangularReductionAxiomAudit"

/-!
# Universal triangular reduction axiom audit

This audit checks the indexing-free face-star reductions and the equivalence
packaging of triangular and general genus-zero targets.
-/

namespace DkMathTest.Tromino

open DkMath.Tromino

/-! ## Indexing-free reductions -/

#check exists_faceStarGenusZeroTriangulation
#check exists_faceStarGenusZeroTetrahedralReduction

/-! ## Universal target schemas -/

#check PortGenusZeroTriangularFourColorTarget
#check portGenusZeroFourColorTarget_imp_triangular
#check portGenusZeroTriangularFourColorTarget_imp_general
#check portGenusZeroTriangularFourColorTarget_iff_fourColorTarget
#check PortGenusZeroTriangularTetrahedralTarget
#check portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget
#check portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget

/-! ## Axiom dependencies of the branch-closing declarations -/

#print axioms exists_faceStarGenusZeroTriangulation
#print axioms portGenusZeroTriangularFourColorTarget_iff_fourColorTarget
#print axioms portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget
#print axioms portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget

end DkMathTest.Tromino
