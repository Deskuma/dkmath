/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RepairDistance

#print "file: DkMathTest.Tromino.RepairDistanceAxiomAudit"

open DkMath.Tromino

#print axioms Steps.concat
#print axioms Steps.reverse_of_symmetric
#print axioms repairHeight_spec
#print axioms repairHeight_minimal
#print axioms repairHeight_unit_slope
