/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.KempeRepair

#print "file: DkMathTest.Tromino.KempeRepairAxiomAudit"

open DkMath.Tromino

#print axioms onePointRecolor_symm
#print axioms kempeReachable_singleton_of_onePointRecolor
#print axioms onePointRecolor_exchange_bridge
#print axioms onePointRecolor_singletonKempeMove
#print axioms singletonKempeMove_symmetric
#print axioms singletonKempe_repairHeight_unit_slope
