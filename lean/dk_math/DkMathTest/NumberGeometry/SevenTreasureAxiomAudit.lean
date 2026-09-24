/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry
import DkMath.FLT.Seven.NumberGeometryFourteenPhaseBridge
import DkMath.CosmicFormula.Rotation.CF2D.CycleDivision

#print "file: DkMathTest.NumberGeometry.SevenTreasureAxiomAudit"

namespace DkMathTest.NumberGeometry

open DkMath.NumberGeometry.Phase

#check FourteenPhase
#check FourteenPhase.complexFourteenPhase_fullTurn
#check FourteenPhase.complexFourteenPhase_halfTurn
#check FourteenPhase.evenSector_card
#check FourteenPhase.oddSector_card
#check FourteenPhase.evenSector_disjoint_oddSector
#check FourteenPhase.sector_card
#check FourteenPhase.even_seventh_equation
#check FourteenPhase.odd_seventh_equation
#check FourteenPhase.zeta_isPrimitiveRoot_seven

open DkMath.CosmicFormula.Rotation.CF2D

/-- The CF2D regular kernel has exact order fourteen. -/
theorem regularKernel_fourteen_exactOrder :
    orderOf (regularKernel 14) = 14 := by
  exact orderOf_regularKernel (by norm_num)

/-- The CF2D regular kernel completes its order-fourteen cycle. -/
theorem regularKernel_fourteen_pow_eq_one :
    regularKernel 14 ^ 14 = 1 := by
  exact regularKernel_pow_eq_one (by norm_num)

#check regularKernel_fourteen_exactOrder
#check regularKernel_fourteen_pow_eq_one

open DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt

#check eta14_sq
#check eta14_pow_seven
#check eta14_pow_fourteen
#check eta14_isPrimitiveRoot
#check degreeSixFourteenPhase_zeta
#check degreeSixFourteenPhase_evenPhase_one

#print axioms FourteenPhase.complexFourteenPhase_fullTurn
#print axioms FourteenPhase.complexFourteenPhase_halfTurn
#print axioms FourteenPhase.evenSector_card
#print axioms FourteenPhase.oddSector_card
#print axioms FourteenPhase.evenSector_disjoint_oddSector
#print axioms FourteenPhase.sector_card
#print axioms FourteenPhase.even_seventh_equation
#print axioms FourteenPhase.odd_seventh_equation
#print axioms FourteenPhase.zeta_isPrimitiveRoot_seven
#print axioms regularKernel_fourteen_exactOrder
#print axioms regularKernel_fourteen_pow_eq_one
#print axioms eta14_sq
#print axioms eta14_pow_seven
#print axioms eta14_pow_fourteen
#print axioms eta14_isPrimitiveRoot
#print axioms degreeSixFourteenPhase_zeta
#print axioms degreeSixFourteenPhase_evenPhase_one

end DkMathTest.NumberGeometry
