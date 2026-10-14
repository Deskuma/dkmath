/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.StateProjectionTransport

#print "file: DkMathTest.Tromino.StateProjectionTransportAxiomAudit"

open DkMath.Tromino

#print axioms RootedChamberTransport.map_steps
#print axioms RootedChamberTransport.lift_steps
#print axioms RootedChamberTransport.reachable_iff_admissibleChamber
#print axioms RootedChamberTransport.admissibleChamber_iff_exists_reachable_project_eq
#print axioms RootedChamberTransport.childStep_iff_restricted_projected
#print axioms mutableColorProjection_injective_of_agreesOutside
#print axioms sameMutableProjection_iff
