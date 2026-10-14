/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.Tromino.OBS019Neighbor01Calibration

#print "file: DkMathTest.Tromino.OBS019Neighbor01AxiomAudit"

open DkMath.Tromino
open DkMathTest.Tromino

/-! # OBS-019 neighbor-01 dependency audit

The calibration is intentionally test-local. This file records the dependency
surface of the generic transport theorems and of the finite witness proofs;
it does not introduce a production theorem or any new foundational assumption.
-/

#print axioms DkMath.Tromino.RootedChamberTransport.map_steps
#print axioms DkMath.Tromino.RootedChamberTransport.lift_steps
#print axioms DkMath.Tromino.RootedChamberTransport.reachable_iff_admissibleChamber
#print axioms DkMath.Tromino.RootedChamberTransport.childStep_iff_restricted_projected
#print axioms DkMathTest.Tromino.project_injective
#print axioms DkMathTest.Tromino.neighbor01_edge_exact
#print axioms DkMathTest.Tromino.neighbor01_transport
#print axioms DkMathTest.Tromino.neighbor01_chamber_equivalence
#print axioms DkMathTest.Tromino.neighbor01_parent_component_exact
#print axioms DkMathTest.Tromino.obs019Neighbor01_provenance
#print axioms DkMathTest.Tromino.obs019Neighbor01_frozen_parent_heights
