/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.RestorationFlipTransport

#print "file: DkMathTest.Tromino.RestorationFlipTransportAxiomAudit"

namespace DkMathTest.Tromino.RestorationFlipTransportAxiomAudit

open DkMath.Tromino

#print axioms SingleEdgeReplacement.adj_unchanged
#print axioms SingleEdgeReplacement.adj_at_unchanged
#print axioms properOnColored_parent_to_child
#print axioms properOnColored_child_to_parent
#print axioms missingAt_flip_locality
#print axioms exactRestorationSector_iff
#print axioms childAdmissibleRestorationStep_iff_transport
#print axioms steps_transport_of_child_reachable
#print axioms steps_child_of_transport
#print axioms exactRestorationSectorTransport
#print axioms exactRestorationSectorTransport_chamber_iff

end DkMathTest.Tromino.RestorationFlipTransportAxiomAudit
