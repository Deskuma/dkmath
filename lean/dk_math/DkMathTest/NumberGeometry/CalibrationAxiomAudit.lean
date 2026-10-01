/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry

/-!
# Axiom audit for the NGEO-006 calibration bridges

The audit checks the public bridge declarations and prints their transitive
axioms.  The substantive results are exact algebraic calibrations only.
-/

#check DkMath.NumberGeometry.Bridge.SilverRatio.ofPair
#check DkMath.NumberGeometry.Bridge.SilverRatio.pairMass_ofPair_eq_dist_sq
#check DkMath.NumberGeometry.Bridge.SilverRatio.bcfg_common_massLevel
#check DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_egyptianW
#check DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_radiusThreePoint
#check DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_keyN
#check DkMath.NumberGeometry.Examples.EgyptianCircle.egyptianW_mem_massLevelSet
#check DkMath.NumberGeometry.Examples.EgyptianCircle.radiusThreePoint_mem_massLevelSet

#print axioms DkMath.NumberGeometry.Bridge.SilverRatio.pairMass_ofPair_eq_dist_sq
#print axioms DkMath.NumberGeometry.Bridge.SilverRatio.bcfg_common_massLevel
#print axioms DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_egyptianW
#print axioms DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_radiusThreePoint
#print axioms DkMath.NumberGeometry.Examples.EgyptianCircle.pairMass_origin_keyN
#print axioms DkMath.NumberGeometry.Examples.EgyptianCircle.egyptianW_mem_massLevelSet
#print axioms DkMath.NumberGeometry.Examples.EgyptianCircle.radiusThreePoint_mem_massLevelSet
