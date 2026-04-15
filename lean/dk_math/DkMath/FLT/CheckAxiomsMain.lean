/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Main

#print "file: DkMath.FLT.CheckAxiomsMain"

set_option linter.style.longLine false

/-!
- `Main.lean`
  - 最終定理群の公開面。
  - 主要入口: README.md 参照 2026/02/25 14:03 現在
    - `FLT_d3_by_padicValNat`
    - `FLT_d3_by_padicValNat_of_NoSqOnS0`
    - `FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport`
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput`
    - `FLT_d3_by_padicValNat_of_harmonicEnvelope_*`
    - `FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport`
    - `FLT_d3_by_padicValNat_of_GEisensteinCore_with_reachability_coprimeSupport`
    - `FLT_d3_by_padicValNat_of_GEisensteinCore_via_reachability_coprimeSupport`
    - `GEisenstein_descent_reaches_zero_of_core`
    - `GEisenstein_descent_reaches_zero_of_descentClassify_primitiveSized`
    - `FLT_d3_by_padicValNat_of_DescentBaseInput`
    - `FLT_d3_by_padicValNat_of_NoSqInput`
-/

namespace DkMath.FLT

-- Check axioms of main theorems.

-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_NoSqOnS0
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_GEisensteinCore_with_reachability_coprimeSupport
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_GEisensteinCore_via_reachability_coprimeSupport
-- TODO: [DkMathTest]: #print axioms GEisenstein_descent_reaches_zero_of_core
-- TODO: [DkMathTest]: #print axioms GEisenstein_descent_reaches_zero_of_descentClassify_primitiveSized
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_DescentBaseInput
-- TODO: [DkMathTest]: #print axioms FLT_d3_by_padicValNat_of_NoSqInput

end DkMath.FLT

-- Latest check: 2026/02/25 14:02

/- $ ./lean-build.sh -v DkMath.FLT.CheckAxiomsMain | grep -A2 "info: "
info: DkMath/FLT/CheckAxiomsMain.lean:27:0: 'DkMath.FLT.FLT_d3_by_padicValNat' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:28:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_NoSqOnS0' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:29:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:30:0: 'DkMath.FLT.FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:31:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:32:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:33:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:34:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:35:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:36:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_GEisensteinCore_with_reachability_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:37:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_GEisensteinCore_via_reachability_coprimeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:38:0: 'DkMath.FLT.GEisenstein_descent_reaches_zero_of_core' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:39:0: 'DkMath.FLT.GEisenstein_descent_reaches_zero_of_descentClassify_primitiveSized' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:40:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_DescentBaseInput' depends on axioms: [propext, Classical.choice, Quot.sound]
info: DkMath/FLT/CheckAxiomsMain.lean:41:0: 'DkMath.FLT.FLT_d3_by_padicValNat_of_NoSqInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
