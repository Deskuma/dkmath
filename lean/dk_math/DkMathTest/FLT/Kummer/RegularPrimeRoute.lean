/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeRoute

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Kummer Branch Test — axioms 監視

Kummer branch の各 theorem の axiom 依存を監視する。
sorry を使っている theorem はそれとして識別し、
no-sorry の theorem が意図せず sorry に汚染されていないことを確認する。

ここは新規に作られた定理の早期チェックのための専用ファイルである。
ビルド時間が長くなったので、既に確認済みの定理は、

- `RegularPrimeRouteNoSorry.lean`
- `RegularPrimeRouteSorry.lean`

へ、移してある。上記、Test Lean は、適宜確認してステータスの変化がないかを監視する。

ここに置くべき `#print axioms` 監視は、`RegularPrimeRoute.lean` の定理の新規実装定理の確認限定である。
-/

section NoSorry
#print "section: begin == no-sorry =="
-- ====================================================================================================================
-- no-sorry
-- ====================================================================================================================
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_normDescent
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalForm_q_dvd_t_not_dvd_s
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistence_of_packet_xyEq
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_hzEq
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_normalFormDescent
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_normDescent
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_normDescent
#print axioms DkMath.FLT.cyclotomicNormDescent_of_refinedClassGroupRoute
#print axioms DkMath.FLT.cyclotomicNormDescent_of_caseSplit
#print axioms DkMath.FLT.cyclotomicNormEqGN_concrete_unitNormalizedChosenFactor
#print axioms DkMath.FLT.cyclotomicNormUnitAbsorb_concrete_unitNormalizedChosenFactor
#print axioms DkMath.FLT.cyclotomicNormGNPower_concrete_unitNormalizedChosenFactor
#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_gnPowerReceiver
#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCase_of_unitNormalizationAndReceiver
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_refinedClassGroupRoute
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_refinedClassGroupRoute
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_namedSmallerCounterexampleTarget
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_packetQuotientLift

#print "section: end == no-sorry =="
end NoSorry
-- --------------------------------------------------------------------------------------------------------------------


section viaSorryAx
#print "section: begin == via-sorry =="
-- ====================================================================================================================
-- `sorry`
-- ====================================================================================================================
#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization
#print axioms DkMath.FLT.cyclotomicNormDescent_of_classGroupPTorsionFree_and_nonFirstCase
#print axioms DkMath.FLT.cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree_and_unitNormalization
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree_and_unitNormalization
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_and_unitNormalization
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_reducesTo_unitNormalization
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute

#print "section: end == via-sorry =="
end viaSorryAx
