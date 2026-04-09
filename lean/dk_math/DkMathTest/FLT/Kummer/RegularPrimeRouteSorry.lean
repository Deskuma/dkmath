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

ここに列挙されている定理は、RegularPrimeRoute.lean の定理のうち、まだ `sorryAx` を含む定理である。
no-sorry となった場合は `RegularPrimeRouteNoSorry.lean` へ写し `no-sorry` 表記へ変更する。
-/

-- §1. Basic: descentExistence_exists_iff_gnReduction_exists (no sorry expected)

-- §2. GapDivisibleBranch

-- §3. CyclotomicPrincipalization

-- `sorry` (legacy one-shot wrapper)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree -- uses sorry

-- §4. ClassGroupBridge
-- `sorry` (still blocked by full principalization stage)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_regularPrime -- uses sorry

-- §5. RegularPrimeRoute

-- §5a. Stage 3a combinatorial bridge + NormEqGN concrete
-- `sorry` (isolated non-first-case peel normal-form descent existence core)
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree -- uses sorry
-- `sorry` only via the isolated non-first-case peel normal-form descent existence core
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_classGroupPTorsionFree -- uses sorry via peel normal-form descent existence core
-- `sorry` only via the isolated non-first-case peel normal-form descent existence core
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree -- uses sorry via named smaller-counterexample target
-- `sorry` only via the isolated non-first-case peel normal-form descent existence core
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree -- uses sorry via peel normal-form descent existence core
-- `sorry` only via the isolated non-first-case peel normal-form descent existence core
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree -- uses sorry via peel normal-form descent existence core
-- `sorry` only via the isolated non-first-case peel normal-form descent existence core
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree -- uses sorry
-- `sorry` only via the isolated non-first-case PacketFromError kernel
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree -- uses sorry via non-first-case packetFromError target
-- `sorry` only via the isolated non-first-case PacketFromError kernel
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseReduction_of_classGroupPTorsionFree -- uses sorry via non-first-case packetFromError target
-- `sorry` only via the isolated non-first-case PacketFromError kernel
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree -- uses sorry via non-first-case packetFromError target
-- `sorry` only via the isolated non-first-case existence kernel
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCaseDescent_of_classGroupPTorsionFree -- uses sorry via non-first-case existence target
-- `sorry` only via the isolated non-first-case existence kernel
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree -- uses sorry via non-first-case existence target
-- `sorry` only via the isolated non-first-case existence kernel
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree -- uses sorry via non-first-case existence target
-- `sorry` only via the isolated non-first-case existence kernel
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute -- uses sorry via non-first-case existence target
