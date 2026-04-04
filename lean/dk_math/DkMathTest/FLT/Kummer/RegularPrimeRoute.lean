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
-/

-- §1. Basic: descentExistence_exists_iff_gnReduction_exists (no sorry expected)
#print axioms DkMath.FLT.descentExistence_exists_iff_gnReduction_exists -- OK: no sorry

-- §2. GapDivisibleBranch
-- no-sorry
#print axioms DkMath.FLT.qAdicGapReduction_qNeP_of_regularAndGapDivisible -- OK: no sorry
-- no-sorry (witness R 自動構成 completed ✅)
#print axioms DkMath.FLT.qAdicGapReductionRegularBranch_of_global -- OK: no sorry

-- §3. CyclotomicPrincipalization
-- no-sorry (Stage 1 composition)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_stage1Split -- OK: no sorry
-- no-sorry (自明: statement 同値)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization -- OK: no sorry
-- no-sorry (3-stage composition)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_threeStages -- OK: no sorry
-- sorry (thinnest geometry witness kernel)
#print axioms DkMath.FLT.cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry -- uses sorry
-- no-sorry (class-group side placeholder bridge)
#print axioms DkMath.FLT.cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree -- OK: no sorry
-- no-sorry (principal-ideal extraction placeholder)
#print axioms DkMath.FLT.cyclotomicPrincipalIdealExtraction_of_classTrivialization -- OK: no sorry
-- no-sorry (refined Stage 1 composition)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_refinedStage1Route -- OK: no sorry if stage assumptions are clean
-- sorry (legacy one-shot wrapper)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree -- uses sorry
-- sorry (thinner Stage 1 kernel)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_classGroupPTorsionFree -- uses sorry

-- §4. ClassGroupBridge
-- no-sorry (trivial)
#print axioms DkMath.FLT.classGroupPTorsionFree_of_regularPrime -- OK: no sorry
-- sorry (chain through cyclotomicPrincipalization)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_regularPrime -- uses sorry

-- §5. RegularPrimeRoute
-- no-sorry (pure composition)
#print axioms DkMath.FLT.qAdicGapReductionPure_of_threeWaySplit -- OK: no sorry
-- no-sorry (refined Stage 1 route)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedStage1Route -- OK: no sorry if stage assumptions are clean
-- no-sorry (refined ideal / unit / norm route)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedKummerRoute -- OK: no sorry if stage assumptions are clean
-- sorry (refined class-group route still depends on Stage 1 kernel)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedClassGroupRoute -- uses sorry
-- sorry (chain through class-group principalization)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerThreeWaySplit -- uses sorry
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute -- uses sorry
