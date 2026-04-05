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
-- no-sorry (DkMath-native local factorization core)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_mul_eq_sub_pow -- OK: no sorry
-- no-sorry (local factorization core target)
#print axioms DkMath.FLT.cyclotomicLocalFactorizationCore -- OK: no sorry
-- no-sorry (local FLT-equation specialization)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_mul_eq_of_add_pow_eq -- OK: no sorry
-- no-sorry (local FLT-equation factorization core target)
#print axioms DkMath.FLT.cyclotomicLocalEquationFactorizationCore -- OK: no sorry
-- no-sorry (local FLT-equation core → equation-level target)
#print axioms DkMath.FLT.cyclotomicEquationFactorizationIdentity_of_localEquationCore -- OK: no sorry
-- no-sorry (generic→Nat specialization)
#print axioms DkMath.FLT.cyclotomicEquationFactorizationIdentity_of_genericIdentity -- OK: no sorry
-- no-sorry (equation-only→prime specialization)
#print axioms DkMath.FLT.cyclotomicPrimeFactorizationSpecialization_of_equationIdentity -- OK: no sorry
-- no-sorry (prime→abstract identity)
#print axioms DkMath.FLT.cyclotomicAbstractFactorizationIdentity_of_primeSpecialization -- OK: no sorry
-- no-sorry (abstract→pack specialization composition)
#print axioms DkMath.FLT.cyclotomicCounterexampleFactorizationSpecialization_of_abstractIdentity -- OK: no sorry
-- no-sorry (pack→prime-ge5 specialization)
#print axioms DkMath.FLT.cyclotomicPureFactorizationIdentity_of_counterexampleSpecialization -- OK: no sorry
-- no-sorry (Stage 1a-1a composition)
#print axioms DkMath.FLT.cyclotomicFactorizationIdentity_of_stage1a1aSplit -- OK: no sorry
-- no-sorry (Stage 1a-1 composition)
#print axioms DkMath.FLT.cyclotomicIdealFactorization_of_stage1a1Split -- OK: no sorry
-- no-sorry (Stage 1a composition)
#print axioms DkMath.FLT.cyclotomicIdealClassPTorsionWitness_of_stage1aSplit -- OK: no sorry
-- no-sorry (Stage 1 composition)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_stage1Split -- OK: no sorry
-- no-sorry (自明: statement 同値)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization -- OK: no sorry
-- no-sorry (3-stage composition)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_threeStages -- OK: no sorry
-- no-sorry (generic factorization target currently closes as placeholder)
#print axioms DkMath.FLT.cyclotomicGenericFactorizationIdentity_overCommSemiring -- OK: no sorry
-- no-sorry (equation-only target closed via local core)
#print axioms DkMath.FLT.cyclotomicEquationFactorizationIdentity_of_diophantineEquation -- OK: no sorry
-- no-sorry (abstract factorization wrapper through equation-only kernel)
#print axioms DkMath.FLT.cyclotomicAbstractFactorizationIdentity_of_fltEquation -- OK: no sorry
-- no-sorry (prime-ge5 pure factorization wrapper through abstract kernel)
#print axioms DkMath.FLT.cyclotomicPureFactorizationIdentity_of_counterexampleGeometry -- OK: no sorry
-- no-sorry (gap-divisible specialization bridge)
#print axioms DkMath.FLT.cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity -- OK: no sorry
-- no-sorry (specialized factorization wrapper through pure kernel)
#print axioms DkMath.FLT.cyclotomicFactorizationIdentity_of_gapDivisibleGeometry -- OK: no sorry
-- no-sorry (ideal equation packaging bridge)
#print axioms DkMath.FLT.cyclotomicIdealEquation_of_factorizationIdentity -- OK: no sorry
-- no-sorry (ideal factorization wrapper through identity kernel)
#print axioms DkMath.FLT.cyclotomicIdealFactorization_of_gapDivisibleGeometry -- OK: no sorry
-- no-sorry (ideal product p-th power bridge)
#print axioms DkMath.FLT.cyclotomicIdealProductPthPower_of_idealFactorization -- OK: no sorry
-- no-sorry (class witness from ideal product)
#print axioms DkMath.FLT.cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower -- OK: no sorry
-- no-sorry (Stage 1a wrapper through factorization kernel)
#print axioms DkMath.FLT.cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry -- OK: no sorry
-- sorry (class-group p-torsion free → generic annihilation bridge)
#print axioms DkMath.FLT.cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree -- uses sorry
-- no-sorry (principal-ideal extraction generic API)
#print axioms DkMath.FLT.cyclotomicPrincipalIdealExtraction_of_classTrivialization -- OK: no sorry
-- no-sorry (integral ideal helper via mk0_eq_one_iff)
#print axioms DkMath.FLT.idealIsPrincipal_of_classGroupMk0_eq_one -- OK: no sorry
-- no-sorry (refined Stage 1 composition)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_refinedStage1Route -- OK: no sorry if stage assumptions are clean
-- sorry (legacy one-shot wrapper)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree -- uses sorry
-- no-sorry only through the class-group annihilation bridge
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
