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
-- no-sorry (local principal-ideal product identity)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideal_mul_eq_span_x_pow_of_add_pow_eq -- OK: no sorry
-- no-sorry (local principal-ideal p-th-power identity)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq -- OK: no sorry
-- no-sorry (general comaximal linear-factor ideal lemma)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideals_sup_eq_top_of_sub_isUnit -- OK: no sorry
-- no-sorry (Kummer-style comaximal linear-factor ideal lemma)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit -- OK: no sorry
-- no-sorry (ideal-level coprimality of linear factors)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideals_isCoprime_of_mul_sub_isUnit -- OK: no sorry
-- no-sorry (pairwise-coprime linear-factor ideals satisfy inf = product)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit -- OK: no sorry
-- no-sorry (Dedekind finite-family prime-power inf = product)
#print axioms DkMath.FLT.dedekindInfPrimePowEqProd -- OK: no sorry
-- no-sorry (Dedekind finite-family quotient/product CRT equivalence)
#print axioms DkMath.FLT.dedekindQuotientEquivPiOfFinsetProdEq -- OK: no sorry
-- no-sorry (Dedekind finite-family representative existence)
#print axioms DkMath.FLT.dedekindExistsRepresentativeModFinset -- OK: no sorry
-- no-sorry (Dedekind ideal factor-count receiver)
#print axioms DkMath.FLT.dedekindIdealCountNormalizedFactorsEq -- OK: no sorry
-- no-sorry (2-ideal p-th-root theorem under coprimality)
#print axioms DkMath.FLT.dedekindIdealEqPowOfMulEqPowOfIsCoprime -- OK: no sorry
-- no-sorry (factor-vs-rest coprimality helper)
#print axioms DkMath.FLT.dedekindIdealIsCoprimeProdErase -- OK: no sorry
-- no-sorry (rest-product nonvanishing helper)
#print axioms DkMath.FLT.dedekindIdealProdEraseNeBot -- OK: no sorry
-- no-sorry (coprime to each factor implies coprime to their product)
#print axioms DkMath.FLT.idealIsCoprime_prod_of_forall -- OK: no sorry
-- no-sorry (finite product of principal ideals is principal by product of generators)
#print axioms DkMath.FLT.span_singleton_finset_prod -- OK: no sorry
-- no-sorry (finite-family each-pth-power theorem)
#print axioms DkMath.FLT.dedekindIdealEqPowOfProdEqPowOfPairwise -- OK: no sorry
-- no-sorry (principal p-th power gives class-group p-torsion witness)
#print axioms DkMath.FLT.dedekindClassGroupMk0PowEqOneOfEqPowAndIsPrincipal -- OK: no sorry
-- no-sorry (finite-family ideal arithmetic gives class-group witness family)
#print axioms DkMath.FLT.dedekindClassGroupPowWitnessOfProdEqPowOfPairwise -- OK: no sorry
-- no-sorry (generator-level coprimality from unit difference)
#print axioms DkMath.FLT.CyclotomicLocalFactorizationContext.linear_factors_isCoprime_of_mul_sub_isUnit -- OK: no sorry
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
-- no-sorry (concrete class-group p-torsion-free target → generic annihilation bridge)
#print axioms DkMath.FLT.cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree -- OK: no sorry
-- no-sorry (principal-ideal extraction generic API)
#print axioms DkMath.FLT.cyclotomicPrincipalIdealExtraction_of_classTrivialization -- OK: no sorry
-- no-sorry (integral ideal helper via mk0_eq_one_iff)
#print axioms DkMath.FLT.idealIsPrincipal_of_classGroupMk0_eq_one -- OK: no sorry
-- no-sorry (principal generators differ by a unit)
#print axioms DkMath.FLT.principalGeneratorsUnitMulOfSpanEq -- OK: no sorry
-- no-sorry (`(a) = (b)^n` gives `a = u * b^n`)
#print axioms DkMath.FLT.unitMulPowOfSpanEqPowIdeal -- OK: no sorry
-- no-sorry (principal ideal generator version of Stage 2 core)
#print axioms DkMath.FLT.unitMulPowOfSpanEqPowPrincipal -- OK: no sorry
-- no-sorry (linear factor specialization of Stage 2 core)
#print axioms DkMath.FLT.linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal -- OK: no sorry
-- no-sorry (local Stage 2 unit-normalization core)
#print axioms DkMath.FLT.cyclotomicLocalUnitNormalizationCore -- OK: no sorry
-- no-sorry (generic principal root ideal existence from torsion annihilation)
#print axioms DkMath.FLT.principalRootIdealExistsOfEqPowAndTorsionKill -- OK: no sorry
-- no-sorry (root ideal nonzero recovered from a pth-power equality)
#print axioms DkMath.FLT.rootIdealNeBotOfEqPow -- OK: no sorry
-- no-sorry (linear factor nonzero recovered from equality plus root nonzero)
#print axioms DkMath.FLT.linearFactorNeZeroOfSpanEqPow -- OK: no sorry
-- no-sorry (local linear-factor root-ideal existence exact receiver)
#print axioms DkMath.FLT.linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill -- OK: no sorry
-- no-sorry (local linear-factor root-ideal existence from root nonzero)
#print axioms DkMath.FLT.linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot -- OK: no sorry
-- no-sorry (explicit Stage 1 output pieces -> existential boundary target)
#print axioms DkMath.FLT.cyclotomicLinearFactorIdealPthPower_of_spanEqPow -- OK: no sorry
-- no-sorry (generic 2-factor receiver: product + coprime -> explicit equality)
#print axioms DkMath.FLT.linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime -- OK: no sorry
-- no-sorry (2-factor route -> Stage 1 explicit equality target)
#print axioms DkMath.FLT.cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime -- OK: no sorry
-- no-sorry (actual supply: exponent agreement -> tail-product equality target)
#print axioms DkMath.FLT.cyclotomicTailLinearFactorMulEqSpanPow_of_exponentAgreement -- OK: no sorry
-- no-sorry (actual supply: exponent agreement -> local exponent nonzero)
#print axioms DkMath.FLT.cyclotomicLocalExponentNonzero_of_exponentAgreement -- OK: no sorry
-- no-sorry (actual supply: CharZero -> x-span nonzero)
#print axioms DkMath.FLT.cyclotomicXSpanNonzero_of_counterexamplePack_of_charZero -- OK: no sorry
-- no-sorry (generic receiver: pairwise unit-difference family -> product-erase coprimality)
#print axioms DkMath.FLT.linearFactorIdealIsCoprimeProdEraseOfPairwiseMulSubIsUnit -- OK: no sorry
-- no-sorry (associated -> span equality)
#print axioms DkMath.FLT.associated_span_eq -- OK: no sorry
-- no-sorry (linear factor diff span = (ζ-1)*y span via Mathlib associated lemma)
#print axioms DkMath.FLT.linearFactorDiffSpanEqSubOneSpan -- OK: no sorry
-- no-sorry (common prime contains (ζ-1)*y)
#print axioms DkMath.FLT.commonPrimeContainsSubOneY -- OK: no sorry
-- no-sorry (common prime divides (ζ-1) or y)
#print axioms DkMath.FLT.commonPrimeDvdsSubOneOrY -- OK: no sorry
-- no-sorry (Mathlib adapter: hζ.toInteger - 1 ∈ P -> P | (p))
#print axioms DkMath.FLT.subOneDividesPrimeP_of_toInteger_sub_one_dvd_prime' -- OK: no sorry
-- no-sorry (ring-of-integers specialization of the common-prime disjunction)
#print axioms DkMath.FLT.commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic -- OK: no sorry
-- no-sorry (generic receiver: no common prime -> coprimality)
#print axioms DkMath.FLT.linearFactorIdeals_isCoprime_of_noCommonPrime -- OK: no sorry
-- no-sorry (ring-of-integers specialization: prime-or-y contradiction -> chosen/other pairwise coprimality)
#print axioms DkMath.FLT.chosenLinearFactor_isCoprime_with_other_of_primeOrYContradiction_of_ringOfIntegersCyclotomic -- OK: no sorry
-- no-sorry (first-case chosen factor is coprime to the full complementary tail)
#print axioms DkMath.FLT.chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack -- OK: no sorry
-- no-sorry (chosen-first 2-factor equality adapter)
#print axioms DkMath.FLT.linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime -- OK: no sorry
-- no-sorry (pack product identity -> chosen/tail ideal equation)
#print axioms DkMath.FLT.chosenLinearFactorMulTailEqSpanPow_of_productEq -- OK: no sorry
-- no-sorry (pack -> x-span nonzero in ring of integers)
#print axioms DkMath.FLT.xSpanNonzero_of_counterexamplePack_of_ringOfIntegers -- OK: no sorry
-- no-sorry (first-case pack -> chosen factor ideal explicit p-th power equality)
#print axioms DkMath.FLT.chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin -- OK: no sorry
-- no-sorry (first-case pack -> Stage 1 existence boundary)
#print axioms DkMath.FLT.cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin -- OK: no sorry
-- no-sorry (actual witness -> tail/factor coprimality target)
#print axioms DkMath.FLT.cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness -- OK: no sorry
-- no-sorry (pack-specialized Stage 2 receiver with explicit ideal equality)
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_spanEqPowPrincipal -- OK: no sorry
-- no-sorry (existential Stage 1 boundary → element-level Stage 2 normalization)
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower -- OK: no sorry
-- no-sorry (explicit Stage 1 output pieces -> concrete Stage 2 target)
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_linearFactorSpanEqPow -- OK: no sorry
-- no-sorry (2-factor route -> existential Stage 1 boundary target)
#print axioms DkMath.FLT.cyclotomicLinearFactorIdealPthPower_of_tailFactorCoprimeRoute -- OK: no sorry
-- no-sorry (2-factor route -> concrete Stage 2 target)
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_tailFactorCoprimeRoute -- OK: no sorry
-- no-sorry (exponent agreement + pairwise witness -> concrete Stage 2 target)
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_exponentAgreementAndPairwiseUnitWitness -- OK: no sorry
-- no-sorry (exponent agreement + pairwise witness -> existential Stage 1 boundary target)
#print axioms DkMath.FLT.cyclotomicLinearFactorIdealPthPower_of_exponentAgreementAndPairwiseUnitWitness -- OK: no sorry
-- no-sorry (refined Stage 1 composition)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_refinedStage1Route -- OK: no sorry if stage assumptions are clean
-- `sorry` (legacy one-shot wrapper)
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree -- uses sorry
-- no-sorry (current target is still placeholder)
#print axioms DkMath.FLT.cyclotomicIdealPthPower_of_classGroupPTorsionFree -- OK: no sorry

-- §4. ClassGroupBridge
-- no-sorry (trivial)
#print axioms DkMath.FLT.classGroupPTorsionFree_of_regularPrime -- OK: no sorry
-- no-sorry (preferred refined regular-prime mainline to gap-divisible branch)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute -- OK: no sorry
-- `sorry` (still blocked by full principalization stage)
#print axioms DkMath.FLT.qAdicGapReductionGapDivisible_of_regularPrime -- uses sorry

-- §5. RegularPrimeRoute
-- no-sorry (pure composition)
#print axioms DkMath.FLT.qAdicGapReductionPure_of_threeWaySplit -- OK: no sorry
-- no-sorry (refined Stage 1 route)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedStage1Route -- OK: no sorry if stage assumptions are clean
-- no-sorry (refined ideal / unit / norm route)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedKummerRoute -- OK: no sorry if stage assumptions are clean
-- no-sorry (refined class-group route still depends only on explicit Stage 2 / Stage 3 assumptions)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedClassGroupRoute -- OK: no sorry if stage assumptions are clean
-- no-sorry (preferred refined regular-prime public mainline)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute -- OK: no sorry if stage assumptions are clean
-- no-sorry (chain through class-group principalization)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerThreeWaySplit -- OK: no sorry
-- `sorry` (chain through cyclotomicPrincipalization)
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute -- uses sorry
