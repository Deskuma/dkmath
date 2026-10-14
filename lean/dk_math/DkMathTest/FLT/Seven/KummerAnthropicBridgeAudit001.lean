/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeRoute
import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer
import DkMath.FLT.Seven.PrimeTraceOneCyclotomicPidBypassAudit
import DkMath.Lib.NumberTheory.UnitPowerSector
import Lean.Util.FoldConsts

#print "file: DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit001"


#check DkMath.FLT.descentExistence_exists_iff_gnReduction_exists
#print axioms DkMath.FLT.descentExistence_exists_iff_gnReduction_exists
#check DkMath.FLT.PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget
#print axioms DkMath.FLT.PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget
#check DkMath.FLT.CyclotomicClassGroupPTorsionFreeTarget
#print axioms DkMath.FLT.CyclotomicClassGroupPTorsionFreeTarget
#check DkMath.FLT.CyclotomicIdealPthPowerTarget
#print axioms DkMath.FLT.CyclotomicIdealPthPowerTarget
#check DkMath.FLT.CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescentTarget
#print axioms DkMath.FLT.CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescentTarget
#check DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree
#check DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#check DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
#check DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute
#check DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit
#check DkMath.FLT.chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_withoutProduct
#print axioms DkMath.FLT.chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_withoutProduct
#check DkMath.FLT.cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct
#print axioms DkMath.FLT.cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct
#check DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_hzEq
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_hzEq
#check DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
#print axioms DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
#check DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing
#print axioms DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing
#check DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_coprime_card
#print axioms DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_coprime_card
#check DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
#print axioms DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow
#check DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
#print axioms DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
#check DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#print axioms DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check DkMath.Lib.NumberTheory.exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#print axioms DkMath.Lib.NumberTheory.exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check DkMath.Lib.NumberTheory.UnitPowerSectorSystem
#print axioms DkMath.Lib.NumberTheory.UnitPowerSectorSystem
#check DkMath.Lib.NumberTheory.exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#print axioms DkMath.Lib.NumberTheory.exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
#check DkMath.FLT.Seven.CounterexamplePack
#print axioms DkMath.FLT.Seven.CounterexamplePack
#check DkMath.FLT.Seven.nonempty_primitiveCounterexampleRamifiedProvenance
#print axioms DkMath.FLT.Seven.nonempty_primitiveCounterexampleRamifiedProvenance
#check DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing
#print axioms DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing
#check DkMath.FLT.Seven.CyclotomicSeven.classNumber_eq_one
#print axioms DkMath.FLT.Seven.CyclotomicSeven.classNumber_eq_one
#check DkMath.FLT.Seven.CyclotomicSeven.classGroupPTorsionFreeAt_ringOfIntegers_seven
#print axioms DkMath.FLT.Seven.CyclotomicSeven.classGroupPTorsionFreeAt_ringOfIntegers_seven
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_injective
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_injective
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringIsPrincipalIdealRing
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringIsPrincipalIdealRing
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.classGroupPTorsionFreeAt_seven
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.classGroupPTorsionFreeAt_seven
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow
#check DkMath.FLT.Seven.sevenIdeal
#print axioms DkMath.FLT.Seven.sevenIdeal
#check DkMath.FLT.Seven.DegreeSixUnitCongruentToRationalModSeven
#print axioms DkMath.FLT.Seven.DegreeSixUnitCongruentToRationalModSeven
#check DkMath.FLT.Seven.DegreeSixKummerUnitLemmaAtSeven
#print axioms DkMath.FLT.Seven.DegreeSixKummerUnitLemmaAtSeven
#check DkMath.FLT.Seven.directCyclotomicPhaseQuotient_one_isCoprime_with_tail
#print axioms DkMath.FLT.Seven.directCyclotomicPhaseQuotient_one_isCoprime_with_tail
#check DkMath.FLT.Seven.directCyclotomicChosenQuotient_ideal_is_seventh_power
#print axioms DkMath.FLT.Seven.directCyclotomicChosenQuotient_ideal_is_seventh_power
#check DkMath.FLT.Seven.directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power
#print axioms DkMath.FLT.Seven.directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power
#check DkMath.FLT.Seven.exists_directCyclotomicChosenQuotientPowerPacket
#print axioms DkMath.FLT.Seven.exists_directCyclotomicChosenQuotientPowerPacket
#check DkMath.FLT.Seven.DirectCyclotomicChosenQuotientPowerPacket.unit_congruentToRationalModSeven
#print axioms DkMath.FLT.Seven.DirectCyclotomicChosenQuotientPowerPacket.unit_congruentToRationalModSeven
#check DkMath.FLT.Seven.DirectCyclotomicChosenQuotientPowerPacket.exists_realNormUnit_seventhPower
#print axioms DkMath.FLT.Seven.DirectCyclotomicChosenQuotientPowerPacket.exists_realNormUnit_seventhPower
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.relativeNormOneScalarUnitAtSeven_unconditional
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.relativeNormOneScalarUnitAtSeven_unconditional
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_unconditional
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_unconditional
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional
#print axioms DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional
#check DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
#print axioms DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
#check DkMath.FLT.Seven.SevenRealCubic.directOrbitCommonPrime_kummer_residue_condition
#print axioms DkMath.FLT.Seven.SevenRealCubic.directOrbitCommonPrime_kummer_residue_condition
#check DkMath.FLT.Seven.SevenRealCubic.directOrbitCommonPrime_kummer_beta_form
#print axioms DkMath.FLT.Seven.SevenRealCubic.directOrbitCommonPrime_kummer_beta_form

namespace DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit001

open DkMath.FLT.Seven
open SevenCyclotomicDegreeSixInt
open scoped NumberField

-- Audit the definitions rather than their informal descriptions.
example : DkMath.FLT.CyclotomicIdealPthPowerTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

example (h : DkMath.FLT.CyclotomicClassGroupPTorsionFreeTarget.{0})
    (R : Type) [CommRing R] [IsDomain R] : Subsingleton (ClassGroup R) := by
  constructor
  intro a b
  have ha : a = 1 := h 0 a (by simp)
  have hb : b = 1 := h 0 b (by simp)
  exact ha.trans hb.symm

-- Check candidate contracts as types only; these are not proof declarations.
#check (∀ u : Ringˣ, DegreeSixUnitCongruentToRationalModSeven (u : Ring) →
  u = starUnit u)
#check (∀ u : Ringˣ, DegreeSixUnitCongruentToRationalModSeven (u : Ring) →
  ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7)
#check (∀ u : Ringˣ, DegreeSixUnitCongruentToRationalModSeven (u : Ring) →
  ∃ v : Ringˣ, u = v ^ 7)

end DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit001


open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let roots := #[
    ``DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute,
    ``DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit,
    ``DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute,
    ``DkMath.FLT.Seven.nonempty_primitiveCounterexampleRamifiedProvenance,
    ``DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional]
  for root in roots do
    let mut pending : Array Name := #[root]
    let mut visited : NameSet := {}
    let mut sorryCallers : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut unreadable : Array Name := #[]
    let mut finished : Array Name := #[]
    let mut axioms : Array Name := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      if visited.contains n then continue
      visited := visited.insert n
      let label := n.toString
      if label.contains "fermatLastTheoremSeven" ||
          label.contains "P2MW.S_flt_regular" || label == "flt_regular" then
        finished := finished.push n
      match env.checked.get.find? n with
      | none => missing := missing.push n
      | some info =>
        if let .axiomInfo _ := info then axioms := axioms.push n
        pending := pending ++ info.type.getUsedConstants
        if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
        match info.value? (allowOpaque := true) with
        | some value =>
          let deps := value.getUsedConstants
          if deps.contains ``sorryAx then sorryCallers := sorryCallers.push n
          pending := pending ++ deps
        | none =>
          match info with
          | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => unreadable := unreadable.push n
          | _ => pure ()
    logInfo m!"AUDIT_ROOT {root}; constants={visited.size}"
    logInfo m!"SORRY_CALLERS {sorryCallers}"
    logInfo m!"AXIOMS {axioms}; FINISHED_FLT7_OR_REGULAR {finished}"
    logInfo m!"MISSING {missing}; UNREADABLE {unreadable}"
    unless missing.isEmpty && unreadable.isEmpty && finished.isEmpty do
      throwError "Incomplete dependency audit or completed theorem dependency"
