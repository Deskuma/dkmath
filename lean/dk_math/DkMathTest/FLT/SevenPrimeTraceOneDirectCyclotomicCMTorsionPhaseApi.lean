import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMTorsionPhaseApi"

namespace DkMath.FLT.Seven

open SevenCyclotomicDegreeSixInt

#check SevenCyclotomicDegreeSixInt.starAlgHom
#check SevenCyclotomicDegreeSixInt.abstractZeta_complexConj
#check SevenCyclotomicDegreeSixInt.cyclotomicIntegralGenerator_complexConj
#check SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_complexConj_coherence
#check SevenCyclotomicDegreeSixInt.cyclotomicTorsionOrder_eq
#check SevenCyclotomicDegreeSixInt.ringOfIntegersUnitsEquiv
#check SevenCyclotomicDegreeSixInt.unitsComplexConj_coherence
#check SevenCyclotomicDegreeSixInt.concrete_norm_one_pow_twentyEight
#check SevenCyclotomicDegreeSixInt.concrete_phase_pow_fourteen
#check SevenCyclotomicDegreeSixInt.unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
#check relativeNormOneScalarUnitAtSeven_unconditional
#check DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional
#check DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_unconditional
#check DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional

example (delta : SevenCyclotomicDegreeSixInt.Ringˣ)
    (hpow : delta ^ 28 = 1)
    (hcong : ((delta : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈ sevenIdeal) :
    delta = 1 :=
  SevenCyclotomicDegreeSixInt.unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
    delta hpow hcong

end DkMath.FLT.Seven
