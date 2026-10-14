import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase

#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv_apply
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv_injective
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv_surjective
#check DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.quadraticNormUnit
#check DkMath.FLT.Seven.directRelativeNormOnePhase_norm_one
#check DkMath.FLT.Seven.directRelativeNormOnePhase_sub_one_mem_sevenIdeal
#check DkMath.FLT.Seven.RelativeNormOneScalarUnitAtSeven

example :
    Function.Bijective
      DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing :=
  ⟨DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_injective,
    DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_surjective⟩
