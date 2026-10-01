import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseApi"

namespace DkMath.FLT.Seven

open SevenCyclotomicDegreeSixInt

#check SevenCyclotomicDegreeSixInt.starUnit
#check SevenCyclotomicDegreeSixInt.quadraticNormUnit
#check SevenCyclotomicDegreeSixInt.quadraticNormUnit_star
#check directRelativeNormOnePhase
#check DirectRelativeNormOnePhasePacket
#check directRelativeNormOnePhase_norm_one
#check directRelativeNormOnePhase_sub_one_mem_sevenIdeal
#check RelativeNormOneScalarUnitAtSeven
#check exists_directRelativeNormOnePhasePacket
#check directRelativeNormOnePhase_eq_one_of_target
#check DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_of_phase_target
#check DirectCyclotomicChosenQuotientPowerPacket.exists_quotient_seventhPower_of_phase_target
#check DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_of_phase_target

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    Nonempty (DirectRelativeNormOnePhasePacket source r p) :=
  exists_directRelativeNormOnePhasePacket p

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    SevenCyclotomicDegreeSixInt.quadraticNormUnit
        (directRelativeNormOnePhase p) = 1 :=
  directRelativeNormOnePhase_norm_one p

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ((directRelativeNormOnePhase p : SevenCyclotomicDegreeSixInt.Ring) - 1) ∈
      sevenIdeal :=
  directRelativeNormOnePhase_sub_one_mem_sevenIdeal p

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r)
    (htarget : RelativeNormOneScalarUnitAtSeven) :
    ∃ gamma : SevenCyclotomicDegreeSixInt.Ring,
      directCyclotomicPhaseQuotient r 1 = gamma ^ 7 :=
  p.exists_quotient_seventhPower_of_phase_target htarget

end DkMath.FLT.Seven
