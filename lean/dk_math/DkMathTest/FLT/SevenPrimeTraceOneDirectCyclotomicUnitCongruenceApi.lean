import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicUnitCongruence

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicUnitCongruenceApi"

namespace DkMath.FLT.Seven

open SevenCyclotomicDegreeSixInt
open SevenRealCubicInt

#check sevenIdeal
#check DirectCyclotomicChosenQuotientPowerPacket
#check DegreeSixUnitCongruentToRationalModSeven
#check DegreeSixKummerUnitLemmaAtSeven
#check degreeSix_pow_seven_scalarized_mod_seven
#check directRamifiedGapTail_mem_sevenIdeal
#check directCyclotomicChosenQuotient_sub_endpointRight_mem_sevenIdeal
#check exists_directCyclotomicChosenQuotientPowerPacket
#check DirectCyclotomicChosenQuotientPowerPacket.quotient_eq
#check DirectCyclotomicChosenQuotientPowerPacket.directLinearFactor_eq
#check DirectCyclotomicChosenQuotientPowerPacket.beta_not_mem_ramifiedPrime
#check DirectCyclotomicChosenQuotientPowerPacket.unit_congruentToRationalModSeven
#check directChosenQuotientRealSource
#check directCyclotomicChosenQuotient_quadraticNorm
#check directChosenQuotientNormUnit
#check DirectCyclotomicChosenQuotientPowerPacket.realSource_eq_normUnit_mul_normBeta_pow
#check DirectCyclotomicChosenQuotientPowerPacket.realUnit_projectiveLog_eq_zero
#check DirectCyclotomicChosenQuotientPowerPacket.exists_realNormUnit_seventhPower

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ p : DirectCyclotomicChosenQuotientPowerPacket source r,
      directCyclotomicPhaseQuotient r 1 = p.unit * p.beta ^ 7 := by
  obtain ⟨p⟩ := exists_directCyclotomicChosenQuotientPowerPacket r
  exact ⟨p, p.quotient_eq⟩

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ n : ℤ,
      (directCyclotomicPhaseQuotient r 1) ^ 7 - (n : Ring) ∈ sevenIdeal := by
  obtain ⟨n, hn⟩ := degreeSix_pow_seven_scalarized_mod_seven
    (directCyclotomicPhaseQuotient r 1)
  exact ⟨n, hn⟩

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicPhaseQuotient r 1 -
        ofReal (r.summit.endpointRight : SevenRealCubicInt) ∈ sevenIdeal :=
  directCyclotomicChosenQuotient_sub_endpointRight_mem_sevenIdeal r

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    DegreeSixUnitCongruentToRationalModSeven p.unit :=
  p.unit_congruentToRationalModSeven

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectCyclotomicChosenQuotientPowerPacket source r) :
    ∃ v : SevenRealCubicIntˣ,
      directChosenQuotientNormUnit p = v ^ 7 :=
  p.exists_realNormUnit_seventhPower

end DkMath.FLT.Seven
