import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicChosenTail

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicChosenTailApi"

namespace DkMath.FLT.Seven

open SevenCyclotomicDegreeSixInt

#check directCyclotomicPhaseFactor
#check directCyclotomicPhaseSum
#check directCyclotomicPhaseQuotient
#check directCyclotomicPhaseQuotient_one
#check directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient
#check ramifiedEval_directCyclotomicPhaseQuotient
#check directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
#check directCyclotomicPhaseFactor_not_mem_ramifiedPrime_sq_of_lt_seven
#check prime_eq_ramified_of_mem_chosen_and_other_phase
#check directCyclotomicPhaseQuotients_one_isCoprime_with
#check directCyclotomicTail
#check directCyclotomicPhaseQuotient_one_isCoprime_with_tail
#check directCyclotomicOtherPhaseProduct_eq_uniformizer_pow_mul_tail
#check directCyclotomicSixPhaseProduct
#check directCyclotomicSixPhaseProduct_eq_uniformizer_pow_mul_quotients
#check sixPhaseProduct_directLinearFactor_eq_directCyclotomicSixPhaseProduct
#check directCyclotomicQuotientProduct_eq_unit_mul_residual_pow
#check directCyclotomicQuotientIdealProduct_eq_residual_pow
#check directCyclotomicChosenQuotient_ideal_is_seventh_power
#check directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicPhaseQuotient r 1 = directRamifiedQuotient r := by
  exact directCyclotomicPhaseQuotient_one r

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {P : Ideal SevenCyclotomicDegreeSixInt.Ring} (hP : P.IsPrime)
    (h1 : directCyclotomicPhaseFactor r 1 ∈ P)
    (h2 : directCyclotomicPhaseFactor r 2 ∈ P) :
    P = ramifiedPrime := by
  exact prime_eq_ramified_of_mem_chosen_and_other_phase r hP
    (by norm_num) (by norm_num) h1 h2

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    IsCoprime
      (Ideal.span ({directCyclotomicPhaseQuotient r 1} :
        Set SevenCyclotomicDegreeSixInt.Ring))
      (Ideal.span ({directCyclotomicTail r} :
        Set SevenCyclotomicDegreeSixInt.Ring)) := by
  exact directCyclotomicPhaseQuotient_one_isCoprime_with_tail r

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    Ideal.span ({directCyclotomicPhaseQuotient r 1} :
        Set SevenCyclotomicDegreeSixInt.Ring) *
      Ideal.span ({directCyclotomicTail r} :
        Set SevenCyclotomicDegreeSixInt.Ring) =
    Ideal.span ({ofReal (r.summit.residualRoot : SevenRealCubicInt)} :
      Set SevenCyclotomicDegreeSixInt.Ring) ^ 7 := by
  exact directCyclotomicQuotientIdealProduct_eq_residual_pow r

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ I : Ideal SevenCyclotomicDegreeSixInt.Ring,
      Ideal.span ({directLinearFactor r} :
        Set SevenCyclotomicDegreeSixInt.Ring) =
        ramifiedPrime * I ^ 7 := by
  exact directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power r

end DkMath.FLT.Seven
