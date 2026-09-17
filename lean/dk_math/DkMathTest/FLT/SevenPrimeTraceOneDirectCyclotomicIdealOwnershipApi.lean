import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicIdealOwnership

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicIdealOwnershipApi"

namespace DkMath.FLT.Seven

open SevenCyclotomicDegreeSixInt

#check directRamifiedGapTail
#check directRamifiedQuotient
#check directGap_eq_uniformizer_pow
#check directLinearFactor_eq_uniformizer_mul_quotient
#check ramifiedEval_directRamifiedQuotient
#check directLinearFactor_mem_ramifiedPrime
#check directLinearFactor_not_mem_ramifiedPrime_sq
#check cyclotomicNormHom_directLinearFactor
#check sixPhaseProduct_directLinearFactor

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directLinearFactor r ∈ ramifiedPrime ∧
      directLinearFactor r ∉ ramifiedPrime ^ 2 := by
  exact ⟨directLinearFactor_mem_ramifiedPrime r,
    directLinearFactor_not_mem_ramifiedPrime_sq r⟩

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    sixPhaseProduct (directLinearFactor r) =
      (7 * (r.summit.residualRoot : ℤ) ^ 7 :
        SevenCyclotomicDegreeSixInt.Ring) := by
  exact sixPhaseProduct_directLinearFactor r

end DkMath.FLT.Seven
