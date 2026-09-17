import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCaseAudit

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicSecondCaseAuditApi"

namespace DkMath.FLT.Seven

#check directLinearFactor
#check directRelativeNorm
#check directCyclotomicNorm
#check PrimitiveCounterexampleDirectCyclotomicSecondCasePacket.ofProvenance
#check directLinearFactor_mul_star
#check directCyclotomicNorm_eq_cyclotomicSeven
#check directLinearFactor_norm_product_identity
#check directLinearFactor_norm_product_eq_distinguished_pow
#check directCyclotomicNorm_eq_seven_mul_residual_pow

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (PrimitiveCounterexampleDirectCyclotomicSecondCasePacket.ofProvenance r).linearFactor =
      directLinearFactor r := by
  rfl

example {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicNorm r.summit.endpointLeft r.summit.endpointRight =
      7 * (r.summit.residualRoot : ℤ) ^ 7 := by
  exact directCyclotomicNorm_eq_seven_mul_residual_pow r

end DkMath.FLT.Seven
