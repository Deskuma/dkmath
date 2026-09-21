import DkMath.FLT.Seven.PrimeTraceOneCyclotomicPidBypassAudit

#print "file: DkMathTest.FLT.SevenPrimeTraceOneCyclotomicPidBypassAuditApi"

namespace DkMath.FLT.Seven

open DkMath.Lib.NumberTheory
open NumberField
open scoped NumberField

#check CyclotomicSeven.classGroupPTorsionFreeAt_ringOfIntegers_seven
#check SevenCyclotomicDegreeSixInt.classGroupPTorsionFreeAt_seven
#check SevenCyclotomicDegreeSixInt.UnitSeventhPowerSurjective
#check SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow_audit
#check RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.directPid_orientedElementLevelPower_audit

example :
    classGroupPTorsionFreeAt SevenCyclotomicDegreeSixInt.Ring 7 := by
  exact SevenCyclotomicDegreeSixInt.classGroupPTorsionFreeAt_seven

example {I : Ideal SevenCyclotomicDegreeSixInt.Ring}
    {a : SevenCyclotomicDegreeSixInt.Ring} {n : ℕ}
    (h : Ideal.span {a} = I ^ n) :
    ∃ u : SevenCyclotomicDegreeSixInt.Ring, IsUnit u ∧
      a = u * Submodule.IsPrincipal.generator I ^ n := by
  exact SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow_audit h

end DkMath.FLT.Seven
