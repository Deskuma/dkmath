import DkMath.FLT.Kummer.SevenCurrentCorrectionPower

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.scratch.RouteProbe"

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt

#check ramifiedEval_uniformizer
#check uniformizer_six_dvd_seven
#check FiniteMultiplicity.of_not_isUnit
#check FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd

#synth WfDvdMonoid C

#print axioms seven_dvd_some_endpoint_of_counterexample
#print axioms nonempty_primitiveCounterexampleRamifiedProvenance
#print axioms currentCorrectionPowerPacket

#check SevenRealCubicInt.thetaResidue

#print axioms DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing
#print axioms concrete_kummer_unit_power_criterion
#print axioms integralEquiv

#check_failure FltRegular.CaseII.exists_solution'
