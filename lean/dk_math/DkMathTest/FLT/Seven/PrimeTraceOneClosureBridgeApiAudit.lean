import DkMath.FLT.Seven.PrimeTraceOneClosureBridge

open DkMath.FLT.Prime
open DkMath.FLT.Seven
open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

example (u v : ℤ) :
    (traceOnePowCoords (-2) u v 7).1 = seventhPowerFst u v :=
  traceOnePowCoords_negTwo_seven_fst u v

example (u v : ℤ) :
    (traceOnePowCoords (-2) u v 7).2 = seventhPowerSnd u v :=
  traceOnePowCoords_negTwo_seven_snd u v

#check not_seven_dvd_natAbs_norm_of_primeTraceOne_residual_axis_terminal
#check not_seven_dvd_norm_of_primeTraceOne_residual_axis_terminal
#check exists_seventhPowerCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
#check exists_seventhPowerRoot_not_seven_dvd_norm_of_primeTraceOnePacket
#check exists_seventhPowerCoords_and_root_not_seven_dvd_norm_of_primeTraceOnePacket
#check exists_seventhPowerCoords_residual_snd_dvd_seven_of_primeTraceOnePacket
#check exists_seventhPowerCoords_residual_sndCore_not_dvd_seven_of_primeTraceOnePacket
#check exists_seventhPowerCoords_residual_snd_fortyNine_iff_dvd_seven_of_primeTraceOnePacket
