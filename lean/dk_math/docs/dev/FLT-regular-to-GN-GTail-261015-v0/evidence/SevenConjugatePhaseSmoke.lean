import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.SevenConjugatePhaseSmoke"

open scoped NumberField
open DkMath.FLT.Kummer DkMath.FLT.Kummer.SevenPrimaryNorm

example : KummerUnitPowerCriterion (𝓞 (CyclotomicField 7 ℚ)) 7 :=
  septic_kummer_unit_power_criterion

#check integralConj_eq_CM
#check unit_square_eq_norm_mul_ratio
#check GN_primary_unit_seventh
#check exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh
#check DkMath.Lib.Algebra.oddPower_root_of_square
