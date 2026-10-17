import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.SevenGNSourceSmoke"

open DkMath.Lib.Cosmic DkMath.FLT.Kummer.SevenPrimaryNorm

#check map_phaseSource_pow
#check rotate_realGNSource
#check currentLinearCarrier_eq_realGNSource
#check current_real_GN_eq_orbitQuotient
#check exists_integer_GN_source_iff
#check currentLinearCarrier_ne_integer_GN_same_phase

example (x u ξ : ℤ) : phaseSource ξ (x - u) u = x - ξ * u :=
  phaseSource_sub_coordinates ξ x u
