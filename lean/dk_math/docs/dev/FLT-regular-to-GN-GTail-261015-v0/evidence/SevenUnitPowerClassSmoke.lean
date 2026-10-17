import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.SevenUnitPowerClassSmoke"

open DkMath.Lib.Algebra DkMath.FLT.Kummer.SevenPrimaryNorm

#check exists_root_and_unit_correction
#check quotient_eq_of_fixed_extraction
#check exists_unit_pow_of_fixed_extraction
#check currentCarrier_unit_class_of_GN_source
#check unit_seventh_after_twist_of_GN_source
#check GNRamifierTwist_two_not_seventh

example : ((-1 : ℤˣ) : ℤˣ ⧸ unitPowerSubgroup ℤ 7) = (1 : ℤˣ ⧸ unitPowerSubgroup ℤ 7) :=
  sameUnitPowerClass_iff_quotient_eq.mp ⟨-1, by decide⟩
