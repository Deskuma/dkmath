import DkMath

#print "file: docs.dev.FLT-regular-to-GN-GTail-261015-v0.evidence.SevenPrimaryNormSmoke"

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm

example (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (h : ∃ n : ℤ, (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ (u : _) - (n : _)) :
    ∃ v : SevenRealCubicIntˣ, Units.map relativeNorm u = v ^ 7 :=
  relativeNorm_primary_unit_seventh u h

#check GN_primary_unit_relativeNorm_seventh
#check integralEquiv_generator
