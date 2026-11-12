import DkMath

#print "file: RootSmokeNOTE006Section4"

/-! NOTE-006 §4: ルート公開入口と主要定理の kernel 公理監査。 -/

#check DkMath.Lib.NumberTheory.RamifiedPhasePacket.exists_phaseMul_one
#check DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.orbitNorm_fixed
#check DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.zero_mul_orbitNorm
#check DkMath.FLT.Frey.Source.good_or_multiplicative
#print axioms DkMath.FLT.Kummer.IrregularPrime37.observe_orbit_norm
#print axioms DkMath.Lib.NumberTheory.FreyLocalReduction.isMinimal_of_isUnit_c4
#print axioms DkMath.FLT.Frey.Source.hasMultiplicativeReduction
#print axioms DkMath.FLT.Frey.Source.hasGoodReduction
#print axioms DkMath.FLT.Frey.Source.minimal_discriminant_exponent_dvd
