import DkMath

#print "file: RootSmokeNOTE031PrimeFiltration"

/-!
# NOTE-031-004 第2部: 通常入口からの全ケース局所終点

同じSource上の良還元・乗法的還元の吸収、全てのp上の場所で同側となる終点、
実際の還元準同型と節点p-torsionの橋を公開入口から参照する。
031-005の全素数での合流と大域化はこのスモークの対象に含まない。
-/
#check DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentSubgroup
#check DkMath.Lib.NumberTheory.EllipticSmoothReduction.zeroComponentReduction
#check DkMath.Lib.NumberTheory.EllipticSmoothReduction.nsmul_reduce_eq_zero
#check DkMath.Lib.NumberTheory.EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model
#check DkMath.Lib.NumberTheory.EllipticNodalInertia.inertia_difference_smooth
#check DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_bad_prime
#check DkMath.FLT.Frey.Source.residualReductionKernel_absorbs_at_p
#check DkMath.FLT.Frey.Source.residual_fixed_or_cofixed_at_p
#check DkMath.FLT.Frey.Source.residual_common_side_at_p
#print axioms DkMath.FLT.Frey.Source.residual_common_side_at_p
