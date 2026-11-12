import DkMath

#print "file: RootSmokeNOTE031DoublingDepth"

/-! NOTE-031-002C6a: 通常ルートから同じ中心の臨界深さ・実際の倍点へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_depth
#check DkMath.Lib.NumberTheory.EllipticCriticalDepth.two_torsion_separation
#check DkMath.Lib.NumberTheory.EllipticCriticalDepth.shallow_denominator_valuation
#check DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_identity
#check DkMath.Lib.NumberTheory.EllipticDoublingDepth.doubling_depth
#check @DkMath.FLT.Frey.Source.two_torsion_critical_depth 37
#check @DkMath.FLT.Frey.Source.shallow_doubling_depth 37
#print axioms DkMath.FLT.Frey.Source.two_torsion_critical_depth
#print axioms DkMath.FLT.Frey.Source.shallow_doubling_depth
