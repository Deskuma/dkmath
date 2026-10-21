import DkMath

#print "file: RootSmokeNOTE029"

/-! NOTE-029: 通常ルートから安定部分群・固定点の降下・整数軌道の核へ到達する。 -/
#check DkMath.FLT.Frey.Source.residual_exists_stable_pointSubgroup
#check DkMath.FLT.Frey.Source.residual_exists_cofixed_line
#check DkMath.FLT.Frey.Source.residual_stable_line_diagonal_product
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion
#check DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit

#print axioms DkMath.FLT.Frey.Source.residual_exists_stable_pointSubgroup
#print axioms DkMath.FLT.Frey.Source.residual_exists_cofixed_line
#print axioms DkMath.Lib.NumberTheory.FoldedValuationOrbit.no_prime_shifted_valuation_orbit

example (v m : ℤ) (h : 2 * (37 * v - 4) ∣ 37 * m) : 2 * (37 * v - 4) ∣ m :=
  DkMath.Lib.NumberTheory.FoldedValuationOrbit.cancel_prime_modulus
    37 (by decide) (by decide) v m h
