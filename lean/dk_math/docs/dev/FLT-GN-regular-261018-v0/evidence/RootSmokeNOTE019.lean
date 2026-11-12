import DkMath

#print "file: RootSmokeNOTE019"

/-! NOTE-019: 全指数の位数、実際の短完全列、同じFrey曲線への接続をルートから検査する。 -/
#check DkMath.Lib.Algebra.TorsionMultiplication.short_exact
#check DkMath.Lib.Algebra.TorsionMultiplication.kernelEquiv
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsion_short_exact
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.torsionMultiply_equivariant
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq
#check DkMath.FLT.Frey.Source.curve_torsion_card_finite_level
#print axioms DkMath.Lib.Algebra.TorsionMultiplication.card_mul
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.card_torsion_sq
#print axioms DkMath.FLT.Frey.Source.curve_torsion_card_sq

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

example (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion E n) = n ^ 2 := card_torsion_sq E n hn

example (E : WeierstrassCurve ℚ) [E.IsElliptic] : Nat.card (Torsion E 36) = 1296 :=
  card_torsion_sq E 36 (by decide)

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nat.card (Torsion E (37 ^ 2)) = 1874161 := card_torsion_pow E 37 2 (by decide)

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (torsionInclusion E 6 6) ∧
      Function.Exact (torsionInclusion E 6 6) (torsionMultiply E 6 6) ∧
      Function.Surjective (torsionMultiply E 6 6) := torsion_short_exact E 6 6 (by decide)

example (S : DkMath.FLT.Frey.Source 37) (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve n) = n ^ 2 ∧ FactorsThroughFiniteLevel S.rationalCurve n :=
  S.curve_torsion_card_finite_level n hn
