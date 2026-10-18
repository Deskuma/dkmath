import DkMath

#print "file: RootSmokeNOTE005"

open DkMath.Lib.NumberTheory DkMath.FLT.Frey

example {p : ℕ} (hp : Odd p) (a b : ℚ) :
    (FreyGapCubic.normalized (a ^ p) (b ^ p)).Δ =
      (a * b) ^ (2 * p) * ((a + b) * GNFreyDiscriminant.gnFactor p a b) ^ 2 / 256 :=
  GNFreyDiscriminant.normalized_discriminant_gn hp a b

example {p : ℕ} (S : Source p) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

example {p ℓ : ℕ} [Fact ℓ.Prime] (hp : 0 < p) (hℓ2 : ℓ ≠ 2)
    (S : Source p) (hd : (ℓ : ℤ) ∣ S.a * S.b * S.c) :
    p ∣ padicValInt ℓ S.curve.Δ := (S.local_arithmetic hp hℓ2 hd).2.2.2

example : FermatLastTheoremFor 11 := DkMath.FLT.Kummer.fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := DkMath.FLT.Kummer.fermatLastTheoremFor_thirteen

#check DkMath.FLT.Kummer.IrregularPrime37.observe_galois
#print axioms FreyGapCubic.normalized_discriminant
#print axioms GNFreyDiscriminant.integral_discriminant_gn
#print axioms FreyPrimeValuation.integral_valuation_of_solution
#print axioms Source.local_arithmetic
#print axioms Source.reduction_isElliptic
