/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoSmallGoodPrime

#print "file: DkMathTest.FLT.FreyHnoSmallGoodPrime"

namespace DkMathTest.FLT.FreyHnoSmallGoodPrime

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.ValuationInertia
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-! The general small-good-prime obstruction is directly reusable. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q < p)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L :=
  S.residual_hno_of_small_good_prime hp5 hbe hq2 hqp hd

/-! The contrapositive support statement exposes the arithmetic footprint of
    any surviving Cofixed line. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    {L : Submodule (ZMod p) S.ResidualSpace}
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q < p →
      (q : ℤ) ∣ S.a * S.b * S.c :=
  S.residual_cofixed_forces_small_prime_support hp5 hbe hline hstable hcofixed

/-! The dyadic branch and the odd-prime branch share one pointwise support API. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    {L : Submodule (ZMod p) S.ResidualSpace}
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∀ q : ℕ, Nat.Prime q → q < p →
      (q : ℤ) ∣ S.a * S.b * S.c :=
  S.residual_cofixed_forces_prime_support hp5 hbe hline hstable hcofixed

/-! The finite product packages the same support condition without a hidden
    primorial or positivity assumption. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    {L : Submodule (ZMod p) S.ResidualSpace}
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ((Finset.range p).filter (fun q => q.Prime ∧ q ≠ 2)).prod
        (fun q => (q : ℤ)) ∣ S.a * S.b * S.c :=
  S.residual_cofixed_forces_odd_prime_product_support
    hp5 hbe hline hstable hcofixed

/-! The same finite support is now expressed by the standard primorial. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    {L : Submodule (ZMod p) S.ResidualSpace}
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    (primorial (p - 1) : ℤ) ∣ S.a * S.b * S.c :=
  S.residual_cofixed_forces_primorial_support hp5 hbe hline hstable hcofixed

/-! The `q = 3` instance supplies the oriented irreducibility conclusion. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    S.ResidualIsIrreducible :=
  S.residual_irreducible_of_three_good hp5 hbe hd

/-! Under the dyadic orientation, the same instance gives an escape element. -/
example (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ ∉ A.decompositionSubgroup ℚ ∧
      ∃ P : S.ResidualSpace,
        P ∈ S.residualZeroComponent A ∧
          S.residualRepresentation σ P ∉ S.residualZeroComponent A :=
  S.residual_escape_outside_decomposition_of_three_good_seven hp5 ha8 hd A hA

#print axioms DkMath.FLT.Frey.Source.residual_hno_of_small_good_prime
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_small_prime_support
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_prime_support
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_odd_prime_product_support
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_forces_primorial_support
#print axioms DkMath.FLT.Frey.Source.residual_irreducible_of_three_good
#print axioms DkMath.FLT.Frey.Source.residual_escape_outside_decomposition_of_three_good_seven

end
end DkMathTest.FLT.FreyHnoSmallGoodPrime
