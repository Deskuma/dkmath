/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyStableLineDiscriminantCriterion

#print "file: DkMathTest.FLT.FreyStableLineDiscriminantCriterion"

namespace DkMathTest.FreyStableLineDiscriminantCriterion

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.ValuationInertia

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 教科書回帰例：既約性を2上の零成分直線の非安定性へ輸送する。 -/
example (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    S.ResidualIsIrreducible ↔
      ¬ S.IsGaloisStable (S.residualZeroComponent A) :=
  residual_irreducible_iff_zeroComponent_not_stable_at_two S hp5 A hA

/-- 教科書回帰例：向き付きSourceのhnoを零成分直線の非安定性へ縮約する。 -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ¬ S.IsGaloisStable (S.residualZeroComponent A) :=
  residual_hno_iff_zeroComponent_not_stable_at_two S hp5 hbe A hA

/-- 教科書回帰例：hnoを零成分からの大域ガロア脱出へ変換する。 -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        ∃ P : S.ResidualSpace,
          P ∈ S.residualZeroComponent A ∧
            S.residualRepresentation σ P ∉ S.residualZeroComponent A :=
  residual_hno_iff_exists_zeroComponent_line_escape S hp5 hbe A hA

/-- 教科書回帰例：`a ≡ 7 mod 8` では脱出元を2上の分解群外へ限定する。 -/
example (hp5 : 5 ≤ p) (hbe : Even S.b) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        σ ∉ A.decompositionSubgroup ℚ ∧
        ∃ P : S.ResidualSpace,
          P ∈ S.residualZeroComponent A ∧
            S.residualRepresentation σ P ∉ S.residualZeroComponent A :=
  residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven
    S hp5 hbe ha8 A hA

#print axioms DkMath.FLT.Frey.Source.residual_irreducible_iff_zeroComponent_not_stable_at_two
#print axioms DkMath.FLT.Frey.Source.residual_hno_iff_zeroComponent_not_stable_at_two
#print axioms DkMath.FLT.Frey.Source.residual_hno_iff_exists_zeroComponent_line_escape
#print axioms DkMath.FLT.Frey.Source.residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven

end DkMathTest.FreyStableLineDiscriminantCriterion
