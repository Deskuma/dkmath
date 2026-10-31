/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyComponentTorsionDichotomy

#print "file: DkMathTest.FLT.FreyComponentTorsionDichotomy"

/-!
# Regression use for the Cofixed component-quotient dichotomy

The example deliberately retains the model-identification equality.  It is
not a proof that a component group exists or is finite; it checks that the
proved theorem exposes exactly the two remaining local alternatives.
-/

namespace DkMathTest.FLT.FreyComponentTorsionDichotomy

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.WeierstrassVariableChange
open DkMath.Lib.RepresentationTheory
open WeierstrassCurve IsLocalRing

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) (hcofixed : IsCofixedOn S.residualRepresentation L)
    {A : ValuationSubring ℚ} [DecidableEq (ResidueField A)] (W : WeierstrassCurve A)
    (hmodel : W.map A.subtype =
      (S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ)) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hstable).map
        (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p ∧
        (2 • pointEquivOfModelEq hmodel.symm Q ∈ zeroComponentSubgroup W ∨
          p ∣ Nat.card (((W.map A.subtype).toAffine.Point) ⧸ zeroComponentSubgroup W)) :=
  S.residual_cofixed_two_p_torsion_component_dichotomy
    hp5 hbe L hline hstable hcofixed W hmodel

/-! At a rational nodal centre below `p`, the same point is first excluded
    from the zero component, leaving only the two component alternatives. -/
example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) (hcofixed : IsCofixedOn S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring ℚ}
    [Fintype (ResidueField A)] [DecidableEq (ResidueField A)]
    (hunit : A.valuation (p : ℚ) = 1)
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp : q < p)
    (W : WeierstrassCurve A)
    (hmodel : W.map A.subtype =
      (S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ))
    (C : CriticalCentre A (W.map A.subtype)) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hstable).map
        (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p ∧
      ¬ HasSmoothReduction W (pointEquivOfModelEq hmodel.symm Q) ∧
        (2 • pointEquivOfModelEq hmodel.symm Q ∈ zeroComponentSubgroup W ∨
          p ∣ Nat.card (((W.map A.subtype).toAffine.Point) ⧸ zeroComponentSubgroup W)) :=
  S.residual_cofixed_component_dichotomy_of_criticalCentre_card_bound
    hp5 hbe L hline hstable hcofixed hunit hresidueCard hqp W hmodel C

#print axioms DkMath.FLT.Frey.Source.residual_cofixed_two_p_torsion_component_dichotomy
#print axioms DkMath.FLT.Frey.Source.residual_cofixed_component_dichotomy_of_criticalCentre_card_bound

end
end DkMathTest.FLT.FreyComponentTorsionDichotomy
