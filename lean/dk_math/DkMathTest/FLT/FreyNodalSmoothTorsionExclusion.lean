/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNodalSmoothTorsionExclusion
import Lean.Util.CollectAxioms

#print "file: DkMathTest.FLT.FreyNodalSmoothTorsionExclusion"

/-!
# Regression entry: the Cofixed torsion witness leaves the smooth component

The example retains the valuation model, its equality with the integer quotient,
and its critical centre as hypotheses.  It checks the exact intended conclusion:
the point constructed by the Cofixed branch has order `2*p` and cannot have
smooth reduction at that model.
-/

namespace DkMathTest.FLT.FreyNodalSmoothTorsionExclusion

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.WeierstrassVariableChange
open DkMath.Lib.RepresentationTheory
open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

example (hp5 : 5 ≤ p) (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) (hcofixed : IsCofixedOn S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring ℚ} [Fintype (ResidueField A)]
    (hunit : A.valuation (p : ℚ) = 1)
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp : q < p)
    (W : WeierstrassCurve A)
    (hmodel : W.map A.subtype =
      (S.residualIntegerKernelModel L hline hstable).map (Int.castRingHom ℚ))
    (C : CriticalCentre A (W.map A.subtype)) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hstable).map
        (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p ∧
        ¬ HasSmoothReduction W (pointEquivOfModelEq hmodel.symm Q) :=
  S.residual_cofixed_exists_two_p_torsion_not_smooth_of_criticalCentre hp5 hbe L hline
    hstable hcofixed hunit hresidueCard hqp W hmodel C

#print axioms DkMath.FLT.Frey.Source.residual_cofixed_exists_two_p_torsion_not_smooth_of_criticalCentre

end
end DkMathTest.FLT.FreyNodalSmoothTorsionExclusion
