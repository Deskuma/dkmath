/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRationalTwoPTorsion
import DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion

#print "file: DkMath.FLT.FreyNodalSmoothTorsionExclusion"

/-!
# NOTE-032: Cofixed `2p`-torsion cannot remain in a nodal zero component

The Cofixed branch already constructs a rational point of exact order `2*p`
on the integer kernel quotient.  The local nodal theory proves that a smooth
point of this order is impossible at a residue address `q < p`, provided a
critical centre of an integral model is available.

This module makes that interface explicit.  It does **not** identify the
integral valuation model of the Frey quotient or construct its critical
centre from multiplicative reduction.  Those two facts remain hypotheses;
under them the conclusion is precisely that the concrete Cofixed point lies
outside the smooth zero component.
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve IsLocalRing
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.WeierstrassVariableChange

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/--
If a Cofixed stable line supplies its rational point of exact order `2*p`,
then that point cannot have smooth reduction at a local model with a critical
centre and residue cardinality below `p`.

The equation `hmodel` is deliberately retained: it records the pending
transport from the actual quotient model to the chosen valuation model rather
than silently identifying two point types.  The conclusion is existential only
because the earlier rational-torsion theorem constructs the point
existentially; its order and its failure of smooth reduction are both proved.
-/
theorem residual_cofixed_exists_two_p_torsion_not_smooth_of_criticalCentre
    (hp5 : 5 ≤ p) (hbe : Even S.b)
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
        ¬ HasSmoothReduction W (pointEquivOfModelEq hmodel.symm Q) := by
  obtain ⟨Q, hQorder⟩ := S.residual_cofixed_implies_rational_two_p_torsion
    (by omega) hbe L hline hcofixed
  refine ⟨Q, hQorder, ?_⟩
  intro hQsmooth
  have htransportOrder : addOrderOf (pointEquivOfModelEq hmodel.symm Q) = 2 * p :=
    (pointEquivOfModelEq hmodel.symm).addOrderOf_eq Q |>.trans hQorder
  exact
    (not_addOrder_eq_two_mul_prime_of_smooth_of_criticalCentre_card_bound W hp5 hunit
      hresidueCard hqp C hQsmooth) htransportOrder

end
end DkMath.FLT.Frey.Source
