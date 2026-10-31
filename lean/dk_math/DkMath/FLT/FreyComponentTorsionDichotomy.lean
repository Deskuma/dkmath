/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNodalSmoothTorsionExclusion
import DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient
import DkMath.Lib.NumberTheory.EllipticSmoothReduction

#print "file: DkMath.FLT.FreyComponentTorsionDichotomy"

/-!
# The remaining component-quotient alternatives for a Cofixed torsion point

The Cofixed branch constructs a rational point of exact order `2*p` on the
integer quotient curve.  At a local integral model, its subgroup of smooth
points is `zeroComponentSubgroup W`.  The general quotient lemma therefore
gives a precise next boundary:

* either twice the Cofixed point is smooth; or
* `p` divides the cardinality of the quotient by the smooth subgroup.

This is the formal replacement for the informal phrase “the torsion may live
in the component group”.  It neither constructs a finite component group nor
proves the quotient finite.  In particular, it is not an unconditional `hno`:
excluding its two alternatives needs genuinely new local reduction input.
-/

namespace DkMath.FLT.Frey.Source

open WeierstrassCurve IsLocalRing
open DkMath.Lib.Algebra
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.WeierstrassVariableChange

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/--
A Cofixed stable line yields a rational point of exact order `2*p`.  After
transporting that point to any explicitly identified integral model, either
its double belongs to the smooth zero component or `p` divides the natural
cardinality of the associated component quotient.

The equality `hmodel` remains an input on purpose.  It marks the still
separate task of constructing an integral model at a chosen prime address;
the proof below only transports point order and applies the abstract quotient
theorem.
-/
theorem residual_cofixed_two_p_torsion_component_dichotomy
    (hp5 : 5 ≤ p) (hbe : Even S.b)
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
          p ∣ Nat.card (((W.map A.subtype).toAffine.Point) ⧸ zeroComponentSubgroup W)) := by
  obtain ⟨Q, hQorder⟩ := S.residual_cofixed_implies_rational_two_p_torsion
    (by omega) hbe L hline hcofixed
  refine ⟨Q, hQorder, ?_⟩
  apply two_nsmul_mem_or_prime_dvd_natCard_quotient_of_addOrder_eq_two_mul_prime
    (zeroComponentSubgroup W) (pointEquivOfModelEq hmodel.symm Q)
  exact (pointEquivOfModelEq hmodel.symm).addOrderOf_eq Q |>.trans hQorder

/--
At a nodal address below `p`, the first alternative is sharpened by the
smooth-point cardinality bound: the Cofixed point itself is outside the zero
component.  What remains is exactly the final component-group boundary:

* `2 • Q` returns to the zero component; or
* the smooth-component quotient has cardinality divisible by `p`.

The hypotheses `hmodel` and `C` are retained rather than reconstructed here.
They record the two geometric inputs still needed to use this theorem at a
concrete bad prime.  In particular, the result does not assert a general
`hno`, because neither remaining alternative is contradicted by group theory
alone.
-/
theorem residual_cofixed_component_dichotomy_of_criticalCentre_card_bound
    (hp5 : 5 ≤ p) (hbe : Even S.b)
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
          p ∣ Nat.card (((W.map A.subtype).toAffine.Point) ⧸ zeroComponentSubgroup W)) := by
  obtain ⟨Q, hQorder⟩ := S.residual_cofixed_implies_rational_two_p_torsion
    (by omega) hbe L hline hcofixed
  have htransportOrder : addOrderOf (pointEquivOfModelEq hmodel.symm Q) = 2 * p :=
    (pointEquivOfModelEq hmodel.symm).addOrderOf_eq Q |>.trans hQorder
  refine ⟨Q, hQorder, ?_, ?_⟩
  · intro hQsmooth
    exact
      (not_addOrder_eq_two_mul_prime_of_smooth_of_criticalCentre_card_bound W hp5 hunit
        hresidueCard hqp C hQsmooth) htransportOrder
  · exact two_nsmul_mem_or_prime_dvd_natCard_quotient_of_addOrder_eq_two_mul_prime
      (zeroComponentSubgroup W) (pointEquivOfModelEq hmodel.symm Q) htransportOrder

end
end DkMath.FLT.Frey.Source
