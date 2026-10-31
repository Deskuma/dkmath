/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient
import DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
import DkMath.Lib.NumberTheory.FreyLocalValuationSubring
import DkMath.Lib.NumberTheory.ValuationPrimeSupport

#print "file: DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction"

/-!
# A finite-residue local component obstruction

The abstract nodal exclusion theorem is formulated for an arbitrary valuation
subring with a supplied finite residue-field bound.  That interface is useful
for geometric arguments over an algebraic closure, but the residue field of an
algebraically closed valuation ring is not the finite field at an actual prime
address.  This file supplies the arithmetic specialization which is safe to
use for the `q`-local model over `ℚ`.

For `q < p`, `p ≥ 5`, a supplied rational singular centre gives

* a finite residue point group of cardinality strictly smaller than `p`,
* exclusion of exact `2*p`-torsion from the smooth zero component, and
* divisibility of the abstract quotient by that zero component by `p`.

The final statement is deliberately about the quotient by the smooth subgroup.
It is not yet an identification with a Néron component group, and therefore it
does not by itself close the global `hno` argument.
-/

namespace DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction

open IsLocalRing
open ValuationPrimeSupport
open FreyLocalReduction
open EllipticNodalSmoothTorsionExclusion
open EllipticNodalSmoothCentre
open EllipticNodalSmoothCard
open EllipticCriticalCentre
open EllipticSmoothTorsionPrimeExclusion
open EllipticGoodReductionSeparation
open EllipticSmoothReduction
open WeierstrassCurve
open DkMath.Lib.Algebra

noncomputable section

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

noncomputable instance localValuationSubringResidueField_decidableEq :
    DecidableEq (ResidueField (localValuationSubring q)) := Classical.decEq _

/-- The `q`-local valuation of a distinct prime `p` is the normalized unit value.

This is the arithmetic bridge missing from the algebraically closed conditional
theorems: `localValuationSubring q` lies over `q`, so a prime `p ≠ q` is a unit
and its valuation is exactly one in the convention used by the reduction API.
-/
theorem localValuationSubring_prime_valuation_eq_one
    (hqp : q ≠ p) :
    (localValuationSubring q).valuation (p : ℚ) = 1 := by
  apply valuation_intCast_eq_one_of_not_dvd (localValuationSubring q)
    (Fact.out : q.Prime)
  · exact (ValuationSubring.mem_nonunits_iff _).mp
      (localValuationSubring_liesOverPrime q)
  · intro hdiv
    have hnat : q ∣ p := Int.natCast_dvd_natCast.mp hdiv
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hnat with hqone | hqeq
    · exact (Fact.out : q.Prime).ne_one hqone
    · exact hqp hqeq

/-- A finite-residue nodal model at an actual prime address forces the first
component obstruction for every exact `2*p` point.

The proof is a direct specialization of the general nodal torsion exclusion:
the residue field of `localValuationSubring q` is canonically `ZMod q`, hence
has cardinality `q`; the point-count estimate gives a cardinality `< p`; the
smooth reduction theorem then excludes the point from the zero component, and
the additive quotient lemma supplies `p ∣ # (E/E₀)`.
-/
theorem localValuationSubring_component_prime_dvd_of_singularCentre
    (hp5 : 5 ≤ p) (hqp : q ≠ p) (hqp' : q < p)
    (W : WeierstrassCurve (localValuationSubring q))
    (C : SingularCentre (W.map (IsLocalRing.residue (localValuationSubring q))))
    {R : (W.map (localValuationSubring q).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction W R ∧
      p ∣ Nat.card ((W.map (localValuationSubring q).subtype).toAffine.Point ⧸
        zeroComponentSubgroup W) := by
  classical
  let A := localValuationSubring q
  have hunit : A.valuation (p : ℚ) = 1 := by
    exact localValuationSubring_prime_valuation_eq_one hqp
  have hresidueCard : Fintype.card (ResidueField A) ≤ q := by
    rw [localValuationSubringResidueField_card q]
  have hcard : ¬ p ∣ Nat.card ((W.map (residue A)).toAffine.Point) := by
    let _ : Finite ((W.map (residue A)).toAffine.Point) := finitePoints C
    have hpos : 0 < Nat.card ((W.map (residue A)).toAffine.Point) :=
      natCard_points_pos C
    have hbound : Nat.card ((W.map (residue A)).toAffine.Point) ≤
        Fintype.card (ResidueField A) + 1 := natCard_points_le_card_add_one C
    have hlt : Nat.card ((W.map (residue A)).toAffine.Point) < p := by
      calc
        Nat.card ((W.map (residue A)).toAffine.Point) ≤
            Fintype.card (ResidueField A) + 1 := hbound
        _ ≤ q + 1 := Nat.add_le_add_right hresidueCard 1
        _ < p := add_one_lt_of_prime_lt_of_five_le hp5 hqp'
    exact prime_not_dvd_of_pos_of_lt hpos hlt
  have hnot : ¬ HasSmoothReduction W R := by
    intro hRsmooth
    exact (not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound W hp5 hunit
      hresidueCard hqp' C hRsmooth) hR
  have hker : ∀ x : (W.map A.subtype).toAffine.Point,
      x ∈ zeroComponentSubgroup W → p • x = 0 → x = 0 := by
    intro x hx hpx
    have hsmooth : HasSmoothReduction W x := (mem_zeroComponentSubgroup_iff W).mp hx
    exact eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard W hunit hcard
      hsmooth hpx
  refine ⟨hnot, ?_⟩
  exact prime_dvd_natCard_quotient_of_two_p_torsion
    (zeroComponentSubgroup W) R hR hker

end
end DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction
