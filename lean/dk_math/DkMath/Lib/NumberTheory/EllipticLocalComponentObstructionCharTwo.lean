/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction
import DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharTwo

#print "file: DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo"

/-!
# The characteristic-two local entry point

The characteristic-two centre constructor and the finite-residue component
obstruction now compose directly.  For the actual valuation subring at `2`, a
residue model with `Δ = 0` and `c₄ ≠ 0` supplies its rational `SingularCentre`
internally, so callers do not have to provide tangent directions or make a
splitness choice.

As in the general finite-local theorem, the conclusion is the abstract
zero-component quotient divisibility.  This module does not identify that
quotient with a Néron component group and does not claim the global `hno`
contradiction.
-/

namespace DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo

open IsLocalRing
open FreyLocalReduction
open EllipticLocalComponentObstruction
open WeierstrassNodalCenterCharTwo
open EllipticNodalSmoothCard
open EllipticGoodReductionSeparation
open EllipticSmoothReduction
open EllipticNodalSmoothTorsionExclusion
open EllipticSmoothTorsionPrimeExclusion
open DkMath.Lib.Algebra

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- [DkMath.Lib] At the dyadic address, a residue discriminant zero and
nonzero `c₄` construct the singular centre and feed the finite-local component
obstruction.  The only remaining geometric inputs are the residue invariant
equalities and the exact-order `2*p` point.
-/
theorem localValuationSubring_two_component_prime_dvd_of_residue_invariants
    (hp5 : 5 ≤ p) (hp2 : p ≠ 2)
    (W : WeierstrassCurve (localValuationSubring 2))
    (hΔ : (W.map (IsLocalRing.residue (localValuationSubring 2))).Δ = 0)
    (hc4 : (W.map (IsLocalRing.residue (localValuationSubring 2))).c₄ ≠ 0)
    {R : (W.map (localValuationSubring 2).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction W R ∧
      p ∣ Nat.card ((W.map (localValuationSubring 2).subtype).toAffine.Point ⧸
        zeroComponentSubgroup W) := by
  let : CharP (IsLocalRing.ResidueField (localValuationSubring 2)) 2 :=
    ValuationPrimeSupport.charP_residueField (localValuationSubring 2)
      Nat.prime_two (localValuationSubring_liesOverPrime 2)
  let C : SingularCentre (W.map (IsLocalRing.residue (localValuationSubring 2))) :=
    singularCentre_of_char_two_of_delta_zero_of_c4_ne_zero
      (W.map (IsLocalRing.residue (localValuationSubring 2))) hΔ hc4
  exact localValuationSubring_component_prime_dvd_of_singularCentre
    hp5 (Ne.symm hp2) (by omega) W C hR

/--
At the same dyadic nodal address, the double of an exact `2*p` point cannot
belong to the smooth zero component.  This is the stronger pointwise form of
the preceding cardinality divisibility theorem: `2 • R` is a nonzero
`p`-torsion point, while the singular residue fibre has cardinality strictly
smaller than `p`.
-/
theorem localValuationSubring_two_double_not_mem_zeroComponent_of_residue_invariants
    (hp5 : 5 ≤ p)
    (W : WeierstrassCurve (localValuationSubring 2))
    (hΔ : (W.map (IsLocalRing.residue (localValuationSubring 2))).Δ = 0)
    (hc4 : (W.map (IsLocalRing.residue (localValuationSubring 2))).c₄ ≠ 0)
    {R : (W.map (localValuationSubring 2).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    2 • R ∉ zeroComponentSubgroup W := by
  let : CharP (IsLocalRing.ResidueField (localValuationSubring 2)) 2 :=
    ValuationPrimeSupport.charP_residueField (localValuationSubring 2)
      Nat.prime_two (localValuationSubring_liesOverPrime 2)
  let C : SingularCentre (W.map (IsLocalRing.residue (localValuationSubring 2))) :=
    singularCentre_of_char_two_of_delta_zero_of_c4_ne_zero
      (W.map (IsLocalRing.residue (localValuationSubring 2))) hΔ hc4
  let A := localValuationSubring 2
  have hunit : A.valuation (p : ℚ) = 1 :=
    localValuationSubring_prime_valuation_eq_one (q := 2) (p := p) (by omega)
  have hresidueCard : Fintype.card (IsLocalRing.ResidueField A) ≤ 2 := by
    rw [localValuationSubringResidueField_card 2]
  let _ : Finite ((W.map (IsLocalRing.residue A)).toAffine.Point) := finitePoints C
  have hpos : 0 < Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) :=
    natCard_points_pos C
  have hbound : Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) ≤
      Fintype.card (IsLocalRing.ResidueField A) + 1 :=
    natCard_points_le_card_add_one C
  have hlt : Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) < p := by
    calc
      Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) ≤
          Fintype.card (IsLocalRing.ResidueField A) + 1 := hbound
      _ ≤ 2 + 1 := Nat.add_le_add_right hresidueCard 1
      _ < p := add_one_lt_of_prime_lt_of_five_le hp5 (by omega)
  have hcard : ¬ p ∣ Nat.card ((W.map (IsLocalRing.residue A)).toAffine.Point) :=
    prime_not_dvd_of_pos_of_lt hpos hlt
  have hdouble_ne : 2 • R ≠ 0 := by
    intro hz
    have hdiv : 2 * p ∣ 2 := by
      rw [← hR]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    have hqge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hle : 2 * p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  intro hdouble
  have hsmooth : HasSmoothReduction W (2 • R) :=
    (mem_zeroComponentSubgroup_iff W).mp hdouble
  have hpdouble : p • (2 • R) = 0 := by
    have htwoq : (2 * p) • R = 0 := by
      rw [← hR]
      exact addOrderOf_nsmul_eq_zero R
    exact (mul_nsmul R 2 p).symm.trans htwoq
  exact hdouble_ne (eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard
    W hunit hcard hsmooth hpdouble)

end
end DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo
