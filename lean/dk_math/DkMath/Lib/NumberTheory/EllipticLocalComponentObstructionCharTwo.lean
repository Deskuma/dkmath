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

end
end DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo
