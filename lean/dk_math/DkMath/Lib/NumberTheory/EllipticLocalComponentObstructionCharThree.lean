/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticLocalComponentObstruction
import DkMath.Lib.NumberTheory.WeierstrassNodalCenterCharThree

#print "file: DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharThree"

/-!
# The triadic local entry point

At the actual rational valuation subring at `3`, the explicit characteristic
three centre supplies `#E_sm ≤ 4 < p`.  Thus the double of any exact-order
`2*p` point is outside the smooth zero component.  All finite-cardinality
arguments take place over the rational residue field, before any extension.
-/

namespace DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharThree

open FreyLocalReduction EllipticLocalComponentObstruction
open WeierstrassNodalCenterCharThree EllipticSmoothReduction

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- At the triadic address the residue invariants construct the centre
internally, and the finite-residue theorem excludes the doubled point. -/
theorem localValuationSubring_three_double_not_mem_zeroComponent_of_residue_invariants
    (hp5 : 5 ≤ p) (W : WeierstrassCurve (localValuationSubring 3))
    (hΔ : (W.map (IsLocalRing.residue (localValuationSubring 3))).Δ = 0)
    (hc4 : (W.map (IsLocalRing.residue (localValuationSubring 3))).c₄ ≠ 0)
    {R : (W.map (localValuationSubring 3).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    2 • R ∉ zeroComponentSubgroup W := by
  let : CharP (IsLocalRing.ResidueField (localValuationSubring 3)) 3 :=
    ValuationPrimeSupport.charP_residueField (localValuationSubring 3)
      Nat.prime_three (localValuationSubring_liesOverPrime 3)
  exact localValuationSubring_double_not_mem_zeroComponent_of_singularCentre hp5
    (by omega) W (singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero _ hΔ hc4) hR

end
end DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharThree
