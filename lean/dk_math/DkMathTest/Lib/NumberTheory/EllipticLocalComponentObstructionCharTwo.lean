/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo

#print "file: DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo"

/-! 教科書回帰例：標数2の節点構成から局所成分商障害への接続。 -/

namespace DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo

open DkMath.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo
open DkMath.Lib.NumberTheory.FreyLocalReduction
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open IsLocalRing

noncomputable section

variable {p : ℕ} [Fact p.Prime]

example (hp5 : 5 ≤ p) (hp2 : p ≠ 2)
    (W : WeierstrassCurve (localValuationSubring 2))
    (hΔ : (W.map (IsLocalRing.residue (localValuationSubring 2))).Δ = 0)
    (hc4 : (W.map (IsLocalRing.residue (localValuationSubring 2))).c₄ ≠ 0)
    {R : (W.map (localValuationSubring 2).subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction W R ∧
      p ∣ Nat.card ((W.map (localValuationSubring 2).subtype).toAffine.Point ⧸
        zeroComponentSubgroup W) :=
  localValuationSubring_two_component_prime_dvd_of_residue_invariants
    hp5 hp2 W hΔ hc4 hR

#print axioms localValuationSubring_two_component_prime_dvd_of_residue_invariants

end
end DkMathTest.Lib.NumberTheory.EllipticLocalComponentObstructionCharTwo
