/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusResonantLift
import DkMath.FLT.FreyCofixedCyclotomic

#print "file: DkMath.FLT.FreyResidualCofixedUpperClass"

/-! # 元の残余直線と上段商の p 捩れ像
底の直線そのものは上段商で零になる。cofixed 性から E[p] の像は大域的に固定される。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の底に入る上段点は、同じ上段商で零になる。 -/
theorem ResidualCyclicStage.upperClass_eq_zero_of_base
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∈ pointSubgroup S.rationalCurve p L) :
    (QuotientAddGroup.mk' T.upperStage) x = 0 := by
  apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) x).mpr
  exact T.base hx

/-- cofixed 性の下で、元の曲線の p 捩れから来た上段商の類は全 Galois 元で固定される。 -/
theorem ResidualCyclicStage.upperClass_fixed_of_cofixed_p_torsion
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (hx : p • x.val = 0)
    (σ : Field.absoluteGaloisGroup ℚ) :
    T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
      (QuotientAddGroup.mk' T.upperStage) x := by
  let P : S.ResidualSpace := ⟨x.val, hx⟩
  have hdiff : pointAction S.rationalCurve σ x.val - x.val ∈ pointSubgroup S.rationalCurve p L := by
    refine ⟨S.residualRepresentation σ P - P, hcofixed σ P, ?_⟩
    rfl
  change (QuotientAddGroup.mk' T.upperStage)
      (representation S.rationalCurve (p ^ (n + 1 + 1)) σ x) =
    (QuotientAddGroup.mk' T.upperStage) x
  apply QuotientAddGroup.eq.mpr
  change -pointAction S.rationalCurve σ x.val + x.val ∈ T.carrier
  convert T.carrier.neg_mem (T.base hdiff) using 1
  abel

end
end DkMath.FLT.Frey.Source
