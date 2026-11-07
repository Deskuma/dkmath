/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1PrimeOrder

#print "file: DkMath.FLT.FreyFixedQuotientTrivial"

/-!
# 同じ Q/F 全体の慣性固定性

F=Q^I。元の有限捩れにおける差分積零性から、全ての Q の作用差は F に入る。
Q/F の自明作用と、元の Q の作用を区別する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ Q/F の全ての元は、同じ実際の慣性作用で固定される。 -/
theorem ResidualCyclicStage.fixedQuotient_all_invariant (z : T.fixedQuotientCoefficient A) :
    z ∈ (T.fixedQuotientCoefficient A).ρ.invariants := by
  obtain ⟨u, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  exact (T.fixedCosetInvariant hp5 hq hqp haddr A hA x).property

/-- 同じ Q/F の作用そのものが自明。元の Q の作用自明性は主張しない。 -/
theorem ResidualCyclicStage.fixedQuotient_action_trivial (σ : inertiaSubgroupIn A ℚ)
    (z : T.fixedQuotientCoefficient A) : (T.fixedQuotientCoefficient A).ρ σ z = z :=
  T.fixedQuotient_all_invariant hp5 hq hqp haddr A hA z σ

/-- 同じ全ての剰余類を保つ、不変部分加群と Q/F の整数線形同型。 -/
def ResidualCyclicStage.fixedQuotientInvariantEquiv :
    (T.fixedQuotientCoefficient A).ρ.invariants ≃ₗ[ℤ] T.fixedQuotientCoefficient A where
  toFun z := z.val
  invFun z := ⟨z, T.fixedQuotient_all_invariant hp5 hq hqp haddr A hA z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end DkMath.FLT.Frey.Source
