/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFiniteActionFactor
import DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
import DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation

#print "file: DkMath.FLT.FreyResidueFrobeniusApproximation"

/-! # 同じ局所住所での有限剰余値 Frobenius 近似
同じ q 上の付値環と元の D 作用について、有限個の剰余値を同時に近似する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
open ValuationInertia
noncomputable section

/-- 実際の剰余作用は q 元の素体を固定する。 -/
def residueFieldAlgAction (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q) :
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
    letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
    A.decompositionSubgroup ℚ →* (IsLocalRing.ResidueField A ≃ₐ[ZMod q] IsLocalRing.ResidueField A) := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  refine { toFun := fun σ => AlgEquiv.ofRingEquiv (f := residueFieldAction A σ) ?_
           map_one' := ?_
           map_mul' := ?_ }
  · intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    simp
  · ext x
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f x) (map_one (residueFieldAction A))
  · intro σ τ
    ext x
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f x) (map_mul (residueFieldAction A) σ τ)

/-- 元の D の剰余作用と、素体上の自己同型としての作用は同じ値を与える。 -/
theorem residueFieldAlgAction_apply (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (σ : A.decompositionSubgroup ℚ) (x : IsLocalRing.ResidueField A) :
    residueFieldAlgAction A hA σ x = σ • x := rfl

/-- 実際の D の任意の元は、有限個の剰余値上で同じ Frobenius の冪に一致する。 -/
theorem residueFinite_frobenius_approx (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (σ : A.decompositionSubgroup ℚ) (s : Finset (IsLocalRing.ResidueField A)) :
    ∃ m : ℕ, ∀ x ∈ s, σ • x = (φ ^ m) • x := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  let : Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField A) := residue_isAlgebraic A hA
  have hf : ∀ x : IsLocalRing.ResidueField A,
      residueFieldAlgAction A hA φ x = x ^ Fintype.card (ZMod q) := by
    intro x
    rw [ZMod.card]
    exact residueFieldAction_frobenius A φ hφ x
  obtain ⟨m, hm⟩ := AlgebraicFiniteFieldApproximation.finite_values_frobenius
    (ZMod q) (IsLocalRing.ResidueField A) (residueFieldAlgAction A hA σ)
    (residueFieldAlgAction A hA φ) hf s
  refine ⟨m, fun x hx => ?_⟩
  have he := hm x hx
  rw [← map_pow (residueFieldAlgAction A hA)] at he
  exact he

end
end DkMath.FLT.Frey.Source
