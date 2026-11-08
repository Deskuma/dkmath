/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure

#print "file: DkMathTest.FLT.FreyFiniteKernelClosure"

namespace FreyFiniteKernelClosureTest
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : DkMath.FLT.Frey.Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

-- Concrete original stage: no continuity, cyclicity, generator or kernel-comparison provider.
example : (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
    (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker :=
  T.radical_kernel_le_commonProjection_kernel A hp5 hq hqp haddr hA

example : IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :=
  T.commonTame_isCyclic A hp5 hq hqp haddr hA

example : Function.Injective (T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)) :=
  T.generator_evaluation_injective A hp5 hq hqp haddr hA

-- Compactness is necessary for eventual detection: descending tails of Nat never enter empty.
example : ¬ ∃ n : ℕ, {x : ℕ | n ≤ x} ⊆ (∅ : Set ℕ) := by
  rintro ⟨n, hn⟩
  exact hn (show n ∈ {x : ℕ | n ≤ x} from le_refl n)

-- An exponent bound is necessary to lower the stage: first-level kernel need not be zero.
example : (ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)) (3 : ZMod 9) = 0 ∧
    (3 : ZMod 9) ≠ 0 := by decide
end
end FreyFiniteKernelClosureTest

#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_eq_preimage
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_kernel_isOpen
#print axioms DkMath.Lib.NumberTheory.CompactKernel.exists_subset_open
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.inertia_compactSpace
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_antitone
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.character_kernel_isClosed
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.all_radicals_fixed_of_tower
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.forall_character_kernel_iff_all_radicals
#print axioms DkMath.Lib.NumberTheory.InertiaRadical.iInter_character_kernel_eq_tail
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.exists_radical_kernel_le_common
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_kernel_le_commonProjection_kernel
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.radical_fixed_evaluations_eq_zero
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.commonProjection_generator_generates
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.commonTame_isCyclic
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.generator_evaluation_injective
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator
