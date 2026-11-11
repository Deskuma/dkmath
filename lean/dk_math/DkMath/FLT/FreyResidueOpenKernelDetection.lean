/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusApproximation
import DkMath.Lib.NumberTheory.InertiaKrullClosed
import DkMath.Lib.RepresentationTheory.CompactFiniteDetection

#print "file: DkMath.FLT.FreyResidueOpenKernelDetection"

/-! # 実際の開作用核を有限個の剰余値で検出する
分解群の Krull コンパクト性と剰余作用の各軌道の連続性を用いる。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open ValuationInertia
noncomputable section

/-- 実際の分解群は代数閉包のコンパクト Galois 群の閉部分群。 -/
theorem decomposition_compact (A : ValuationSubring (AlgebraicClosure ℚ)) :
    CompactSpace (A.decompositionSubgroup ℚ) := by
  have h := InertiaStability.isClosed_decompositionSubgroup (K := ℚ) A
  exact h.isClosedEmbedding_subtypeVal.compactSpace

/-- 一つの剰余値を動かす分解群の元は、元の Krull 位相で開集合をなす。 -/
theorem residue_moved_isOpen (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : IsLocalRing.ResidueField A) :
    IsOpen {σ : A.decompositionSubgroup ℚ | σ • x ≠ x} := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have he : {σ : A.decompositionSubgroup ℚ |
      σ • IsLocalRing.residue A a ≠ IsLocalRing.residue A a} =
      Subtype.val ⁻¹' {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
        ¬ A.valuation (σ a - a) < 1} := by
    ext σ
    change (σ • IsLocalRing.residue A a ≠ IsLocalRing.residue A a) ↔
      ¬ A.valuation (σ.val a - a) < 1
    have hk : (σ • IsLocalRing.residue A a = IsLocalRing.residue A a) ↔
        A.valuation (σ.val a - a) < 1 := by
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
        IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      rfl
    exact not_congr hk
  rw [he]
  exact (InertiaClosed.isOpen_setOf_apply (K := ℚ)
    (fun y => ¬ A.valuation (y - a) < 1) (a : AlgebraicClosure ℚ)).preimage continuous_subtype_val

/-- 慣性を含む任意の開部分群は、有限個の実際の剰余値の固定性で検出される。 -/
theorem exists_finite_residue_detection (A : ValuationSubring (AlgebraicClosure ℚ))
    (N : Subgroup (A.decompositionSubgroup ℚ))
    (hN : IsOpen (N : Set (A.decompositionSubgroup ℚ)))
    (hI : A.inertiaSubgroup ℚ ≤ N) :
    ∃ s : Finset (IsLocalRing.ResidueField A),
      ∀ σ : A.decompositionSubgroup ℚ, (∀ x ∈ s, σ • x = x) → σ ∈ N := by
  let : CompactSpace (A.decompositionSubgroup ℚ) := decomposition_compact A
  apply CompactFiniteDetection.exists_finite_detecting_set (N : Set (A.decompositionSubgroup ℚ)) hN
    (fun σ x => σ • x) (residue_moved_isOpen A)
  intro σ hσ
  by_contra hnone
  push Not at hnone
  apply hσ
  apply hI
  change residueFieldAction A σ = 1
  ext x
  exact hnone x

end
end DkMath.FLT.Frey.Source
