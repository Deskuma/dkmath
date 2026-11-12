/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusOpenQuotient
import DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration

#print "file: DkMath.FLT.FreyResidueFrobeniusDense"

/-! # 実際の分解群の慣性と Frobenius による稠密生成 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open ValuationInertia
noncomputable section

/-- 同じ局所住所では、慣性と実際の Frobenius は分解群を位相的に生成する。 -/
theorem frobeniusInertia_dense (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ := by
  let : CompactSpace (A.decompositionSubgroup ℚ) := decomposition_compact A
  apply ProfiniteOpenGeneration.closure_eq_top_of_open_approximation
  intro N hN hHN σ
  have hI : A.inertiaSubgroup ℚ ≤ N := le_sup_left.trans hHN
  obtain ⟨m, hm⟩ := exists_frobenius_power_mod_open A hA φ hφ N hN hI σ
  refine ⟨φ ^ m, ?_, hm⟩
  exact (show Subgroup.zpowers φ ≤ A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ from le_sup_right)
    (Subgroup.npow_mem_zpowers φ m)

/-- 同じ住所では、稠密生成する実際の Frobenius を内部構成できる。 -/
theorem exists_frobeniusInertia_dense (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q) :
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧
      (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  exact ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, frobeniusInertia_dense A hA _ hφ⟩

end
end DkMath.FLT.Frey.Source
