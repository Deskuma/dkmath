/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaTailGaloisRoots
import DkMath.Lib.NumberTheory.InertiaRadicalCorrection

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalKernelTopology"

/-! # 根指標の閉核・減少性・交叉とコンパクト抽出
全段を固定する条件を、同じ根指標の全核への所属として正確に記述する。 -/
namespace DkMath.Lib.NumberTheory.CompactKernel
/-- 減少閉集合の交叉が開集合に含まれれば、有限段ですでに含まれる。 -/
theorem exists_subset_open {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (C : ℕ → Set X) (hc : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    (U : Set X) (hu : IsOpen U) (hsub : (⋂ n, C n) ⊆ U) : ∃ n, C n ⊆ U := by
  by_contra hn
  have hne : ∀ n, (C n ∩ Uᶜ).Nonempty := by
    intro n
    have hnot : ¬ C n ⊆ U := fun h => hn ⟨n, h⟩
    obtain ⟨x, hx, hxu⟩ := Set.not_subset.mp hnot
    exact ⟨x, hx, hxu⟩
  have hd : Directed (· ⊇ ·) (fun n => C n ∩ Uᶜ) := by
    intro n m
    exact ⟨max n m, fun x hx => ⟨hanti (le_max_left _ _) hx.1, hx.2⟩,
      fun x hx => ⟨hanti (le_max_right _ _) hx.1, hx.2⟩⟩
  have hclosed (n : ℕ) : IsClosed (C n ∩ Uᶜ) := (hc n).inter hu.isClosed_compl
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun n => C n ∩ Uᶜ) hd hne (fun n => (hclosed n).isCompact) hclosed
  have hall := Set.mem_iInter.mp hx
  exact (hall 0).2 (hsub (Set.mem_iInter.mpr (fun n => (hall n).1)))
end DkMath.Lib.NumberTheory.CompactKernel

namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ実際の慣性群は、元の Krull 位相でコンパクト。 -/
theorem inertia_compactSpace : CompactSpace (inertiaSubgroupIn A ℚ) :=
  isCompact_iff_compactSpace.mp (InertiaClosed.isClosed_inertia_map A).isCompact

/-- 同じ根指標の核は高い段ほど小さい。 -/
theorem character_kernel_antitone : Antitone (fun k => (character hp hq hpq A hA k).ker) := by
  intro i j hij σ hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  change character hp hq hpq A hA i σ = 1
  rw [← character_compat hp hq hpq A hA i d σ, hs, one_pow]

/-- 指標値に代数閉包の離散位相を導入せず、根の開固定群から閉核を得る。 -/
theorem character_kernel_isClosed (k : ℕ) :
    IsClosed ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ)) := by
  have he : ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ)) =
      Subtype.val ⁻¹' {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
        σ (radical p q hp k) = radical p q hp k} := by
    ext σ
    exact character_eq_one_iff_root_fixed hp hq hpq A hA k σ
  rw [he]
  exact (InertiaClosed.isClosed_setOf_apply (fun y => y = radical p q hp k)
    (radical p q hp k)).preimage continuous_subtype_val

include hq hpq hA in
/-- 全ての選んだ根を固定すれば、同じ q の任意の p 冪根を固定する。 -/
theorem all_radicals_fixed_of_tower (σ : inertiaSubgroupIn A ℚ)
    (hs : ∀ k, σ.val (radical p q hp k) = radical p q hp k)
    (α : AlgebraicClosure ℚ) (k : ℕ) (hα : α ^ (p ^ k) = (q : AlgebraicClosure ℚ)) : σ.val α = α := by
  let β := radical p q hp k
  have hβ : β ≠ 0 := radical_ne_zero hp hq k
  have hratio : (α / β) ^ (p ^ k) = 1 := by
    rw [div_pow, hα, PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k]
    exact div_self (by exact_mod_cast hq.ne_zero)
  have hf := inertia_fixes_primePower_root hp hq hpq A hA σ k (α / β) hratio
  have he : α = (α / β) * β := (div_mul_cancel₀ _ hβ).symm
  calc σ.val α = σ.val (α / β) * σ.val β := by conv_lhs => rw [he]; rw [map_mul]
       _ = (α / β) * β := by rw [hf, hs k]
       _ = α := div_mul_cancel₀ _ hβ

/-- 全根指標の核の交叉は、実際の全根固定 tail と同じ条件。 -/
theorem forall_character_kernel_iff_all_radicals (σ : inertiaSubgroupIn A ℚ) :
    (∀ k, σ ∈ (character hp hq hpq A hA k).ker) ↔
      ∀ α k, α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α := by
  constructor
  · intro hs
    exact all_radicals_fixed_of_tower hp hq hpq A hA σ
      (fun k => (character_eq_one_iff_root_fixed hp hq hpq A hA k σ).mp (hs k))
  · intro hs k
    exact (character_eq_one_iff_root_fixed hp hq hpq A hA k σ).mpr
      (hs _ k (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k))

/-- 集合としても同じ tail 核を回収する。 -/
theorem iInter_character_kernel_eq_tail :
    (⋂ k, ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ))) =
      {σ | σ.val ∈ (InertiaResidue.tailField A p q).fixingSubgroup} := by
  ext σ
  simp only [Set.mem_iInter, SetLike.mem_coe, Set.mem_ofPred_eq]
  exact (forall_character_kernel_iff_all_radicals hp hq hpq A hA σ).trans
    (InertiaResidue.mem_tailFixing_iff_all_radicals A σ).symm
end
end DkMath.Lib.NumberTheory.InertiaRadical

