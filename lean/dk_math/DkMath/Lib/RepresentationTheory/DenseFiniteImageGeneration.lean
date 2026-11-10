/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration"

/-! # 明示的な密度から離散有限群像の Frobenius 生成へ -/
namespace DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- 慣性 N を消す連続離散群像は、明示密度の下で φ の像で生成される。 -/
theorem mem_zpowers_of_dense (ρ : G →* H) (hρ : Continuous ρ) (N : Subgroup G)
    (hN : N ≤ ρ.ker) (φ : G)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (g : G) :
    ρ g ∈ Subgroup.zpowers (ρ φ) := by
  let J := (Subgroup.zpowers (ρ φ)).comap ρ
  have hj : IsClosed (J : Set G) := by
    change IsClosed (ρ ⁻¹' (Subgroup.zpowers (ρ φ) : Set H))
    exact (isClosed_discrete _).preimage hρ
  have ht := ClosedFixedSubgroup.eq_top_of_dense_join N J φ hj
    (fun σ hσ => by change ρ σ ∈ Subgroup.zpowers (ρ φ); rw [show ρ σ = 1 from hN hσ]; exact Subgroup.one_mem _)
    (Subgroup.mem_zpowers (ρ φ)) hdense
  change g ∈ J
  rw [ht]
  exact Subgroup.mem_top g

omit [TopologicalSpace H] [DiscreteTopology H] in
/-- 有限群での一元生成は、元の Frobenius の位数未満の自然数冪で証明できる。 -/
theorem bounded_power_of_mem_zpowers [Finite H] (a b : H) (hb : b ∈ Subgroup.zpowers a) :
    ∃ n : ℕ, n < orderOf a ∧ a ^ n = b := by
  have hp : b ∈ Submonoid.powers a := mem_powers_iff_mem_zpowers.mpr hb
  obtain ⟨m, hm⟩ := hp
  exact ⟨m % orderOf a, Nat.mod_lt _ (orderOf_pos a), (pow_mod_orderOf a m).trans hm⟩
end DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration
