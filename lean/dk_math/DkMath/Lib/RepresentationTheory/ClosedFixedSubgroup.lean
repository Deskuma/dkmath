/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

#print "file: DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup"

/-! # 閉固定部分群と、指定部分群・一元が生成する稠密部分群
密度は明示入力。特定の算術的 Frobenius の密度を供給しない。 -/
namespace DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- N と φ を含む閉部分群は、それらの生成群が稠密なら全体である。 -/
theorem eq_top_of_dense_join (N H : Subgroup G) (φ : G)
    (hclosed : IsClosed (H : Set G)) (hN : N ≤ H) (hφ : φ ∈ H)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) : H = ⊤ := by
  apply top_unique
  rw [← hdense]
  exact Subgroup.topologicalClosure_minimal _ (sup_le hN (Subgroup.zpowers_le.mpr hφ)) hclosed

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- 同じ N の剰余類に属する元は、N と併せて同じ部分群を生成する。 -/
theorem join_zpowers_eq_of_div_mem (N : Subgroup G) {φ ψ : G} (h : φ / ψ ∈ N) :
    N ⊔ Subgroup.zpowers φ = N ⊔ Subgroup.zpowers ψ := by
  have hφ : φ ∈ N ⊔ Subgroup.zpowers ψ := by
    have hm := (N ⊔ Subgroup.zpowers ψ).mul_mem
      ((le_sup_left : N ≤ N ⊔ Subgroup.zpowers ψ) h)
      ((le_sup_right : Subgroup.zpowers ψ ≤ N ⊔ Subgroup.zpowers ψ) (Subgroup.mem_zpowers ψ))
    simpa only [div_mul_cancel] using hm
  have hi : ψ / φ ∈ N := by simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using N.inv_mem h
  have hψ : ψ ∈ N ⊔ Subgroup.zpowers φ := by
    have hm := (N ⊔ Subgroup.zpowers φ).mul_mem
      ((le_sup_left : N ≤ N ⊔ Subgroup.zpowers φ) hi)
      ((le_sup_right : Subgroup.zpowers φ ≤ N ⊔ Subgroup.zpowers φ) (Subgroup.mem_zpowers φ))
    simpa only [div_mul_cancel] using hm
  exact le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr hφ))
    (sup_le le_sup_left (Subgroup.zpowers_le.mpr hψ))

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- 線形表現の一元を固定する元は部分群をなす。 -/
def linearStabilizer (ρ : G →* Module.End R M) (m : M) : Subgroup G where
  carrier := {g | ρ g m = m}
  one_mem' := by change ρ 1 m = m; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) m = m
    rw [map_mul]
    change ρ g (ρ h m) = m
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    have he := congrArg (fun f : Module.End R M => f m) (ρ.map_mul g⁻¹ g)
    change ρ (g⁻¹ * g) m = ρ g⁻¹ (ρ g m) at he
    rw [inv_mul_cancel, map_one] at he
    change m = ρ g⁻¹ (ρ g m) at he
    rw [hg] at he
    exact he.symm

/-- 閉固定条件と明示的密度から、同じ元の全群固定性を得る。 -/
theorem fixed_of_dense_join (ρ : G →* Module.End R M) (m : M) (N : Subgroup G) (φ : G)
    (hclosed : IsClosed {g : G | ρ g m = m})
    (hN : N ≤ ρ.ker) (hφ : ρ φ m = m)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) : ∀ g, ρ g m = m := by
  have ht := eq_top_of_dense_join N (linearStabilizer ρ m) φ hclosed
    (fun g hg => by change ρ g m = m; rw [show ρ g = 1 from hN hg]; rfl) hφ hdense
  intro g
  change g ∈ linearStabilizer ρ m
  rw [ht]
  exact Subgroup.mem_top g
end DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
