/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Topology.Algebra.ClopenNhdofOne

#print "file: DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration"

/-! # 開部分群 modulo の生成から profinite 群の稠密生成へ -/
namespace DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration

/-- profinite 群の閉部分群が、それを含む全開部分群で全群となるなら全群に等しい。 -/
theorem closed_eq_top_of_forall_open {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hclosed : IsClosed (H : Set G))
    (hopen : ∀ N : Subgroup G, IsOpen (N : Set G) → H ≤ N → N = ⊤) : H = ⊤ := by
  let C : ClosedSubgroup G := ⟨H, hclosed⟩
  have he := ProfiniteGrp.closedSubgroup_eq_sInf_open C
  apply le_antisymm le_top
  intro g _
  change g ∈ (C : Subgroup G)
  rw [he]
  apply Subgroup.mem_sInf.mpr
  intro N hN
  rw [hopen N hN.1 hN.2]
  exact Subgroup.mem_top g

/-- 任意の開商 modulo で部分群が全元を近似すれば、その閉包は全群。 -/
theorem closure_eq_top_of_open_approximation {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G)
    (happrox : ∀ N : Subgroup G, IsOpen (N : Set G) → H ≤ N →
      ∀ g : G, ∃ h ∈ H, h⁻¹ * g ∈ N) :
    H.topologicalClosure = ⊤ := by
  apply closed_eq_top_of_forall_open _ (Subgroup.isClosed_topologicalClosure H)
  intro N hN hHN
  apply le_antisymm le_top
  intro g _
  obtain ⟨h, hh, hdiff⟩ := happrox N hN ((Subgroup.le_topologicalClosure H).trans hHN) g
  have hhN : h ∈ N := hHN (Subgroup.le_topologicalClosure H hh)
  have hg := N.mul_mem hhN hdiff
  simpa only [mul_inv_cancel_left] using hg

end DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration
