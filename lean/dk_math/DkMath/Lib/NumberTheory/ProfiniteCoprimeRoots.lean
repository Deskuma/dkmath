/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots"

/-! # 全有限商で p と素な位数を持つ副有限群の p 冪根
有限商での根を閉集合として交差し、コンパクト性で正確な根を得る。 -/
namespace DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- 開正規部分群は副有限群の元を分離する。 -/
theorem eq_one_of_forall_mem_openNormalSubgroup [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [T2Space G]
    (y : G) (hy : ∀ N : OpenNormalSubgroup G, y ∈ N) : y = 1 := by
  by_contra hne
  have hU : IsOpen ({y}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have h1 : (1 : G) ∈ ({y}ᶜ : Set G) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hne h.symm
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact (hN (hy N)) rfl

/-- 有限商の位数と素な冪写像の全射性を、商を法とする根に戻す。 -/
theorem exists_pow_mul_inv_mem (N : OpenNormalSubgroup G) {p : ℕ}
    (hcop : (N.toSubgroup.index).Coprime p) (g : G) (k : ℕ) :
    ∃ x : G, (x ^ p ^ k)⁻¹ * g ∈ N.toSubgroup := by
  have hcard : (Nat.card (G ⧸ N.toSubgroup)).Coprime (p ^ k) := by
    rw [← Subgroup.index_eq_card]
    exact hcop.pow_right k
  obtain ⟨xbar, hxbar⟩ := (powCoprime hcard).surjective ((g : G ⧸ N.toSubgroup))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
  exact hxbar

/-- 全有限商での根と閉集合の有向交差から、群内の正確な根を得る。 -/
theorem exists_pow_pow_eq [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space G] {p : ℕ}
    (hidx : ∀ N : OpenNormalSubgroup G, (N.toSubgroup.index).Coprime p)
    (g : G) (k : ℕ) :
    ∃ w : G, w ^ p ^ k = g := by
  have : Nonempty (OpenNormalSubgroup G) :=
    ⟨⟨⟨⊤, isOpen_univ⟩, inferInstanceAs ((⊤ : Subgroup G).Normal)⟩⟩
  have hcont : Continuous fun x : G => (x ^ p ^ k)⁻¹ * g :=
    ((continuous_pow (p ^ k)).inv).mul continuous_const
  set C : OpenNormalSubgroup G → Set G :=
    fun N => (fun x : G => (x ^ p ^ k)⁻¹ * g) ⁻¹' (N.toSubgroup : Set G) with hCdef
  have hclosed : ∀ N, IsClosed (C N) := fun N =>
    (N.toOpenSubgroup.isClosed).preimage hcont
  have hne : ∀ N, (C N).Nonempty := fun N => by
    obtain ⟨x, hx⟩ := exists_pow_mul_inv_mem N (hidx N) g k
    exact ⟨x, hx⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro N M
    refine ⟨N ⊓ M, ?_, ?_⟩
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).2
  -- 全ての有限商の合同条件を同時に満たす点を選ぶ。
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun N => (hclosed N).isCompact) hclosed
  refine ⟨x, ?_⟩
  have hy : ∀ N : OpenNormalSubgroup G, (x ^ p ^ k)⁻¹ * g ∈ N :=
    fun N => Set.mem_iInter.mp hx N
  have h1 : (x ^ p ^ k)⁻¹ * g = 1 := eq_one_of_forall_mem_openNormalSubgroup _ hy
  exact (inv_mul_eq_one.mp h1)


end DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots

