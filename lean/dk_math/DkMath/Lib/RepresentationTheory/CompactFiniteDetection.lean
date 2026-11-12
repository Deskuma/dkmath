/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Topology.Compactness.Compact

#print "file: DkMath.Lib.RepresentationTheory.CompactFiniteDetection"

/-! # コンパクト性による有限個の値での開条件の検出
開集合の外の各点を少なくとも一つの値で検出できれば、有限個で同時に検出できる。 -/
namespace DkMath.Lib.RepresentationTheory.CompactFiniteDetection

/-- コンパクトな空間上の開条件を、開な非一致集合の有限個で検出する。 -/
theorem exists_finite_detecting_set {G X : Type*} [TopologicalSpace G] [CompactSpace G]
    (N : Set G) (hN : IsOpen N) (act : G → X → X)
    (hopen : ∀ x, IsOpen {g | act g x ≠ x})
    (hseparate : ∀ g ∉ N, ∃ x, act g x ≠ x) :
    ∃ s : Finset X, ∀ g, (∀ x ∈ s, act g x = x) → g ∈ N := by
  classical
  have hc : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hcover : Nᶜ ⊆ ⋃ x : X, {g | act g x ≠ x} := by
    intro g hg
    obtain ⟨x, hx⟩ := hseparate g hg
    exact Set.mem_iUnion.mpr ⟨x, hx⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x => {g | act g x ≠ x}) hopen hcover
  refine ⟨s, fun g hg => ?_⟩
  by_contra hnot
  have hmem := hs hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
  obtain ⟨x, hx, hne⟩ := hmem
  exact hne (hg x hx)

end DkMath.Lib.RepresentationTheory.CompactFiniteDetection
