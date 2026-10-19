/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import Mathlib.Algebra.Module.Submodule.Map

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionGaloisStable"

/-!
# 安定部分加群と既約性を、同変な線形同型で輸送する

部分加群Nの安定性とは、全てのガロア元がNをNへ送ることである。
既約性は「空間が非零、かつ安定部分加群は零と全体だけ」という命題として定義する。
非零条件を落とすと零表現まで既約と呼んでしまうため、明示的に保持する。

前半は任意の表現についての線形代数であり、後半で実際の楕円曲線のE[n]へ適用する。
このファイルは既約性の証明目標を固定する。Frey表現の既約性を供給する定理ではない。
-/

namespace DkMath.Lib.RepresentationTheory
variable {R G V W : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- 全ての群元の作用で閉じている部分加群。 -/
def IsStable (ρ : Representation R G V) (N : Submodule R V) : Prop :=
  ∀ g, ∀ x ∈ N, ρ g x ∈ N

/-- 非零性と、安定部分加群が零または全体であること。 -/
def IsIrreducible (ρ : Representation R G V) : Prop :=
  Nontrivial V ∧ ∀ N, IsStable ρ N → N = ⊥ ∨ N = ⊤

/-- 同変線形同型による像は、安定部分加群をちょうど安定部分加群へ写す。 -/
theorem isStable_map_iff (ρ : Representation R G V) (τ : Representation R G W)
    (e : V ≃ₗ[R] W) (he : ∀ g x, e (ρ g x) = τ g (e x)) (N : Submodule R V) :
    IsStable τ (N.map e.toLinearMap) ↔ IsStable ρ N := by
  constructor
  · intro h g x hx
    obtain ⟨y, hy, hye⟩ := h g (e x) ⟨x, hx, rfl⟩
    exact e.injective (hye.trans (he g x).symm) ▸ hy
  · intro h g _ hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨ρ g x, h g x hx, he g x⟩

/-- 同変な線形同型に沿って既約性を前向きに輸送する。 -/
theorem isIrreducible_of_equivariant (ρ : Representation R G V) (τ : Representation R G W)
    (e : V ≃ₗ[R] W) (he : ∀ g x, e (ρ g x) = τ g (e x))
    (h : IsIrreducible ρ) : IsIrreducible τ := by
  have := h.1
  refine ⟨e.injective.nontrivial, ?_⟩
  intro N hN
  let M := N.map e.symm.toLinearMap
  have hs : IsStable ρ M := (isStable_map_iff τ ρ e.symm (by
    intro g x
    apply e.injective
    simpa only [e.apply_symm_apply] using (he g (e.symm x)).symm) N).mpr hN
  have hMN : M.map e.toLinearMap = N := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change e (e.symm z) ∈ N
      rwa [e.apply_symm_apply]
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
  rcases h.2 M hs with hb | ht
  · left
    rw [hb, Submodule.map_bot] at hMN
    exact hMN.symm
  · right
    have heTop : (⊤ : Submodule R V).map e.toLinearMap = ⊤ :=
      (Submodule.orderIsoMapComap e).map_top
    rw [ht, heTop] at hMN
    exact hMN.symm

/-- 安定部分加群の順序同型から既約性を双方向に輸送する。基底も次元も不要。 -/
theorem isIrreducible_iff (ρ : Representation R G V) (τ : Representation R G W)
    (e : V ≃ₗ[R] W) (he : ∀ g x, e (ρ g x) = τ g (e x)) :
    IsIrreducible ρ ↔ IsIrreducible τ := by
  refine ⟨isIrreducible_of_equivariant ρ τ e he,
    isIrreducible_of_equivariant τ ρ e.symm ?_⟩
  intro g x
  apply e.injective
  simpa only [e.apply_symm_apply] using (he g (e.symm x)).symm

end DkMath.Lib.RepresentationTheory

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (n : ℕ)

/-- 実際のE[n]のガロア安定部分加群という条件。 -/
def IsGaloisStable (N : Submodule (ZMod n) (Torsion E n)) : Prop :=
  DkMath.Lib.RepresentationTheory.IsStable (representation E n) N

/-- 実際のE[n]の既約性という証明目標。 -/
def IsIrreducible : Prop :=
  DkMath.Lib.RepresentationTheory.IsIrreducible (representation E n)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
