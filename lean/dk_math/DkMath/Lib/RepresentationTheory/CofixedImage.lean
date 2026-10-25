/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.FixedCofixed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

#print "file: DkMath.Lib.RepresentationTheory.CofixedImage"

/-!
# NOTE-032-005C₁: 商の固定性を同じ準同型の像へ運ぶ

[DkMath.Lib] 同変線形写像fがCofixed部分空間Lを消せば、像の各元は固定される。
さらにker(f)=Lなら、非零の像はLの外の元から来る。二次元空間の直線を核とする場合、
階数・退化次数公式が像の次元1と非零性を供給する。

これは同じfの像についての定理であり、fや幾何学的商の存在を主張しない。
核の包含だけではf=0を排除できず、安定性だけでは商の固定性も得られない。
-/
namespace DkMath.Lib.RepresentationTheory.CofixedImage
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- [DkMath.Lib] Cofixed部分空間を消す同変写像の像は点ごとに固定される。
L⊆ker(f)のみを使い、核の一致や次元条件は要求しない。 -/
theorem image_fixed (ρ : Representation k G V) (τ : Representation k G W)
    (f : V →ₗ[k] W) (L : Submodule k V) (hL : IsCofixedOn ρ L)
    (hkill : L ≤ LinearMap.ker f) (heq : ∀ g x, f (ρ g x) = τ g (f x))
    (x : V) (g : G) : τ g (f x) = f x := by
  have hz : f (ρ g x - x) = 0 := hkill (hL g x)
  rw [map_sub, heq] at hz
  exact sub_eq_zero.mp hz

/-- [DkMath.Lib] 核が同じLであれば、像の非零性は元がLの外にあることと同値。 -/
theorem image_ne_zero_iff (f : V →ₗ[k] W) (L : Submodule k V)
    (hker : LinearMap.ker f = L) (x : V) : f x ≠ 0 ↔ x ∉ L := by
  change ¬ x ∈ LinearMap.ker f ↔ _
  rw [hker]

/-- [DkMath.Lib] 正確に同じ核で割った商と、同じ写像の像の第一同型。
幾何学的な曲線の商ではなく、線形空間の商であることを型で区別する。 -/
noncomputable def quotientEquivRange (f : V →ₗ[k] W) (L : Submodule k V)
    (hker : LinearMap.ker f = L) : (V ⧸ L) ≃ₗ[k] LinearMap.range f :=
  hker ▸ f.quotKerEquivRange

/-- [DkMath.Lib] 商から像への同型は、代表元xを元の同じf(x)へ送る。 -/
theorem quotientEquivRange_apply_val (f : V →ₗ[k] W) (L : Submodule k V)
    (hker : LinearMap.ker f = L) (x : V) :
    (quotientEquivRange f L hker (L.mkQ x)).val = f x := by
  subst L
  rfl

/-- [DkMath.Lib] 同変写像の核がLと一致すれば、Cofixed条件は像の点ごとの固定と同値。
逆向きは差の像が零という事実を、同じ核へ戻す。 -/
theorem cofixed_iff_image_fixed (ρ : Representation k G V) (τ : Representation k G W)
    (f : V →ₗ[k] W) (L : Submodule k V) (hker : LinearMap.ker f = L)
    (heq : ∀ g x, f (ρ g x) = τ g (f x)) :
    IsCofixedOn ρ L ↔ ∀ x g, τ g (f x) = f x := by
  constructor
  · intro h x g
    exact image_fixed ρ τ f L h hker.ge heq x g
  · intro h g x
    rw [← hker]
    change f (ρ g x - x) = 0
    rw [map_sub, heq, h x g, sub_self]

/-- [DkMath.Lib] 二次元空間の同じ一次元核を持つ写像の像は一次元。
全射性や標的の次元は仮定せず、階数・退化次数公式から得る。 -/
theorem finrank_range [FiniteDimensional k V] (f : V →ₗ[k] W)
    (L : Submodule k V) (hd : Module.finrank k V = 2)
    (hline : Module.finrank k L = 1) (hker : LinearMap.ker f = L) :
    Module.finrank k (LinearMap.range f) = 1 := by
  have h := f.finrank_range_add_finrank_ker
  rw [hker, hline, hd] at h
  omega

/-- [DkMath.Lib] 二次元のCofixed直線を正確に核とする同変写像には非零の固定像がある。
元xとそのL外所属を保持し、単なる固定ベクトルの抽象的存在に置き換えない。 -/
theorem exists_nonzero_fixed_image [FiniteDimensional k V]
    (ρ : Representation k G V) (τ : Representation k G W) (f : V →ₗ[k] W)
    (L : Submodule k V) (hd : Module.finrank k V = 2)
    (hline : Module.finrank k L = 1) (hker : LinearMap.ker f = L)
    (hL : IsCofixedOn ρ L) (heq : ∀ g x, f (ρ g x) = τ g (f x)) :
    ∃ x : V, x ∉ L ∧ f x ≠ 0 ∧ ∀ g, τ g (f x) = f x := by
  have htop := ((proper_nonzero_iff_finrank_one hd L).mpr hline).2
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ L := by
    by_contra h
    push Not at h
    exact htop (Submodule.eq_top_iff'.mpr h)
  exact ⟨x, hx, (image_ne_zero_iff f L hker x).mpr hx,
    image_fixed ρ τ f L hL hker.ge heq x⟩

end DkMath.Lib.RepresentationTheory.CofixedImage
