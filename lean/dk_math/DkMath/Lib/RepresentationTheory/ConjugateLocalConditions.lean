/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.RepresentationTheory.ConjugateLocalConditions"

/-!
# NOTE-031-004D: 局所群の共役輸送でFixed/Cofixedの側を保存する

全群で安定な同じNについて、一つの局所群Iで選んだFixedの側はgIg⁻¹でもFixed、
Cofixedの側はgIg⁻¹でもCofixedとなる。共役の都度Nや側を選び直さない。
後で付値環の共役推移性と結び、一つのp上の付値環で決めた側を全ての付値環へ運ぶ。
-/
namespace DkMath.Lib.RepresentationTheory.ConjugateLocalConditions
open LocalFixedCofixed
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- 全群で安定なNの点ごとの固定は、局所群の共役後にも同じ側で成立する。 -/
theorem fixedOn_conjugate (ρ : Representation k G V) (N : Submodule k V)
    (hN : IsStable ρ N) (I : Subgroup G) (g : G) (h : FixedOn ρ N I) :
    FixedOn ρ N (I.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨τ, hτ, rfl⟩ x hx
  change ρ (g * τ * g⁻¹) x = x
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [h τ hτ (ρ g⁻¹ x) (hN g⁻¹ x hx), ρ.self_inv_apply]

/-- 全群で安定な同じNへの変化量の吸収は、局所群の共役後にも保たれる。 -/
theorem cofixedOn_conjugate (ρ : Representation k G V) (N : Submodule k V)
    (hN : IsStable ρ N) (I : Subgroup G) (g : G) (h : CofixedOn ρ N I) :
    CofixedOn ρ N (I.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨τ, hτ, rfl⟩ x
  have hm := hN g _ (h τ hτ (ρ g⁻¹ x))
  change ρ (g * τ * g⁻¹) x - x ∈ N
  simpa only [map_sub, ρ.self_inv_apply, map_mul, Module.End.mul_apply] using hm

/-- 一つの局所群で選んだ同じ側を、その全ての共役群へ同時に輸送する。 -/
theorem common_side_on_conjugates (ρ : Representation k G V) (N : Submodule k V)
    (hN : IsStable ρ N) (I : Subgroup G) (h : FixedOn ρ N I ∨ CofixedOn ρ N I) :
    (∀ g, FixedOn ρ N (I.map (MulAut.conj g).toMonoidHom)) ∨
      (∀ g, CofixedOn ρ N (I.map (MulAut.conj g).toMonoidHom)) :=
  h.elim (fun hf => Or.inl (fun g => fixedOn_conjugate ρ N hN I g hf))
    (fun hc => Or.inr (fun g => cofixedOn_conjugate ρ N hN I g hc))

end DkMath.Lib.RepresentationTheory.ConjugateLocalConditions
