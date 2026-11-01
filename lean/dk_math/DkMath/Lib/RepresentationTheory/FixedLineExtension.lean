/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.FixedCofixed
import Mathlib.LinearAlgebra.Projection

#print "file: DkMath.Lib.RepresentationTheory.FixedLineExtension"

/-!
# 固定部分加群と指標商を持つ extension の具体的な障害

`C` 上で恒等、商で `χ` として作用する同じ表現を扱う。
`ker χ` 上では `ρ(g)-1` が加法的となり、共役では逆指標で変換される。
`χ` が非自明なら、この加法指標の消滅と大域安定な補部分加群の存在は同値。
局所補部分加群からは、その局所群と `ker χ` の交わりでの消滅だけを得る。
類群・単数による大域的な消滅は、この線形代数からは結論しない。
-/

namespace DkMath.Lib.RepresentationTheory.FixedLineExtension

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (C : Submodule k V) (χ : G →* kˣ)
    (hfixed : IsFixedOn ρ C)
    (hquot : ∀ g v, ρ g v - (χ g : k) • v ∈ C)

include hfixed hquot

/-- 局所安定な補部分加群があれば、その局所群の指標核は全空間を固定する。 -/
theorem eq_one_of_complement (D : Submodule k V) (hCD : IsCompl C D)
    {g : G} (hD : ∀ x ∈ D, ρ g x ∈ D) (hg : χ g = 1) : ρ g = 1 := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ C ⊔ D := by rw [hCD.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  have hdiffC : ρ g d - d ∈ C := by simpa only [hg, Units.val_one, one_smul] using hquot g d
  have hdiffD : ρ g d - d ∈ D := D.sub_mem (hD d hd) hd
  have hdiff : ρ g d - d = 0 := by
    have hb : ρ g d - d ∈ (⊥ : Submodule k V) := hCD.inf_eq_bot ▸ ⟨hdiffC, hdiffD⟩
    simpa only [Submodule.mem_bot] using hb
  change ρ g (c + d) = c + d
  rw [map_add, hfixed g c hc, sub_eq_zero.mp hdiff]

omit hfixed hquot in
/-- 同じ指標値の群元は、指標核の作用が自明なら同じ作用を持つ。 -/
theorem representation_eq_of_character_eq
    (hker : ∀ g, χ g = 1 → ρ g = 1) {g h : G} (he : χ g = χ h) : ρ g = ρ h := by
  have hc : χ (g * h⁻¹) = 1 := by simp only [map_mul, map_inv, he, mul_inv_cancel]
  calc
    ρ g = ρ (g * h⁻¹) * ρ h := by rw [← map_mul]; simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = ρ h := by rw [hker _ hc, one_mul]

/-- 非自明な指標値の固有空間が実際の補部分加群になる。 -/
theorem isCompl_eigenKernel {t : G} (ht : (χ t : k) ≠ 1) :
    IsCompl C (LinearMap.ker (ρ t - (χ t : k) • (1 : Module.End k V))) := by
  let a : k := χ t
  let f : Module.End k V := ρ t - a • 1
  have ha : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hf (x : V) : f x ∈ C := hquot t x
  have hfc (x : V) (hx : x ∈ C) : f x = (1 - a) • x := by
    change ρ t x - a • x = (1 - a) • x
    rw [hfixed t x hx, sub_smul, one_smul]
  apply IsCompl.of_eq
  · rw [Submodule.eq_bot_iff]
    intro x hx
    have hz : (1 - a) • x = 0 := (hfc x hx.1).symm.trans hx.2
    exact (smul_eq_zero.mp hz).resolve_left ha
  · rw [Submodule.eq_top_iff']
    intro x
    let c : V := (1 - a)⁻¹ • f x
    have hc : c ∈ C := C.smul_mem _ (hf x)
    have hrest : x - c ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hfc c hc]
      dsimp [c]
      rw [smul_smul, mul_inv_cancel₀ ha, one_smul, sub_self]
    exact Submodule.mem_sup.mpr ⟨c, hc, x - c, hrest, by abel⟩

/-- 指標核が自明に作用するとき、上の同じ固有空間が全群で安定になる。 -/
theorem exists_stable_complement_of_kernel_trivial
    (hker : ∀ g, χ g = 1 → ρ g = 1) {t : G} (ht : (χ t : k) ≠ 1) :
    ∃ D : Submodule k V, IsCompl C D ∧ IsStable ρ D := by
  let D := LinearMap.ker (ρ t - (χ t : k) • (1 : Module.End k V))
  refine ⟨D, isCompl_eigenKernel ρ C χ hfixed hquot ht, ?_⟩
  intro g x hx
  have he : ρ (t * g) = ρ (g * t) := representation_eq_of_character_eq ρ χ hker
    (by rw [map_mul, map_mul, mul_comm])
  have hcomm : ρ t (ρ g x) = ρ g (ρ t x) := by
    exact congrArg (fun f : Module.End k V => f x) (by simpa only [map_mul] using he)
  have hx' : ρ t x = (χ t : k) • x := sub_eq_zero.mp hx
  change ρ t (ρ g x) - (χ t : k) • ρ g x = 0
  rw [hcomm, hx', map_smul, sub_self]

/-- 大域分裂を、指標核上の実際の作用の消滅へ正確に還元する。 -/
theorem stable_complement_iff_kernel_trivial {t : G} (ht : (χ t : k) ≠ 1) :
    (∃ D : Submodule k V, IsCompl C D ∧ IsStable ρ D) ↔
      ∀ g, χ g = 1 → ρ g = 1 := by
  constructor
  · rintro ⟨D, hCD, hD⟩ g hg
    exact eq_one_of_complement ρ C χ hfixed hquot D hCD (hD g) hg
  · intro h
    exact exists_stable_complement_of_kernel_trivial ρ C χ hfixed hquot h ht

omit hfixed in
/-- 指標核では作用差が固定部分加群に入る。 -/
theorem difference_mem (g : χ.ker) (v : V) : ρ g.val v - v ∈ C := by
  simpa only [MonoidHom.mem_ker.mp g.property, Units.val_one, one_smul] using hquot g.val v

/-- 指標核上の作用差。積を加法へ送る実際の準同型である。 -/
def deviationHom : χ.ker →* Multiplicative (Module.End k V) where
  toFun g := Multiplicative.ofAdd (ρ g.val - 1)
  map_one' := by change ρ 1 - 1 = 0; rw [map_one, sub_self]
  map_mul' g h := by
    change ρ (g.val * h.val) - 1 = (ρ g.val - 1) + (ρ h.val - 1)
    apply LinearMap.ext
    intro v
    have hf := hfixed g.val _ (difference_mem ρ C χ hquot h v)
    rw [map_sub] at hf
    change ρ (g.val * h.val) v - v = (ρ g.val v - v) + (ρ h.val v - v)
    rw [map_mul, Module.End.mul_apply]
    calc
      ρ g.val (ρ h.val v) - v = (ρ g.val (ρ h.val v) - ρ g.val v) + (ρ g.val v - v) := by abel
      _ = (ρ g.val v - v) + (ρ h.val v - v) := by rw [hf]; abel

/-- この指標の核は、元の表現核の指標核への逆像そのもの。 -/
theorem deviationHom_eq_one_iff (g : χ.ker) :
    deviationHom ρ C χ hfixed hquot g = 1 ↔ ρ g.val = 1 := by
  change ρ g.val - 1 = 0 ↔ _
  exact sub_eq_zero

/-- 共役では逆指標の重みになる。類群・Kummer の固有成分へ渡す向きを固定する。 -/
theorem deviation_conjugate (g : G) (u : χ.ker) :
    ρ (g * u.val * g⁻¹) - 1 = (χ g⁻¹ : k) • (ρ u.val - 1) := by
  apply LinearMap.ext
  intro v
  have hc := hquot g⁻¹ v
  have hfix := hfixed u.val _ hc
  rw [map_sub, map_smul] at hfix
  have hd : ρ u.val (ρ g⁻¹ v) - ρ g⁻¹ v = (χ g⁻¹ : k) • (ρ u.val v - v) := by
    rw [smul_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    have := sub_eq_sub_iff_add_eq_add.mp hfix
    simpa only [add_comm] using this
  have he := congrArg (ρ g) hd
  rw [map_sub, map_smul, ρ.self_inv_apply,
    hfixed g _ (difference_mem ρ C χ hquot u v)] at he
  change ρ (g * u.val * g⁻¹) v - v = (χ g⁻¹ : k) • (ρ u.val v - v)
  simpa only [map_mul, Module.End.mul_apply] using he

/-- 指定した同じベクトルで評価した、固定部分加群値の有限加法指標。 -/
def deviationAt (v : V) : χ.ker →* Multiplicative C where
  toFun g := Multiplicative.ofAdd ⟨ρ g.val v - v, difference_mem ρ C χ hquot g v⟩
  map_one' := by apply Subtype.ext; change ρ 1 v - v = 0; simp
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun f : Multiplicative (Module.End k V) => f.toAdd v)
      ((deviationHom ρ C χ hfixed hquot).map_mul g h)

/-- 評価された指標の消滅は、同じベクトルの実際の固定性。 -/
theorem deviationAt_eq_one_iff (v : V) (g : χ.ker) :
    deviationAt ρ C χ hfixed hquot v g = 1 ↔ ρ g.val v = v := by
  change (⟨ρ g.val v - v, _⟩ : C) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact sub_eq_zero

/-- 指標核の消滅は、この同じ固定部分加群値の指標族の消滅と同値。 -/
theorem kernel_trivial_iff_deviationAt_trivial :
    (∀ g, χ g = 1 → ρ g = 1) ↔
      ∀ v, ∀ g : χ.ker, deviationAt ρ C χ hfixed hquot v g = 1 := by
  constructor
  · intro h v g
    apply (deviationAt_eq_one_iff ρ C χ hfixed hquot v g).mpr
    rw [h g.val g.property]; rfl
  · intro h g hg
    apply LinearMap.ext
    intro v
    exact (deviationAt_eq_one_iff ρ C χ hfixed hquot v ⟨g, hg⟩).mp (h v ⟨g, hg⟩)

/-- 指定ベクトルで評価しても、共役の重みは同じ逆指標。 -/
theorem deviationAt_conjugate (v : V) (g : G) (u : χ.ker)
    (hu : χ (g * u.val * g⁻¹) = 1) :
    (deviationAt ρ C χ hfixed hquot v ⟨g * u.val * g⁻¹, hu⟩).toAdd =
      (χ g⁻¹ : k) • (deviationAt ρ C χ hfixed hquot v u).toAdd := by
  apply Subtype.ext
  exact congrArg (fun f : Module.End k V => f v) (deviation_conjugate ρ C χ hfixed hquot g u)

end DkMath.Lib.RepresentationTheory.FixedLineExtension
