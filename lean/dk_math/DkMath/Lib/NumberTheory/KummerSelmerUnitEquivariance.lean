/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmerEquivariance

/-!
# 単元冪商、同変な短完全列、同じ単元類への固有条件の移送

整数側の自己同型から実際の単元冪商の自己同型を構成する。
同じ `unitInclusion` との同変性を、整数環から分数体への可換性で証明する。
単射性により、元の Selmer 類の固有条件をその同じ単元逆像へ戻す。
Selmer 所属や類群・単元の算術的消滅は供給しない。
-/

namespace DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance

open CyclotomicKummerWeight KummerSelmerClassMap KummerSelmerExact KummerSelmerEquivariance
open DkMath.Lib.Algebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

/-- 同じ整数環の実際の自己同型を、その単元冪商へ下ろす。 -/
def unitClassMap (p : ℕ) (σ : CompatibleAut R F) : UnitClass R p →* UnitClass R p :=
  QuotientGroup.map _ _ (Units.map σ.integers.toMonoidHom) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map σ.integers.toMonoidHom u, (map_pow _ _ _).symm⟩)

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem unitClassMap_mk (p : ℕ) (σ : CompatibleAut R F) (u : Rˣ) :
    unitClassMap p σ (u : UnitClass R p) =
      ((Units.map σ.integers.toMonoidHom u : Rˣ) : UnitClass R p) := rfl

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem unitClassMap_refl (p : ℕ) (u : UnitClass R p) :
    unitClassMap p (CompatibleAut.refl (F := F)) u = u := by
  refine Quotient.inductionOn u (fun v => ?_)
  rw [unitClassMap_mk]
  congr 1

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem unitClassMap_trans (p : ℕ) (σ τ : CompatibleAut R F) (u : UnitClass R p) :
    unitClassMap p (σ.trans τ) u = unitClassMap p τ (unitClassMap p σ u) := by
  refine Quotient.inductionOn u (fun v => ?_)
  rw [unitClassMap_mk, unitClassMap_mk, unitClassMap_mk]
  congr 1

omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem symm_trans (σ : CompatibleAut R F) : σ.symm.trans σ = CompatibleAut.refl :=
  CompatibleAut.ext _ _ (by ext r; exact σ.integers.apply_symm_apply r)
    (by ext x; exact σ.field.apply_symm_apply x)

/-- 同じ単元冪商の実際の自己同型。逆写像も整数側の逆自己同型から作る。 -/
def unitClassEquiv (p : ℕ) (σ : CompatibleAut R F) : UnitClass R p ≃* UnitClass R p :=
  { unitClassMap p σ with
    invFun := unitClassMap p σ.symm
    left_inv := fun u => by
      change unitClassMap p σ.symm (unitClassMap p σ u) = u
      rw [← unitClassMap_trans, CompatibleAut.trans_symm, unitClassMap_refl]
    right_inv := fun u => by
      change unitClassMap p σ (unitClassMap p σ.symm u) = u
      rw [← unitClassMap_trans, symm_trans, unitClassMap_refl] }

theorem selmerMap_refl (p : ℕ) (z : Selmer R F p) :
    (CompatibleAut.refl (R := R) (F := F)).selmerMap p z = z := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val
  change (x : KummerClass F p) = z.val at hx
  change classMap p (CompatibleAut.refl (R := R) (F := F)).field.toRingHom z.val = z.val
  rw [← hx, classMap_mk]
  rfl

theorem selmerMap_trans (p : ℕ) (σ τ : CompatibleAut R F) (z : Selmer R F p) :
    (σ.trans τ).selmerMap p z = τ.selmerMap p (σ.selmerMap p z) := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val
  change (x : KummerClass F p) = z.val at hx
  change classMap p (σ.trans τ).field.toRingHom z.val =
    classMap p τ.field.toRingHom (classMap p σ.field.toRingHom z.val)
  rw [← hx, classMap_mk, classMap_mk]
  change ((Units.map (σ.trans τ).field.toMonoidHom x : Fˣ) : KummerClass F p) =
    classMap p τ.field.toRingHom ((Units.map σ.field.toMonoidHom x : Fˣ) : KummerClass F p)
  rw [classMap_mk]
  rfl

/-- 類群捩れ上の作用にも同じ逆自己同型を制限する。 -/
def classTorsionEquiv (p : ℕ) (σ : CompatibleAut R F) : ClassTorsion R p ≃* ClassTorsion R p :=
  { σ.classTorsionMap p with
    invFun := σ.symm.classTorsionMap p
    left_inv := fun z => Subtype.ext (σ.classGroupEquiv.left_inv z.val)
    right_inv := fun z => Subtype.ext (σ.classGroupEquiv.right_inv z.val) }

/-- 同じ Selmer 群にも逆写像を備えた実際の自己同型を与える。 -/
def selmerEquiv (p : ℕ) (σ : CompatibleAut R F) : Selmer R F p ≃* Selmer R F p :=
  { σ.selmerMap p with
    invFun := σ.symm.selmerMap p
    left_inv := fun z => by
      change σ.symm.selmerMap p (σ.selmerMap p z) = z
      rw [← selmerMap_trans, CompatibleAut.trans_symm, selmerMap_refl]
    right_inv := fun z => by
      change σ.selmerMap p (σ.symm.selmerMap p z) = z
      rw [← selmerMap_trans, symm_trans, selmerMap_refl] }

/-- 同じ単元埋め込みと Selmer 側の作用は、実際の整数環埋め込みの可換性から両立する。 -/
theorem unitInclusion_equivariant (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (u : UnitClass R p) :
    σ.selmerMap p (unitInclusion p hp u) = unitInclusion p hp (unitClassMap p σ u) := by
  refine Quotient.inductionOn u (fun v => ?_)
  rw [unitClassMap_mk, unitInclusion_mk, unitInclusion_mk]
  apply Subtype.ext
  change classMap p σ.field.toRingHom
      ((Units.map (algebraMap R F).toMonoidHom v : Fˣ) : KummerClass F p) =
    ((Units.map (algebraMap R F).toMonoidHom (Units.map σ.integers.toMonoidHom v) : Fˣ) :
      KummerClass F p)
  rw [classMap_mk]
  have hc : Units.map σ.field.toMonoidHom (Units.map (algebraMap R F).toMonoidHom v) =
      Units.map (algebraMap R F).toMonoidHom (Units.map σ.integers.toMonoidHom v) :=
    Units.ext (σ.commutes v.val)
  exact congrArg (fun x : Fˣ => (x : KummerClass F p)) hc

/-- 既存の短完全列と、その同じ二つの写像の同変性。消滅を仮定しない。 -/
theorem short_exact_equivariant (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F) :
    (Function.Injective (unitInclusion (R := R) (F := F) p hp) ∧
      (toClassTorsion (R := R) (F := F) p hp).ker = (unitInclusion p hp).range ∧
      Function.Surjective (toClassTorsion (R := R) (F := F) p hp)) ∧
    (∀ u : UnitClass R p,
      σ.selmerMap p (unitInclusion p hp u) = unitInclusion p hp (unitClassMap p σ u)) ∧
    (∀ z : Selmer R F p,
      toClassTorsion p hp (σ.selmerMap p z) = σ.classTorsionMap p (toClassTorsion p hp z)) :=
  ⟨short_exact p hp, unitInclusion_equivariant p hp σ, σ.toClassTorsion_equivariant p hp⟩

/-- 類群像が零である同じ Selmer 類の単元逆像は、存在するだけでなく一意である。 -/
theorem existsUnique_unitClass (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassTorsion p hp z = 1) :
    ∃! u : UnitClass R p, unitInclusion p hp u = z := by
  have hr : z ∈ (unitInclusion (R := R) (F := F) p hp).range := by
    rw [← kernel_eq_unit_range]
    exact hzero
  obtain ⟨u, hu⟩ := hr
  exact ⟨u, hu, fun v hv => unitInclusion_injective p hp (hv.trans hu.symm)⟩

/-- 同じ Selmer 類の一意な単元逆像。実際の単元の代表元を選び直しても、この類は変わらない。 -/
def unitPreimage (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassTorsion p hp z = 1) : UnitClass R p :=
  (existsUnique_unitClass p hp z hzero).choose

theorem unitPreimage_spec (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassTorsion p hp z = 1) :
    unitInclusion p hp (unitPreimage p hp z hzero) = z :=
  (existsUnique_unitClass p hp z hzero).choose_spec.1

theorem unitPreimage_eq (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassTorsion p hp z = 1) (u : UnitClass R p)
    (hu : unitInclusion p hp u = z) : unitPreimage p hp z hzero = u :=
  unitInclusion_injective p hp ((unitPreimage_spec p hp z hzero).trans hu.symm)

theorem unitPreimage_ne_one (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassTorsion p hp z = 1) (hne : z ≠ 1) : unitPreimage p hp z hzero ≠ 1 := by
  intro h
  apply hne
  rw [← unitPreimage_spec p hp z hzero, h, map_one]

theorem selmerMap_class_eq_one (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (z : Selmer R F p) (hzero : toClassTorsion p hp z = 1) :
    toClassTorsion p hp (σ.selmerMap p z) = 1 := by
  rw [CompatibleAut.toClassTorsion_equivariant, hzero, map_one]

/-- 一意な同じ単元逆像は、選択の取り直しを含めても自己同型と可換。 -/
theorem unitPreimage_equivariant (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (z : Selmer R F p) (hzero : toClassTorsion p hp z = 1) :
    unitPreimage p hp (σ.selmerMap p z) (selmerMap_class_eq_one p hp σ z hzero) =
      unitClassMap p σ (unitPreimage p hp z hzero) := by
  apply unitPreimage_eq
  rw [← unitInclusion_equivariant, unitPreimage_spec]

/-- 元の Selmer 類を表す同じ単元逆像は、単射性によって同じ冪の固有条件を満たす。 -/
theorem unitClass_weight (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (z : Selmer R F p) (u : UnitClass R p) (hu : unitInclusion p hp u = z)
    (r : ℕ) (he : classMap p σ.field.toRingHom z.val = z.val ^ r) :
    unitClassMap p σ u = u ^ r := by
  apply unitInclusion_injective (R := R) (F := F) p hp
  rw [← unitInclusion_equivariant, map_pow, hu]
  exact Subtype.ext he

omit [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F] in
theorem unitClass_pow (p : ℕ) (u : UnitClass R p) : u ^ p = 1 := by
  refine Quotient.inductionOn u (fun v => ?_)
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨v, rfl⟩

/-- 単元冪商の同じ加法群を `ZMod p` 加群として読む。 -/
instance unitClassModule (R : Type*) [CommRing R] (p : ℕ) :
    Module (ZMod p) (Additive (UnitClass R p)) :=
  AddCommGroup.zmodModule (by
    intro u
    apply Additive.toMul.injective
    exact unitClass_pow p u.toMul)

/-- 同じ単元自己同型を `ZMod p` 線形写像として読む。 -/
def unitClassLinearMap (p : ℕ) (σ : CompatibleAut R F) :
    Additive (UnitClass R p) →ₗ[ZMod p] Additive (UnitClass R p) :=
  (unitClassMap p σ).toAdditive.toZModLinearMap p

theorem unitClassLinearMap_weight (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (z : Selmer R F p) (u : UnitClass R p) (hu : unitInclusion p hp u = z)
    (a : ZMod p) (he : classMap p σ.field.toRingHom z.val = z.val ^ a.val) :
    unitClassLinearMap p σ (Additive.ofMul u) = a • Additive.ofMul u := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hw := unitClass_weight p hp σ z u hu a.val he
  apply Additive.toMul.injective
  rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, toMul_nsmul]
  change unitClassMap p σ u = u ^ a.val
  exact hw

end
end DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance
