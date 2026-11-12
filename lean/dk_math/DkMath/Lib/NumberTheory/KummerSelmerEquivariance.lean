/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmerExact
import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# 同じイデアル根による Selmer 類群写像の同変性

整域とその分数体の自己同型が埋め込みと両立するとき、主イデアル `(x)` は `(σ x)` に移る。
`J^p=(x)` を移して得た根は、正の指数での根の一意性から実際に `J_{σx}=σJ_x`
である。この等式を商へ下ろす。Selmer 所属を自動的に供給する算術的定理ではない。
-/

namespace DkMath.Lib.NumberTheory.KummerSelmerEquivariance

open CyclotomicKummerWeight KummerSelmer KummerSelmerClassMap IsDedekindDomain
open DkMath.Lib.Algebra
open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

/-- 整数側と分数体側の自己同型、および実際の埋め込みとの可換性。 -/
structure CompatibleAut (R F : Type*) [CommRing R] [Field F] [Algebra R F] where
  integers : R ≃+* R
  field : F ≃+* F
  commutes : ∀ r : R, field (algebraMap R F r) = algebraMap R F (integers r)

namespace CompatibleAut

/-- 埋め込みを保つ恒等自己同型。 -/
def refl : CompatibleAut R F where
  integers := RingEquiv.refl R
  field := RingEquiv.refl F
  commutes _ := rfl

/-- `σ` の後に `τ` を施す合成。 -/
def trans (σ τ : CompatibleAut R F) : CompatibleAut R F where
  integers := σ.integers.trans τ.integers
  field := σ.field.trans τ.field
  commutes r := by
    change τ.field (σ.field (algebraMap R F r)) = _
    rw [σ.commutes, τ.commutes]
    rfl

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[ext] theorem ext (σ τ : CompatibleAut R F)
    (hi : σ.integers = τ.integers) (hf : σ.field = τ.field) : σ = τ := by
  cases σ
  cases τ
  cases hi
  cases hf
  rfl

/-- 可換性を保つ逆自己同型。 -/
def symm (σ : CompatibleAut R F) : CompatibleAut R F where
  integers := σ.integers.symm
  field := σ.field.symm
  commutes r := by
    apply σ.field.injective
    rw [RingEquiv.apply_symm_apply, σ.commutes, RingEquiv.apply_symm_apply]

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem trans_symm (σ : CompatibleAut R F) : σ.trans σ.symm = refl := by
  have hi : (σ.trans σ.symm).integers = (refl (R := R) (F := F)).integers := by
    ext r
    exact σ.integers.symm_apply_apply r
  have hf : (σ.trans σ.symm).field = (refl (R := R) (F := F)).field := by
    ext x
    exact σ.field.symm_apply_apply x
  exact CompatibleAut.ext _ _ hi hf

variable (σ : CompatibleAut R F)

omit [IsFractionRing R F] in
private theorem preserves_denominators : R⁰ ≤ Submonoid.comap σ.integers.toRingHom R⁰ := by
  intro r hr
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (σ.integers.injective.ne (mem_nonZeroDivisors_iff_ne_zero.mp hr) |>.trans_eq (map_zero _))

/-- 同じ分数体内でイデアルを自己同型に沿って移す、実際の環準同型。 -/
def idealMap : FractionalIdeal R⁰ F →+* FractionalIdeal R⁰ F :=
  FractionalIdeal.extendedHom' F σ.preserves_denominators

theorem idealMap_refl (J : FractionalIdeal R⁰ F) :
    (refl (R := R) (F := F)).idealMap J = J := by
  have hf : IsLocalization.map F (refl (R := R) (F := F)).integers.toRingHom
      (refl (R := R) (F := F)).preserves_denominators = RingHom.id F :=
    IsLocalization.map_unique _ _ (fun _ => rfl)
  ext x
  change x ∈ J.extended F (refl (R := R) (F := F)).preserves_denominators ↔ x ∈ J
  rw [FractionalIdeal.mem_extended_iff]
  change x ∈ Submodule.span R
    (IsLocalization.map F (refl (R := R) (F := F)).integers.toRingHom
      (refl (R := R) (F := F)).preserves_denominators '' (J : Set F)) ↔ x ∈ J
  rw [hf]
  change x ∈ Submodule.span R ((id : F → F) '' (J : Set F)) ↔ x ∈ J
  rw [Set.image_id]
  change x ∈ Submodule.span R (J.val : Set F) ↔ x ∈ J.val
  rw [Submodule.span_eq]

theorem idealMap_trans (τ : CompatibleAut R F) (J : FractionalIdeal R⁰ F) :
    (σ.trans τ).idealMap J = τ.idealMap (σ.idealMap J) := by
  change J.extended F _ = (J.extended F σ.preserves_denominators).extended F τ.preserves_denominators
  rw [FractionalIdeal.extended_extended]

theorem idealMap_span (x : F) :
    σ.idealMap (FractionalIdeal.spanSingleton R⁰ x) =
      FractionalIdeal.spanSingleton R⁰ (σ.field x) := by
  have hf : IsLocalization.map F σ.integers.toRingHom σ.preserves_denominators =
      σ.field.toRingHom := IsLocalization.map_unique _ _ σ.commutes
  change (FractionalIdeal.spanSingleton R⁰ x).extended F _ = _
  rw [FractionalIdeal.extended_spanSingleton, hf]
  rfl

/-- 非零分数イデアルを同じ写像で移す。 -/
def idealUnitsMap : (FractionalIdeal R⁰ F)ˣ →* (FractionalIdeal R⁰ F)ˣ :=
  Units.map σ.idealMap.toMonoidHom

theorem idealUnitsMap_principal (x : Fˣ) :
    σ.idealUnitsMap (toPrincipalIdeal R F x) =
      toPrincipalIdeal R F (Units.map σ.field.toMonoidHom x) := by
  apply Units.ext
  change σ.idealMap (toPrincipalIdeal R F x).val = _
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, idealMap_span]
  rfl

/-- 主イデアルを保つ実際のイデアル写像を、実際の類群へ下ろす。 -/
def classGroupMap : ClassGroup R →* ClassGroup R :=
  (QuotientGroup.lift (toPrincipalIdeal R F).range
    ((ClassGroup.mk F).comp σ.idealUnitsMap) (by
      rintro _ ⟨x, rfl⟩
      change ClassGroup.mk F (σ.idealUnitsMap (toPrincipalIdeal R F x)) = 1
      rw [idealUnitsMap_principal, principal_class_eq_one])).comp
    (ClassGroup.equiv F).toMonoidHom

theorem classGroupMap_mk (J : (FractionalIdeal R⁰ F)ˣ) :
    σ.classGroupMap (ClassGroup.mk F J) = ClassGroup.mk F (σ.idealUnitsMap J) := by
  simp only [classGroupMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl]
  rfl

theorem classGroupMap_refl (z : ClassGroup R) :
    (refl (R := R) (F := F)).classGroupMap z = z := by
  refine ClassGroup.induction F (fun J => ?_) z
  rw [classGroupMap_mk]
  congr 1
  apply Units.ext
  exact idealMap_refl J.val

theorem classGroupMap_trans (τ : CompatibleAut R F) (z : ClassGroup R) :
    (σ.trans τ).classGroupMap z = τ.classGroupMap (σ.classGroupMap z) := by
  refine ClassGroup.induction F (fun J => ?_) z
  rw [classGroupMap_mk, classGroupMap_mk, classGroupMap_mk]
  congr 1
  apply Units.ext
  exact σ.idealMap_trans τ J.val

/-- 類群上の写像は、実際に逆写像を持つ自己同型である。 -/
def classGroupEquiv : ClassGroup R ≃* ClassGroup R :=
  { σ.classGroupMap with
    invFun := σ.symm.classGroupMap
    left_inv := fun z => by
      change σ.symm.classGroupMap (σ.classGroupMap z) = z
      rw [← classGroupMap_trans, trans_symm, classGroupMap_refl]
    right_inv := fun z => by
      have ht : σ.symm.trans σ = refl := by
        exact CompatibleAut.ext _ _ (by ext r; exact σ.integers.apply_symm_apply r)
          (by ext x; exact σ.field.apply_symm_apply x)
      change σ.classGroupMap (σ.symm.classGroupMap z) = z
      rw [← classGroupMap_trans, ht, classGroupMap_refl] }

/-- 同じ代表元の Selmer 条件を、同じ主イデアルの冪根を移して保つ。 -/
theorem map_mem {p : ℕ} (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    Additive.ofMul ((Units.map σ.field.toMonoidHom x : Fˣ) : KummerClass F p) ∈
      valuationSpace (R := R) p := by
  apply (mem_valuationSpace_mk_iff p _).mpr
  intro v
  apply count_dvd_of_eq_pow p (J := (σ.idealUnitsMap (rootIdeal p x hx)).val)
  have he := congrArg (fun J => (σ.idealUnitsMap J).val) (rootIdeal_pow p x hx)
  simpa only [map_pow, idealUnitsMap_principal, Units.val_pow_eq_pow_val,
    coe_toPrincipalIdeal] using he.symm

/-- 移した根は、移した代表元から選んだ根と実際に等しい。 -/
theorem rootIdeal_map {p : ℕ} (hp : 0 < p) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    rootIdeal p (Units.map σ.field.toMonoidHom x) (σ.map_mem x hx) =
      σ.idealUnitsMap (rootIdeal p x hx) := by
  apply idealUnits_pow_injective hp
  dsimp only
  rw [rootIdeal_pow, ← map_pow, rootIdeal_pow, idealUnitsMap_principal]

/-- 実際の Selmer 部分群上の写像。所属の保存を別の provider にしない。 -/
def selmerMap (p : ℕ) : Selmer R F p →* Selmer R F p :=
  (classMap p σ.field.toRingHom).restrict (by
    intro z hz
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z
    change (x : KummerClass F p) = z at hx
    have hv := (mem_valuationSpace_iff_selmer p z).mpr hz
    rw [← hx] at hv
    change classMap p σ.field.toRingHom z ∈ Selmer R F p
    rw [← hx, classMap_mk]
    exact (mem_valuationSpace_iff_selmer p _).mp (σ.map_mem x hv))

/-- 商を取っても、元の同じ Selmer 類の類群像は自己同型と可換。 -/
theorem toClassGroup_equivariant (p : ℕ) (hp : 0 < p) (z : Selmer R F p) :
    toClassGroup p hp (σ.selmerMap p z) = σ.classGroupMap (toClassGroup p hp z) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val
  change (x : KummerClass F p) = z.val at hx
  have hval := (mem_valuationSpace_iff_selmer p z.val).mpr z.property
  rw [← hx] at hval
  have he : ((Units.map σ.field.toMonoidHom x : Fˣ) : KummerClass F p) =
      (σ.selmerMap p z).val := by
    change _ = classMap p σ.field.toRingHom z.val
    rw [← hx, classMap_mk]
    rfl
  change classMapValue p _ = σ.classGroupMap (classMapValue p z)
  rw [classMapValue_eq hp _ _ (σ.map_mem x hval) he,
    classMapValue_eq hp z x hval hx, classGroupMap_mk, rootIdeal_map σ hp]

/-- 類群の同じ `p` 捩れ部分群にも実際の写像を制限する。 -/
def classTorsionMap (p : ℕ) : ClassTorsion R p →* ClassTorsion R p :=
  σ.classGroupMap.restrict (by
    intro z hz
    change σ.classGroupMap z ^ p = 1
    rw [← map_pow, show z ^ p = 1 from hz, map_one])

theorem toClassTorsion_equivariant (p : ℕ) (hp : 0 < p) (z : Selmer R F p) :
    toClassTorsion p hp (σ.selmerMap p z) =
      σ.classTorsionMap p (toClassTorsion p hp z) := by
  apply Subtype.ext
  exact σ.toClassGroup_equivariant p hp z

/-- 実際の類群作用の `ZMod p` 線形化。 -/
def classTorsionLinearMap (p : ℕ) :
    Additive (ClassTorsion R p) →ₗ[ZMod p] Additive (ClassTorsion R p) :=
  (σ.classTorsionMap p).toAdditive.toZModLinearMap p

theorem classTorsionLinearMap_refl (p : ℕ) (w : Additive (ClassTorsion R p)) :
    (refl (R := R) (F := F)).classTorsionLinearMap p w = w := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact classGroupMap_refl w.toMul.val

theorem classTorsionLinearMap_trans (τ : CompatibleAut R F) (p : ℕ)
    (w : Additive (ClassTorsion R p)) :
    (σ.trans τ).classTorsionLinearMap p w =
      τ.classTorsionLinearMap p (σ.classTorsionLinearMap p w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact σ.classGroupMap_trans τ w.toMul.val

/-- 元の類の固有条件を、同変性を用いて同じ類群像へ移す。像は零でもよい。 -/
theorem classImage_weight {p : ℕ} (hp : 0 < p) (z : Selmer R F p) (a : ZMod p)
    (he : classMap p σ.field.toRingHom z.val = z.val ^ a.val) :
    σ.classTorsionLinearMap p (Additive.ofMul (toClassTorsion p hp z)) =
      a • Additive.ofMul (toClassTorsion p hp z) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hs : σ.selmerMap p z = z ^ a.val := Subtype.ext he
  have hw : σ.classTorsionMap p (toClassTorsion p hp z) =
      toClassTorsion p hp z ^ a.val := by
    rw [← toClassTorsion_equivariant, hs, map_pow]
  apply Additive.toMul.injective
  rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, toMul_nsmul]
  change σ.classTorsionMap p (toClassTorsion p hp z) = toClassTorsion p hp z ^ a.val
  exact hw

end CompatibleAut
end
end DkMath.Lib.NumberTheory.KummerSelmerEquivariance
