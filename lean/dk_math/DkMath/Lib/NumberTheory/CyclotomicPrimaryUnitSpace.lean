/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance
import DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance
import DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace"

/-!
# 実際の局所冪の核と、同じ円分単元商の ω² 部分空間

整数環単元の p 乗商から、指定した同じ素点の完備体の Kummer 商への写像を作る。
局所 p 乗条件をその核の共通部分として定義するため、代表元に依存しない。
同じ整数環 Galois 作用の ω² 固有空間と交差を取り、未解決の消滅条件を正確に述べる。
この空間が零であること自体は仮定に残す。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace

open DkMath.Lib.Algebra KummerSelmerExact KummerSelmerUnitEquivariance
open CyclotomicKummerWeight CyclotomicKernelField CyclotomicKummerEquivariance
open IsDedekindDomain
open scoped NumberField
noncomputable section

variable {R E : Type*} [CommRing R] [Field E]

/-- 指定した環準同型を、単元冪商から実際の Kummer 商への写像に下ろす。 -/
def classMapAlong (p : ℕ) (φ : R →+* E) :
    UnitClass R p →* KummerClass E p :=
  QuotientGroup.map _ _ (Units.map φ.toMonoidHom) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨Units.map φ.toMonoidHom a,
      (map_pow _ _ _).symm⟩)

/-- 核への所属は、同じ単元の実際の局所 p 乗根の存在と同値。 -/
theorem classMapAlong_mk_eq_one_iff (p : ℕ) (φ : R →+* E) (u : Rˣ) :
    classMapAlong p φ (u : UnitClass R p) = 1 ↔
      ∃ t : Eˣ,
        (t : E) ^ p = φ (u : R) := by
  change ((Units.map φ.toMonoidHom u :
    Eˣ) : KummerClass E p) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change (∃ t : Eˣ,
    t ^ p = Units.map φ.toMonoidHom u) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h := congrArg Units.val ht
    rw [Units.val_pow_eq_pow_val] at h
    exact h
  · rintro ⟨t, ht⟩
    refine ⟨t, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact ht

variable {F : Type*} [Field F] [NumberField F]

/-- 同じ整数環の単元商から指定した完備体へ、実際の自然な写像を適用する。 -/
def localClassMap (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) :
    UnitClass (𝓞 F) p →* KummerClass (vF.adicCompletion F) p :=
  classMapAlong p (algebraMap (𝓞 F) (vF.adicCompletion F))

/-- 同じ素点への写像の核を、実際の局所根の等式として読む。 -/
theorem localClassMap_mk_eq_one_iff (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) :
    localClassMap p vF (u : UnitClass (𝓞 F) p) = 1 ↔
      ∃ t : (vF.adicCompletion F)ˣ,
        (t : vF.adicCompletion F) ^ p = algebraMap (𝓞 F) (vF.adicCompletion F) (u : 𝓞 F) :=
  classMapAlong_mk_eq_one_iff p _ u

/-- 同じ局所化写像を、既存の同じ ZMod p 加群構造で読む。 -/
def localClassLinearMap (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) :
    Additive (UnitClass (𝓞 F) p) →ₗ[ZMod p] Additive (KummerClass (vF.adicCompletion F) p) :=
  (localClassMap p vF).toAdditive.toZModLinearMap p

/-- p 上の全素点における局所 p 乗条件を満たす、実際の単元商の部分空間。 -/
def localPowerSpace (F : Type*) [Field F] [NumberField F] (p : ℕ) :
    Submodule (ZMod p) (Additive (UnitClass (𝓞 F) p)) :=
  ⨅ vF : HeightOneSpectrum (𝓞 F), ⨅ (_hpv : (p : 𝓞 F) ∈ vF.asIdeal),
    (localClassLinearMap p vF).ker

/-- 任意の代表元で、同じ局所根の条件を読む。 -/
theorem mk_mem_localPowerSpace_iff (p : ℕ) (u : (𝓞 F)ˣ) :
    Additive.ofMul (u : UnitClass (𝓞 F) p) ∈ localPowerSpace F p ↔
      ∀ vF : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ vF.asIdeal →
        ∃ t : (vF.adicCompletion F)ˣ,
          (t : vF.adicCompletion F) ^ p = algebraMap (𝓞 F) (vF.adicCompletion F) (u : 𝓞 F) := by
  simp only [localPowerSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h vF hpv
    apply (localClassMap_mk_eq_one_iff p vF u).mp
    have ht := h vF hpv
    change localClassMap p vF (u : UnitClass (𝓞 F) p) = 1 at ht
    exact ht
  · intro h vF hpv
    change localClassMap p vF (u : UnitClass (𝓞 F) p) = 1
    exact (localClassMap_mk_eq_one_iff p vF u).mpr (h vF hpv)

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance instRootNumberField : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ整数環作用と同じ円分指標に対する ω² 単元固有空間。 -/
def weightSquareSpace : Submodule (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) where
  carrier := {a | ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
    unitClassLinearMap p (integerAut γ) a = (baseCharacter hζ γ : ZMod p) ^ 2 • a}
  zero_mem' γ := by simp
  add_mem' hx hy γ := by rw [map_add, hx γ, hy γ, smul_add]
  smul_mem' c a ha γ := by rw [map_smul, ha γ, smul_comm]

/-- 今回の Frey の出力を受ける、同じ単元商上の正確な部分空間。 -/
def primaryWeightSquareSpace :
    Submodule (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  weightSquareSpace hζ ⊓ localPowerSpace (rootField ζ) p

/-- 同じ整数環単元について、固有条件と底体の各完備体での根を同時に読む。 -/
theorem mk_mem_primaryWeightSquareSpace_iff (u : (𝓞 (rootField ζ))ˣ) :
    Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ ↔
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        unitClassLinearMap p (integerAut γ) (Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 • Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p)) ∧
      ∀ vF : HeightOneSpectrum (𝓞 (rootField ζ)), (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
        ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
          (t : vF.adicCompletion (rootField ζ)) ^ p =
            algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ))
              (algebraMap (𝓞 (rootField ζ)) (rootField ζ) u) := by
  rw [primaryWeightSquareSpace, Submodule.mem_inf, mk_mem_localPowerSpace_iff]
  rfl

/-- 部分空間の消滅が供給されたとき、同じ単元類が1になる。算術的消滅自体は入力。 -/
theorem unitClass_eq_one_of_space_eq_bot
    (hunit : primaryWeightSquareSpace hζ = ⊥) (u : (𝓞 (rootField ζ))ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ) :
    (u : UnitClass (𝓞 (rootField ζ)) p) = 1 := by
  rw [hunit, Submodule.mem_bot] at hu
  exact Additive.ofMul.injective hu

/-- 未解決の空間消滅は、同じ固有・局所条件の単元が大域の単元 p 乗になるという命題と同値。
局所根から大域根への移行を定義だけで済ませず、算術的に証明すべき条件として露出させる。 -/
theorem primaryWeightSquareSpace_eq_bot_iff_global_power :
    primaryWeightSquareSpace hζ = ⊥ ↔
      ∀ u : (𝓞 (rootField ζ))ˣ,
        Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ →
        ∃ a : (𝓞 (rootField ζ))ˣ, a ^ p = u := by
  constructor
  · intro hunit u hu
    have h := unitClass_eq_one_of_space_eq_bot hζ hunit u hu
    exact (QuotientGroup.eq_one_iff u).mp h
  · intro hpower
    apply (Submodule.eq_bot_iff (primaryWeightSquareSpace hζ)).mpr
    intro x hx
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
      (powerSubgroup (𝓞 (rootField ζ))ˣ p) x.toMul
    have hxu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) = x :=
      congrArg Additive.ofMul hu
    obtain ⟨a, ha⟩ := hpower u (hxu.symm ▸ hx)
    have hclass : (u : UnitClass (𝓞 (rootField ζ)) p) = 1 :=
      (QuotientGroup.eq_one_iff u).mpr ⟨a, ha⟩
    exact hxu.symm.trans (congrArg Additive.ofMul hclass)

end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
