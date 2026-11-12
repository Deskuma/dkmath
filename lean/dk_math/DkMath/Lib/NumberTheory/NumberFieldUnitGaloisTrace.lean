/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use the SAME DkMath integerAut, UnitClass, unitProjection and proved
Dirichlet basis; no external ModP or trace theorem is imported.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
import Mathlib.LinearAlgebra.Trace

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace"

/-!
# 同じ単元作用の捩れ成分と自由成分のトレース

整数環自己同型は既存の integerAut。捩れ群の安定性を証明して自由商へ作用を降ろす。
実際の UnitClass の捩れ・基本単元基底の対角成分を計算し、mod p の trace を
捩れ成分 n と整数上の自由商作用の trace の和として証明する。
基本単元が Galois 不変とは仮定しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace

open NumberField NumberField.Units NumberFieldUnitPowerDimension
open CyclotomicKummerEquivariance KummerSelmerUnitEquivariance KummerSelmerExact
open scoped NumberField
noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F]

/-- Mathlib の Dirichlet 自由商を同じ群構造で明示する。 -/
instance freeUnitsCommGroup : CommGroup ((𝓞 F)ˣ ⧸ torsion F) :=
  QuotientGroup.Quotient.commGroup _
instance freeUnitsAddCommGroup : AddCommGroup (Additive ((𝓞 F)ˣ ⧸ torsion F)) :=
  Additive.addCommGroup
instance freeUnitsIntModule : Module ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) :=
  AddCommGroup.toIntModule _

/-- 同じ整数環への実際の制限が与える単元群の作用。 -/
def unitsMap (σ : F ≃ₐ[ℚ] F) : (𝓞 F)ˣ →* (𝓞 F)ˣ :=
  Units.map (integerAut σ).integers.toMonoidHom

/-- 指定した元の数体自己同型と可換する。 -/
theorem unitsMap_coe (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    ((unitsMap F σ u : 𝓞 F) : F) = σ ((u : 𝓞 F) : F) := rfl

/-- 有限位数の単元は同じ整数環作用で有限位数に保たれる。 -/
lemma unitsMap_torsion_le (σ : F ≃ₐ[ℚ] F) :
    torsion F ≤ (torsion F).comap (unitsMap F σ) := by
  intro t ht
  rw [Subgroup.mem_comap]
  rw [torsion, CommGroup.mem_torsion] at ht ⊢
  exact MonoidHom.isOfFinOrder _ ht

/-- 実際の有限捩れ群による同じ自由商への作用。 -/
def quotMap (σ : F ≃ₐ[ℚ] F) : Additive ((𝓞 F)ˣ ⧸ torsion F) →+ Additive ((𝓞 F)ˣ ⧸ torsion F) :=
  MonoidHom.toAdditive
    (QuotientGroup.map (torsion F) (torsion F) (unitsMap F σ) (unitsMap_torsion_le F σ))

lemma quotMap_mk (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    quotMap F σ (Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F))) =
      Additive.ofMul (QuotientGroup.mk (unitsMap F σ u)) := rfl

set_option backward.isDefEq.respectTransparency false in

/-- 同じ自由商の加法作用を整数線形写像として読む。 -/
def quotMapLin (σ : F ≃ₐ[ℚ] F) : Additive ((𝓞 F)ˣ ⧸ torsion F) →ₗ[ℤ] Additive ((𝓞 F)ˣ ⧸ torsion F) :=
  (quotMap F σ).toIntLinearMap

lemma quotMapLin_apply (σ : F ≃ₐ[ℚ] F) (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    quotMapLin F σ x = quotMap F σ x := rfl


/-- 同じ単元上の実際の自己同型の合成則。 -/
theorem unitsMap_mul (σ τ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    unitsMap F (σ * τ) u = unitsMap F σ (unitsMap F τ u) := by
  apply Units.ext
  apply NumberField.RingOfIntegers.coe_injective
  rfl

/-- 捩れを除いた同じ自由商上にも、実際の Galois 群作用を与える。 -/
def freeUnitAction : (F ≃ₐ[ℚ] F) →*
    Module.End ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) where
  toFun σ := quotMapLin F σ
  map_one' := by
    ext x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (torsion F) x.toMul
    have he : Additive.ofMul ((QuotientGroup.mk' (torsion F)) u) = x := congrArg Additive.ofMul hu
    rw [← he]
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (torsion F) x.toMul
    have he : Additive.ofMul ((QuotientGroup.mk' (torsion F)) u) = x := congrArg Additive.ofMul hu
    rw [← he]
    change Additive.ofMul (QuotientGroup.mk (unitsMap F (σ * τ) u)) =
      Additive.ofMul (QuotientGroup.mk (unitsMap F σ (unitsMap F τ u)))
    rw [unitsMap_mul]


/-- 既存 unitClassLinearMap そのものによる同じ単元 p 乗商上の作用。 -/
def vMap (σ : F ≃ₐ[ℚ] F) :
    Additive (UnitClass (𝓞 F) p) →ₗ[ZMod p] Additive (UnitClass (𝓞 F) p) :=
  unitClassLinearMap p (integerAut σ)

theorem vMap_proj (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    vMap p F σ (unitProjection (F := F) p (Additive.ofMul u)) =
      unitProjection (F := F) p (Additive.ofMul (unitsMap F σ u)) := rfl

/-- 実際の捩れ成分 n と自由商の整数 trace を足した、同じ作用の trace。 -/
theorem trace_vMap (hdiv : p ∣ torsionOrder F) (σ : F ≃ₐ[ℚ] F) (n : ℕ)
    (hσ : ∀ x : 𝓞 F, x ^ p = 1 → (integerAut σ).integers x = x ^ n) :
    LinearMap.trace (ZMod p) _ (vMap p F σ) =
      (n : ZMod p) + ((LinearMap.trace ℤ _ (quotMapLin F σ) : ℤ) : ZMod p) := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion F)
  have hord : orderOf t = torsionOrder F := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  obtain ⟨b, hb_none, hb_some⟩ := exists_unitClass_basis (p := p) F hdiv t ht
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp
    (ht ⟨unitsMap F σ (t : (𝓞 F)ˣ), unitsMap_torsion_le F σ t.2⟩)
  have he' : unitsMap F σ (t : (𝓞 F)ˣ) = (t : (𝓞 F)ˣ) ^ e := by
    have := congrArg (fun x : torsion F => (x : (𝓞 F)ˣ)) he
    simpa only [Subgroup.coe_zpow] using this.symm
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp [torsionOrder_ne_zero F] at hq)
  have he_n : (e : ZMod p) = (n : ZMod p) := by
    -- 全捩れ生成元の適切な冪が位数 p の元を与え、その作用が e≡n を強制する。
    set y : (𝓞 F)ˣ := (t : (𝓞 F)ˣ) ^ q with hy
    have hyp : (y : 𝓞 F) ^ p = 1 := by
      rw [hy, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hq, ← hord,
        ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have h1 : unitsMap F σ y = y ^ n := by
      ext
      rw [Units.val_pow_eq_pow_val, ← hσ _ hyp]
      rfl
    have h2 : unitsMap F σ y = (t : (𝓞 F)ˣ) ^ ((q : ℤ) * e) := by
      rw [hy, map_pow, he', ← zpow_natCast, ← zpow_mul, mul_comm]
    have h3 : (t : (𝓞 F)ˣ) ^ ((q : ℤ) * e) = (t : (𝓞 F)ˣ) ^ ((q : ℤ) * n) := by
      rw [← h2, h1, hy, ← pow_mul, ← zpow_natCast, Nat.cast_mul]
    rw [zpow_eq_zpow_iff_modEq, Subgroup.orderOf_coe, hord, hq, Nat.cast_mul,
      mul_comm (p : ℤ) (q : ℤ)] at h3
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hmod : e ≡ (n : ℤ) [ZMOD (p : ℤ)] := Int.ModEq.mul_left_cancel' hq0 h3
    rw [← Int.cast_natCast n]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  have row_none : b.repr (vMap p F σ (b none)) none = n := by
    rw [hb_none, vMap_proj, he', ofMul_zpow, map_zsmul, ← hb_none,
      ← Int.cast_smul_eq_zsmul (ZMod p), map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, he_n]
  -- 基本単元が作用で不変でなくても、商作用の整数行列と対角係数が一致する。
  have row_some : ∀ i, b.repr (vMap p F σ (b (some i))) (some i) =
      (((basisModTorsion F).repr (quotMapLin F σ (basisModTorsion F i)) i : ℤ) : ZMod p) := by
    intro i
    set w : (𝓞 F)ˣ := unitsMap F σ (fundSystem F i) with hw_def
    obtain ⟨⟨ζw, ew⟩, hw, -⟩ := exist_unique_eq_mul_prod F w
    dsimp only at hw
    have hrepr : ew = (basisModTorsion F).repr (quotMapLin F σ (basisModTorsion F i)) := by
      rw [fun_eq_repr F ζw.2 hw, quotMapLin_apply, ← fundSystem_mk, quotMap_mk]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζw)
    have hζw : (ζw : (𝓞 F)ˣ) = (t : (𝓞 F)ˣ) ^ m := by
      rw [← hm, Subgroup.coe_zpow]
    have hvw : vMap p F σ (b (some i)) =
        (m : ZMod p) • b none + ∑ j, ((ew j : ℤ) : ZMod p) • b (some j) := by
      rw [hb_some, vMap_proj, ← hw_def, hw, hζw, ofMul_mul, ofMul_zpow, ofMul_prod, map_add,
        map_zsmul, map_sum, hb_none, Int.cast_smul_eq_zsmul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ofMul_zpow, map_zsmul, hb_some, Int.cast_smul_eq_zsmul]
    rw [hvw, map_add, map_sum, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Option.some.injEq, reduceCtorEq, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_false,
      zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hrepr]
  rw [LinearMap.trace_eq_matrix_trace (ZMod p) b, LinearMap.trace_eq_matrix_trace ℤ
    (basisModTorsion F)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_option, row_none,
    row_some, Int.cast_sum]

end
end DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace
