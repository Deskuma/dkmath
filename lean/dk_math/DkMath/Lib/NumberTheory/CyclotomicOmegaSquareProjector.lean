/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
import DkMath.Lib.NumberTheory.CyclotomicClassVanishing

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector"

/-!
# 同じ単元商・同じ Galois 作用の ω² 射影子

実際の群の位数 p−1 の可逆性を内部供給する。
像が既存 weightSquareSpace と一致する射影を構成する。
固有空間の次元・非零性はここでは主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicKummerEquivariance
open KummerSelmerExact KummerSelmerUnitEquivariance CyclotomicPrimaryUnitSpace
open CyclotomicClassVanishing
open scoped NumberField
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 元の整数環作用を、同じ単元冪商上の実際の線形表現にまとめる。 -/
def unitAction : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) →*
    Module.End (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) where
  toFun γ := unitClassLinearMap p (integerAut γ)
  map_one' := by
    ext x
    change Additive.ofMul (unitClassMap p (integerAut 1) x.toMul) = x
    rw [integerAut_one, unitClassMap_refl]
    rfl
  map_mul' γ δ := by
    ext x
    change Additive.ofMul (unitClassMap p (integerAut (γ * δ)) x.toMul) =
      Additive.ofMul (unitClassMap p (integerAut γ) (unitClassMap p (integerAut δ) x.toMul))
    rw [integerAut_mul, unitClassMap_trans]

/-- 同じ baseCharacter の二乗に対する平均射影。 -/
def omegaSquareProjector : Module.End (ZMod p)
    (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  (Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) : ZMod p)⁻¹ •
    ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitAction (p := p) γ

/-- 射影の実際の有限和表示。 -/
theorem omegaSquareProjector_apply (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x =
      (Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) : ZMod p)⁻¹ •
        ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x := by
  simp only [omegaSquareProjector, LinearMap.smul_apply, LinearMap.sum_apply, unitAction,
    MonoidHom.coe_mk, OneHom.coe_mk]

/-- 平均の像は同じ ω² 固有条件を満たす。 -/
theorem omegaSquareProjector_mem (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x ∈ weightSquareSpace hζ := by
  intro δ
  rw [omegaSquareProjector_apply, map_smul, map_sum]
  have he : ∀ γ, unitClassLinearMap p (integerAut δ)
      (((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x) =
      ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut (δ * γ)) x := by
    intro γ
    rw [map_smul]
    exact congrArg (fun y => ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • y)
      (LinearMap.congr_fun (map_mul (unitAction (p := p)) δ γ) x).symm
  rw [Finset.sum_congr rfl (fun γ _ => he γ)]
  have hs : ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut (δ * γ)) x =
      (baseCharacter hζ δ : ZMod p) ^ 2 •
        ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x := by
    rw [Finset.smul_sum]
    refine Fintype.sum_bijective (δ * ·) (Group.mulLeft_bijective δ) _ _ (fun γ => ?_)
    rw [smul_smul, map_mul, Units.val_mul, mul_pow, mul_inv_rev]
    congr 1
    have hn : (baseCharacter hζ δ : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 (baseCharacter hζ δ).ne_zero
    field_simp
  rw [hs, smul_comm]

/-- 固有空間上で射影は恒等写像。群位数の可逆性は算術から供給する。 -/
theorem omegaSquareProjector_eq_self (x : Additive (UnitClass (𝓞 (rootField ζ)) p))
    (hx : x ∈ weightSquareSpace hζ) : omegaSquareProjector hζ x = x := by
  rw [omegaSquareProjector_apply]
  have he : ∀ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut γ) x = x := by
    intro γ
    rw [hx γ, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (baseCharacter hζ γ).ne_zero), one_smul]
  rw [Finset.sum_congr rfl (fun γ _ => he γ), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul (R := ZMod p), smul_smul,
    inv_mul_cancel₀ (root_galois_card_isUnit hζ).ne_zero, one_smul]

/-- 射影を二度適用しても変わらない。 -/
theorem omegaSquareProjector_idempotent :
    omegaSquareProjector hζ * omegaSquareProjector hζ = omegaSquareProjector hζ := by
  ext x
  exact omegaSquareProjector_eq_self hζ _ (omegaSquareProjector_mem hζ x)

/-- 射影の像は新しい代用品でなく、既存の同じ固有空間である。 -/
theorem omegaSquareProjector_range :
    LinearMap.range (omegaSquareProjector hζ) = weightSquareSpace hζ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact omegaSquareProjector_mem hζ y
  · intro hx
    exact ⟨x, omegaSquareProjector_eq_self hζ x hx⟩

/-- 指定した根の指標自体を同型にする。標準 zeta への取り替えを使わない。 -/
def characterEquiv : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) ≃* (ZMod p)ˣ :=
  letI := rootField_isCyclotomic hζ
  MulEquiv.ofBijective (baseCharacter hζ) (by
    apply (Fintype.bijective_iff_injective_and_card (baseCharacter hζ)).mpr
    refine ⟨(baseRoot_primitive hζ).autToPow_injective ℚ, ?_⟩
    rw [← Nat.card_eq_fintype_card, root_galois_card hζ, ZMod.card_units p])

/-- 逆同型で選んだ自己同型は、同じ指定根を d 乗へ送る。 -/
theorem characterEquiv_symm_root (d : (ZMod p)ˣ) :
    (characterEquiv hζ).symm d (baseRoot ζ) = baseRoot ζ ^ (d : ZMod p).val := by
  have h := (baseRoot_primitive hζ).autToPow_spec ℚ ((characterEquiv hζ).symm d)
  have hd : baseCharacter hζ ((characterEquiv hζ).symm d) = d :=
    (characterEquiv hζ).apply_symm_apply d
  rw [show (baseRoot_primitive hζ).autToPow ℚ ((characterEquiv hζ).symm d) = d from hd] at h
  exact h.symm

/-- 非零評価に使う、同じ指標同型による有限和の添字変更。 -/
theorem omegaSquareProjector_apply_units (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x =
      (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ,
        ((d : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut ((characterEquiv hζ).symm d)) x := by
  rw [omegaSquareProjector_apply]
  have hc : Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) = Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (characterEquiv hζ).toEquiv
  rw [hc]
  congr 1
  exact Fintype.sum_equiv (characterEquiv hζ).toEquiv _ _ (fun γ => by
    change _ = ((characterEquiv hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut ((characterEquiv hζ).symm (characterEquiv hζ γ))) x
    rw [MulEquiv.symm_apply_apply]
    rfl)

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector
