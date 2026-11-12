/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKernelField
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.Lib.NumberTheory.KummerRadicalCharacter"

/-!
# 同じ根の比を取る Kummer 指標

`α^p` を円分指標核が固定するとき、`u(α)/α` は実際の `μ_p` に入る。
核上では根の群の作用が自明なので、この比は群準同型となる。
さらに元の全射加法指標の核で零になる比は、その値域を経由する。
この因子化を `ZMod p` 線形として読み、共役でのスカラーを同じ比へ輸送する。
-/

namespace DkMath.Lib.NumberTheory.KummerRadicalCharacter

open CyclotomicRootModule
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime]
local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- 円分指標核の各元は全ての `p` 乗根を固定する。 -/
theorem kernel_fixes_root (u : (cyclotomicCharacter (K := ℚ) p).ker)
    (z : rootsOfUnity p (AlgebraicClosure ℚ)) : u.val.toAlgHom (z.val : AlgebraicClosure ℚ) = z.val := by
  have h := cyclotomicCharacter_spec (K := ℚ) p u.val z
  rw [MonoidHom.mem_ker.mp u.property, Units.val_one, ZMod.val_one, pow_one] at h
  exact h

variable (α : AlgebraicClosure ℚ) (hα : α ≠ 0)
    (hpow : ∀ u : (cyclotomicCharacter (K := ℚ) p).ker, u.val.toAlgHom (α ^ p) = α ^ p)

include hα hpow in
/-- 根の比は実際に `p` 乗根となる。 -/
theorem ratio_pow (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    (u.val.toAlgHom α / α) ^ p = 1 := by
  rw [div_pow, ← map_pow, hpow u, div_self (pow_ne_zero p hα)]

/-- 同じ代数閉包内で同じ根の比を取る実際の指標。 -/
def radicalCharacter : (cyclotomicCharacter (K := ℚ) p).ker →*
    rootsOfUnity p (AlgebraicClosure ℚ) where
  toFun u := rootsOfUnity.mkOfPowEq _ (ratio_pow α hα hpow u)
  map_one' := by
    apply rootsOfUnity.coe_injective
    change α / α = 1
    exact div_self hα
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    change u.val.toAlgHom (v.val.toAlgHom α) / α =
      (u.val.toAlgHom α / α) * (v.val.toAlgHom α / α)
    have hf := kernel_fixes_root u (rootsOfUnity.mkOfPowEq _ (ratio_pow α hα hpow v))
    change u.val.toAlgHom (v.val.toAlgHom α / α) = v.val.toAlgHom α / α at hf
    rw [map_div₀] at hf
    have hu : u.val.toAlgHom α ≠ 0 := (map_ne_zero u.val.toAlgHom).mpr hα
    apply (div_eq_iff hα).mpr
    have he := (div_eq_iff hu).mp hf
    rw [he]
    field_simp

theorem radicalCharacter_coe (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    ((radicalCharacter α hα hpow u).val : AlgebraicClosure ℚ) = u.val.toAlgHom α / α := rfl

/-- 指標が1であることと同じ根の固定性は同値。 -/
theorem radicalCharacter_eq_one_iff (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    radicalCharacter α hα hpow u = 1 ↔ u.val.toAlgHom α = α := by
  rw [← rootsOfUnity.coe_injective.eq_iff]
  change u.val.toAlgHom α / α = 1 ↔ _
  exact div_eq_one_iff_eq hα

section Factor

variable {G C : Type*} [Group G] [AddCommGroup C] [Module (ZMod p) C]
    (ψ : G →* Multiplicative C) (hsurj : Function.Surjective ψ)
    (κ : G →* rootsOfUnity p (AlgebraicClosure ℚ)) (hker : ψ.ker ≤ κ.ker)

/-- 元の全射指標の値域への因子化。基底や離散対数の選択は不要である。 -/
def factor : Multiplicative C →* rootsOfUnity p (AlgebraicClosure ℚ) :=
  (QuotientGroup.lift ψ.ker κ hker).comp
    (QuotientGroup.liftEquiv ψ.ker hsurj rfl).symm.toMonoidHom

omit [Fact p.Prime] [Module (ZMod p) C] in
theorem factor_apply (u : G) : factor ψ hsurj κ hker (ψ u) = κ u := by
  let e := QuotientGroup.liftEquiv ψ.ker hsurj rfl
  change (QuotientGroup.lift ψ.ker κ hker) (e.symm (e (QuotientGroup.mk u))) = κ u
  rw [e.symm_apply_apply]
  rfl

include hsurj hker in
/-- 元の加法指標でのスカラー関係は、同じ Kummer 比の冪の関係になる。 -/
theorem map_scalar (u v : G) (a : ZMod p) (h : (ψ u).toAdd = a • (ψ v).toAdd) :
    κ u = κ v ^ a.val := by
  let f := (factor ψ hsurj κ hker).toAdditiveRight
  have he := congrArg f h
  rw [ZMod.map_smul] at he
  change Additive.ofMul (factor ψ hsurj κ hker (ψ u)) =
    a • Additive.ofMul (factor ψ hsurj κ hker (ψ v)) at he
  rw [factor_apply, factor_apply] at he
  have hm := congrArg Additive.toMul he
  simpa only [smul_toMul, toMul_ofMul] using hm

end Factor

variable {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ (radicalCharacter α hα hpow).ker)
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

include hsurj hker hweight in
/-- 逆指標の共役則と根自身の円分作用を合わせると、比の指数は円分指標の二乗になる。
底体を動かす `σ` と、底体上の `u` を別々に追跡する。 -/
theorem conjugate_ratio (σ : Field.absoluteGaloisGroup ℚ)
    (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    u.val.toAlgHom (σ.toAlgHom α) / σ.toAlgHom α =
      (u.val.toAlgHom α / α) ^ ((cyclotomicCharacter p σ : ZMod p) ^ 2).val := by
  let κ := radicalCharacter α hα hpow
  let d : ZMod p := cyclotomicCharacter p σ
  have hw : cyclotomicCharacter p (σ⁻¹ * u.val * σ) = 1 := by
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp u.property, mul_one, map_inv, inv_mul_cancel]
  let w : (cyclotomicCharacter (K := ℚ) p).ker := ⟨σ⁻¹ * u.val * σ, hw⟩
  have hk : κ w = κ u ^ d.val := by
    apply map_scalar ψ hsurj κ hker w u d
    simpa only [inv_inv] using hweight σ⁻¹ u hw
  have hr : σ.toAlgHom ((κ w).val : AlgebraicClosure ℚ) =
      ((κ u).val : AlgebraicClosure ℚ) ^ (d ^ 2).val := by
    calc
      _ = ((κ w).val : AlgebraicClosure ℚ) ^ d.val :=
        cyclotomicCharacter_spec (K := ℚ) p σ (κ w)
      _ = (((κ u).val : AlgebraicClosure ℚ) ^ d.val) ^ d.val := by rw [hk, rootsOfUnity.coe_pow]
      _ = ((κ u).val : AlgebraicClosure ℚ) ^ (d * d).val := by
        rw [← pow_mul, ZMod.val_mul]
        exact pow_eq_pow_mod _ ((mem_rootsOfUnity' p (κ u).val).mp (κ u).property)
      _ = _ := by rw [pow_two]
  change σ.toAlgHom (w.val.toAlgHom α / α) = _ at hr
  rw [map_div₀] at hr
  have hwσ : σ * w.val = u.val * σ := by
    change σ * (σ⁻¹ * u.val * σ) = _
    group
  have he := congrArg (fun g : Field.absoluteGaloisGroup ℚ => g.toAlgHom α) hwσ
  change σ.toAlgHom (w.val.toAlgHom α) = u.val.toAlgHom (σ.toAlgHom α) at he
  rw [he] at hr
  exact hr

end
end DkMath.Lib.NumberTheory.KummerRadicalCharacter
