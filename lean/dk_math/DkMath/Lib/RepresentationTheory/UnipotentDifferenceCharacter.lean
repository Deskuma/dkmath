/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

#print "file: DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter"

/-!
# 積零の作用差分は通常の加法的準同型になる

値は Multiplicative で包んだ元の加法群。共役輸送では基点も動かす。
Frobenius の q 倍関係や野生慣性の消滅は仮定しない。
-/
namespace DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
variable {R Γ V : Type*} [Ring R] [Group Γ] [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (hprod : ∀ σ τ, (ρ σ - 1) * (ρ τ - 1) = 0)

include hprod

/-- 同じ差点は全作用元に固定される。 -/
theorem difference_fixed (σ τ : Γ) (x : V) : ρ σ (ρ τ x - x) = ρ τ x - x := by
  have h := congrArg (fun f : Module.End R V => f x) (hprod σ τ)
  change ρ σ (ρ τ x - x) - (ρ τ x - x) = 0 at h
  exact sub_eq_zero.mp h

/-- 二次の差分積が零なら、固定した同じ基点の差分は加法的。 -/
theorem difference_mul (σ τ : Γ) (x : V) :
    ρ (σ * τ) x - x = (ρ σ x - x) + (ρ τ x - x) := by
  rw [map_mul]
  change ρ σ (ρ τ x) - x = _
  calc
    ρ σ (ρ τ x) - x = ρ σ (ρ τ x - x) + (ρ σ x - x) := by rw [map_sub]; abel
    _ = _ := by rw [difference_fixed ρ hprod σ τ x]; abel

/-- 元の同じ加法群への通常の群準同型。 -/
def character (x : V) : Γ →* Multiplicative V where
  toFun σ := Multiplicative.ofAdd (ρ σ x - x)
  map_one' := by change ρ 1 x - x = 0; rw [map_one]; exact sub_self x
  map_mul' σ τ := difference_mul ρ hprod σ τ x

omit hprod in
/-- 共役の作用差分を輸送する恒等式。基点を ρ(φ)x へ動かすことが必要。 -/
theorem difference_conjugate (φ τ : Γ) (x : V) :
    ρ (φ * τ * φ⁻¹) (ρ φ x) - ρ φ x = ρ φ (ρ τ x - x) := by
  change (ρ (φ * τ * φ⁻¹) * ρ φ) x - ρ φ x = _
  rw [← map_mul, show (φ * τ * φ⁻¹) * φ = φ * τ by simp [mul_assoc], map_mul, map_sub]
  rfl

end DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
