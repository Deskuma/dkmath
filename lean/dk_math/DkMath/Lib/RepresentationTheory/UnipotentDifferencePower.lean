/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter

#print "file: DkMath.Lib.RepresentationTheory.UnipotentDifferencePower"

/-!
# 積零の作用差分の冪公式と同じ点の周期

通常の差分準同型の冪保存から線形な冪公式を得る。
有限捩れへの適用で周期を内部供給し、野生剛性へ渡す。
-/
namespace DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
variable {R Γ V : Type*} [Ring R] [Group Γ] [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (hprod : ∀ σ τ, (ρ σ - 1) * (ρ τ - 1) = 0)

include hprod

/-- 同じ基点の m 乗の作用差は、元の作用差の m 倍。 -/
theorem difference_pow (σ : Γ) (x : V) (m : ℕ) :
    ρ (σ ^ m) x - x = m • (ρ σ x - x) :=
  congrArg Multiplicative.toAdd (map_pow (character ρ hprod x) σ m)

/-- m で消える同じ点は、同じ作用元の m 乗に固定される。 -/
theorem fixed_by_pow_of_killed (σ : Γ) (x : V) {m : ℕ} (hx : m • x = 0) :
    ρ (σ ^ m) x = x := by
  apply sub_eq_zero.mp
  rw [difference_pow ρ hprod σ x m, nsmul_sub, ← map_nsmul, hx, map_zero, sub_self]

end DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
