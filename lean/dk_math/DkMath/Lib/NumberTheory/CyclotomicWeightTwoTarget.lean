/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicClassVanishing
import Mathlib.NumberTheory.Bernoulli

#print "file: DkMath.Lib.NumberTheory.CyclotomicWeightTwoTarget"

/-! # 実際の ω² 類群成分と B₂ の算術的準備
Herbrand・反射定理や類群消滅を仮定も結論もしない。現在の hclass の正確な対象を固定する。 -/
namespace DkMath.Lib.NumberTheory.CyclotomicClassVanishing
open CyclotomicRootModule CyclotomicKernelField CyclotomicKummerWeight
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 元の ClassModP と元の classModPAction を使う整数線形 ω² 固有部分空間。 -/
def weightTwoComponent : Submodule ℤ (ClassModP (rootField ζ) p) where
  carrier := {a | ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
    classModPAction p γ a = (baseCharacter hζ γ : ZMod p) ^ 2 • a}
  zero_mem' := by intro γ; simp
  add_mem' := by intro a b ha hb γ; rw [map_add, ha γ, hb γ, smul_add]
  smul_mem' := by intro n a ha γ; rw [map_smul, ha γ, smul_comm]

/-- 現行 hclass は、同じ固有部分空間が零であることそのもの。消滅の証明ではない。 -/
theorem weightTwo_eq_bot_iff : weightTwoComponent hζ = ⊥ ↔
    ∀ a : ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        classModPAction p γ a = (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0 := by
  constructor
  · intro he a ha
    have hm : a ∈ weightTwoComponent hζ := ha
    rw [he, Submodule.mem_bot] at hm
    exact hm
  · intro hv
    apply le_antisymm _ bot_le
    intro a ha
    exact hv a ha

/-- Herbrand の k=2 に現れる実際の Bernoulli 数。 -/
theorem bernoulli_two_numerator : (bernoulli 2).num = 1 := by
  rw [bernoulli_two]
  norm_num

omit [Fact p.Prime] in
/-- p≥5 なら B₂ の分子を p は割らない。類群への輸送は別途必要。 -/
theorem prime_not_dvd_bernoulli_two_numerator (hp5 : 5 ≤ p) : ¬ (p : ℤ) ∣ (bernoulli 2).num := by
  rw [bernoulli_two_numerator]
  intro hd
  have habs : (p : ℕ) ∣ 1 := by exact_mod_cast hd
  have := Nat.le_of_dvd (by decide : 0 < 1) habs
  omega
end
end DkMath.Lib.NumberTheory.CyclotomicClassVanishing

