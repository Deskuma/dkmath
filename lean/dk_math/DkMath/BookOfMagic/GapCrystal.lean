/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.BookOfMagic.UniqueGapContract

universe u v

namespace DkMath.BookOfMagic

/-- The subtype of certified gaps over a fixed core. -/
def GapFiber
    {Core : Type u}
    {Gap : Core → Type v}
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) :=
  { gap : Gap core // RestoreRel core gap }

/-- A core together with a dependent gap and its restoration certificate. -/
structure GapCrystal
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) where
  core : Core
  gap : Gap core
  certificate : RestoreRel core gap

/-- The world of certified core-gap objects. -/
abbrev CrystalWorld
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop) :=
  GapCrystal Core Gap RestoreRel

/-- Forget the dependent gap and retain only its core. -/
def forgetGap
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    (crystal : CrystalWorld Core Gap RestoreRel) : Core :=
  crystal.core

/-- Two distinct certified gaps over one core make the forgetting map noninjective. -/
theorem forgetGap_notInjective_of_two_gaps
    {Core : Type u}
    {Gap : Core → Type v}
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ Function.Injective
      (forgetGap
        (Core := Core)
        (Gap := Gap)
        (RestoreRel := RestoreRel)) := by
  let crystal₁ : CrystalWorld Core Gap RestoreRel := ⟨core, gap₁, h₁⟩
  let crystal₂ : CrystalWorld Core Gap RestoreRel := ⟨core, gap₂, h₂⟩
  intro hinjective
  have hcrystal : crystal₁ = crystal₂ := hinjective rfl
  apply hne
  injection hcrystal

end DkMath.BookOfMagic
