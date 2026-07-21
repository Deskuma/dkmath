/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Logic.ExistsUnique

universe u v

namespace DkMath.BookOfMagic

section

variable {Core : Type u}
variable {Gap : Core → Type v}

/-- A core has exactly one certified restoring gap. -/
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop :=
  ∃! gap, RestoreRel core gap

/-- Two distinct certified gaps over one core refute the unique-gap contract. -/
theorem not_uniqueGap_of_two
    {RestoreRel : (core : Core) → Gap core → Prop}
    {core : Core}
    {gap₁ gap₂ : Gap core}
    (h₁ : RestoreRel core gap₁)
    (h₂ : RestoreRel core gap₂)
    (hne : gap₁ ≠ gap₂) :
    ¬ UniqueGap RestoreRel core := by
  intro hunique
  rcases hunique with ⟨gap, hgap, honly⟩
  apply hne
  exact (honly gap₁ h₁).trans (honly gap₂ h₂).symm

end


end DkMath.BookOfMagic
