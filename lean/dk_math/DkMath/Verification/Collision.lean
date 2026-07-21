/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Logic.Function.Basic

/-!
# Collision certificates

A `CollisionCertificate` records two distinct inputs with the same image.  Its
generic consequences are independent of any domain-specific counterexample.
-/

universe u v

namespace DkMath.Verification

/-- Two distinct inputs with the same image under `f`. -/
structure CollisionCertificate
    {α : Type u}
    {β : Type v}
    (f : α → β) where
  left : α
  right : α
  left_ne_right : left ≠ right
  map_eq : f left = f right

/-- An explicit collision refutes injectivity. -/
theorem CollisionCertificate.notInjective
    {α : Type u}
    {β : Type v}
    {f : α → β}
    (c : CollisionCertificate f) :
    ¬ Function.Injective f := by
  intro hinjective
  exact c.left_ne_right (hinjective c.map_eq)

/-- A function with an explicit collision has no set-theoretic left inverse. -/
theorem CollisionCertificate.noLeftInverse
    {α : Type u}
    {β : Type v}
    {f : α → β}
    (c : CollisionCertificate f) :
    ¬ ∃ g : β → α, Function.LeftInverse g f := by
  rintro ⟨g, hleft⟩
  exact c.left_ne_right (hleft.injective c.map_eq)

end DkMath.Verification

#print "file: DkMath.Verification.Collision"
