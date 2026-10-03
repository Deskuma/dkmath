/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

#print "file: DkMath.Lib.NumberTheory.QuadraticResidueType"

/-! Root-factorization types of the relation `ω² = a + bω`.
These predicates retain the multiplication parameters; they are not additive
carrier classifications. In characteristic two the calibrations are separate. -/
namespace DkMath.Lib.NumberTheory.QuadraticResidueType

variable {K : Type*} [Field K]

/-- Two distinct linear factors of the quadratic relation. -/
def Split (a b : K) : Prop :=
  ∃ r t : K, r ≠ t ∧ r ^ 2 = a + b * r ∧ t ^ 2 = a + b * t
/-- The quadratic relation has no linear factor. -/
def Inert (a b : K) : Prop := ¬ ∃ r : K, r ^ 2 = a + b * r
/-- The quadratic relation has exactly one root (a repeated factor). -/
def Ramified (a b : K) : Prop := ∃! r : K, r ^ 2 = a + b * r

theorem inert_iff_discr [NeZero (2 : K)] (a b : K) :
    Inert a b ↔ ¬ IsSquare (QuadraticAlgebra.discr a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  exact QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.not

theorem inert_iff_isField [NeZero (2 : K)] (a b : K) :
    Inert a b ↔ IsField (QuadraticAlgebra K a b) := by
  rw [inert_iff_discr, QuadraticAlgebra.isField_iff_not_isSquare_discr]

theorem ramified_iff_discr [NeZero (2 : K)] (a b : K) :
    Ramified a b ↔ QuadraticAlgebra.discr a b = 0 := by
  have hd : discrim (1 : K) (-b) (-a) = QuadraticAlgebra.discr a b := by
    simp [discrim, QuadraticAlgebra.discr]
  have he (x : K) : 1 * (x * x) + (-b) * x + (-a) = 0 ↔
      x ^ 2 = a + b * x := by
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  simpa only [Ramified, hd, he] using (discrim_eq_zero_iff (K := K) (a := 1)
    (b := -b) (c := -a) one_ne_zero).symm

theorem split_iff_discr [NeZero (2 : K)] (a b : K) :
    Split a b ↔ IsSquare (QuadraticAlgebra.discr a b) ∧
      QuadraticAlgebra.discr a b ≠ 0 := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · rintro ⟨r, t, hrt, hr, ht⟩
    refine ⟨QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.mp ⟨r, hr⟩, ?_⟩
    intro hd
    obtain ⟨u, hu, huniq⟩ := (ramified_iff_discr a b).mpr hd
    exact hrt ((huniq r hr).trans (huniq t ht).symm)
  · rintro ⟨hs, hn⟩
    obtain ⟨r, hr⟩ := QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.mpr hs
    refine ⟨r, b - r, ?_, hr, ?_⟩
    · intro h
      apply hn
      simp only [QuadraticAlgebra.discr]
      linear_combination -4 * hr + (2 * r - b) * h
    · linear_combination hr

/-- Exhaustive discriminant classification in odd characteristic. -/
theorem classification [NeZero (2 : K)] (a b : K) :
    Split a b ∨ Inert a b ∨ Ramified a b := by
  by_cases hd : QuadraticAlgebra.discr a b = 0
  · exact Or.inr (Or.inr ((ramified_iff_discr a b).mpr hd))
  · by_cases hs : IsSquare (QuadraticAlgebra.discr a b)
    · exact Or.inl ((split_iff_discr a b).mpr ⟨hs, hd⟩)
    · exact Or.inr (Or.inl ((inert_iff_discr a b).mpr hs))

/-- The three types cannot overlap in odd characteristic. -/
theorem exclusive [NeZero (2 : K)] (a b : K) :
    ¬ (Split a b ∧ Inert a b) ∧ ¬ (Split a b ∧ Ramified a b) ∧
      ¬ (Inert a b ∧ Ramified a b) := by
  rw [split_iff_discr, inert_iff_discr, ramified_iff_discr]
  have hz : IsSquare (0 : K) := ⟨0, by simp⟩
  constructor
  · rintro ⟨⟨hs, _⟩, hn⟩; exact hn hs
  constructor
  · rintro ⟨⟨_, hn⟩, hd⟩; exact hn hd
  · rintro ⟨hn, hd⟩; exact hn (hd ▸ hz)

theorem traceOne_mod_two_split : Split (0 : ZMod 2) 1 := by
  exact ⟨0, 1, by decide, by decide, by decide⟩

theorem traceOne_mod_two_inert : Inert (1 : ZMod 2) 1 := by
  intro ⟨r, hr⟩
  fin_cases r <;> revert hr <;> decide

/-- The inert characteristic-two calibration also has a field multiplication. -/
theorem traceOne_mod_two_isField : IsField (QuadraticAlgebra (ZMod 2) 1 1) := by
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) :=
    ⟨fun r hr => traceOne_mod_two_inert ⟨r, hr⟩⟩
  exact Field.toIsField _

theorem gaussian_mod_two_ramified : Ramified (-1 : ZMod 2) 0 := by
  refine ⟨1, by decide, ?_⟩
  intro r hr
  fin_cases r
  · have hn : ¬ (0 : ZMod 2) ^ 2 = -1 + 0 * 0 := by decide
    exact False.elim (hn hr)
  · rfl

/-- The Gaussian repeated factor really gives a nonzero square-zero element. -/
theorem gaussian_mod_two_nilpotent :
    let e : QuadraticAlgebra (ZMod 2) (-1) 0 := ⟨1, 1⟩
    e ≠ 0 ∧ e ^ 2 = 0 := by
  constructor
  · intro h
    have := congrArg QuadraticAlgebra.im h
    norm_num at this
  · ext <;> decide

end DkMath.Lib.NumberTheory.QuadraticResidueType
