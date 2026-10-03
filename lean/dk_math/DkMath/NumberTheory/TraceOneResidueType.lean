import DkMath.Lib.NumberTheory.QuadraticResidueType
import DkMath.NumberTheory.TraceOneQuadratic

/-! Multiplication-preserving residue models for the existing TraceOne carrier. -/
namespace DkMath.NumberTheory.TraceOneResidueType
open TraceOneQuadratic
open DkMath.Lib.NumberTheory.QuadraticResidueType

/-- Coordinate reduction retains `τ² = s + τ`. -/
def residueMap (s : ℤ) (q : ℕ) :
    TraceOneInt s →+* QuadraticAlgebra (ZMod q) (s : ZMod q) 1 where
  toFun x := ⟨x.fst, x.snd⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- Every residue coordinate pair is attained by integral reduction. -/
theorem residueMap_surjective (s : ℤ) (q : ℕ) : Function.Surjective (residueMap s q) := by
  intro z
  refine ⟨⟨ZMod.cast z.re, ZMod.cast z.im⟩, ?_⟩
  ext <;> simp [residueMap]

/-- The existing integral discriminant reduces to Mathlib's quadratic discriminant. -/
theorem residue_discr (s : ℤ) (q : ℕ) :
    QuadraticAlgebra.discr (s : ZMod q) 1 = (discr s : ZMod q) := by
  simp [QuadraticAlgebra.discr, discr]

theorem split_of_even (s : ℤ) (h : Even s) : Split (s : ZMod 2) 1 := by
  obtain ⟨k, rfl⟩ := h
  have hk : ((k + k : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [hk]
  exact traceOne_mod_two_split

theorem inert_of_odd (s : ℤ) (h : Odd s) : Inert (s : ZMod 2) 1 := by
  obtain ⟨k, rfl⟩ := h
  have hk : ((2 * k + 1 : ℤ) : ZMod 2) = 1 := by simp [show (2 : ZMod 2) = 0 by decide]
  rw [hk]
  exact traceOne_mod_two_inert

/-- Parity gives the complete characteristic-two TraceOne dichotomy. -/
theorem mod_two_dichotomy (s : ℤ) :
    (Even s ∧ Split (s : ZMod 2) 1) ∨ (Odd s ∧ Inert (s : ZMod 2) 1) := by
  rcases Int.even_or_odd s with h | h
  · exact Or.inl ⟨h, split_of_even s h⟩
  · exact Or.inr ⟨h, inert_of_odd s h⟩

/-- At any odd prime the signed integral discriminant controls all three types. -/
theorem odd_prime_classification (s : ℤ) (q : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] :
    (Split (s : ZMod q) 1 ↔ IsSquare (discr s : ZMod q) ∧ (discr s : ZMod q) ≠ 0) ∧
    (Inert (s : ZMod q) 1 ↔ ¬ IsSquare (discr s : ZMod q)) ∧
    (Ramified (s : ZMod q) 1 ↔ (discr s : ZMod q) = 0) := by
  simpa only [residue_discr] using
    And.intro (split_iff_discr (s : ZMod q) 1)
      (And.intro (inert_iff_discr (s : ZMod q) 1) (ramified_iff_discr (s : ZMod q) 1))

end DkMath.NumberTheory.TraceOneResidueType
