/-
New theorems for SilverRatioUnit: Unique representation in Q(√2)

Key insight: The naive statement "∃! (p : ℝ × ℝ), Ag p.1 p.2 = x" is NOT true
for all x ∈ ℝ. However, it IS true when x ∈ ℚ(√2) and (a,b) ∈ ℚ².

This is because {1, √2} is ℚ-linearly independent (from √2's irrationality),
which makes uAg = (1 + √2)/2 generate a unique representation system.
-/

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas
import DkMath.SilverRatio.SilverRatioUnit

namespace DkMath.SilverRatio.SilverRatioUnit

open Real
open DkMath.SilverRatio.Sqrt2
open DkMath.SilverRatioUnit

noncomputable section

/-- Linear independence of {1, √2} over ℚ.
   Key lemma: If a + b*√2 = c + d*√2 where a,b,c,d ∈ ℚ, then a=c and b=d.
   This follows from √2 being irrational.
-/
lemma sqrt2_Q_lin_indep (a b c d : ℚ) :
    (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 → a = c ∧ b = d := by
  intro h
  by_cases hbd : b = d
  · have : (a : ℝ) = (c : ℝ) := by
      rw [hbd] at h
      have : (a : ℝ) + (d : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 := h
      linarith
    exact ⟨Rat.cast_injective this, hbd⟩
  · have hbd_ne : ((b - d : ℚ) : ℝ) ≠ 0 := by norm_cast; intro heq; grind only
    have h_diff : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := by
      have : (a : ℝ) + (b : ℝ) * sqrt2 = (c : ℝ) + (d : ℝ) * sqrt2 := h
      have : (a : ℝ) - (c : ℝ) + ((b : ℝ) - (d : ℝ)) * sqrt2
           = (a : ℝ) + (b : ℝ) * sqrt2 - ((c : ℝ) + (d : ℝ) * sqrt2) := by ring
      calc ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2
           = (a : ℝ) - (c : ℝ) + ((b : ℝ) - (d : ℝ)) * sqrt2 := by push_cast; ring
         _ = (a : ℝ) + (b : ℝ) * sqrt2 - ((c : ℝ) + (d : ℝ) * sqrt2) := this
         _ = 0 := by rw [h]; ring
    have h_sqrt2 : sqrt2 = -((a - c : ℚ) : ℝ) / ((b - d : ℚ) : ℝ) := by
      field_simp [hbd_ne]
      have : ((a - c : ℚ) : ℝ) + ((b - d : ℚ) : ℝ) * sqrt2 = 0 := h_diff
      nlinarith [this]
    have : sqrt2 ∈ Set.range ((↑) : ℚ → ℝ) := by
      use (-(a - c) : ℚ) / (b - d)
      simp only [Rat.cast_div, Rat.cast_neg]
      exact h_sqrt2.symm
    exact absurd this (sqrt2_irrational)

/-- Definition: Elements of ℚ(√2) expressed via uAg basis.
   InQAdjSqrt2Ag x means x = a + b*uAg for some rational a, b.
   Since uAg = (1 + √2)/2, this is equivalent to x ∈ ℚ(√2).
-/
def InQAdjSqrt2Ag (x : ℝ) : Prop := ∃ a b : ℚ, (a : ℝ) + (b : ℝ) * uAg = x

/-- THEOREM: In ℚ(√2), the representation with basis {1, uAg} is UNIQUE.
   This is the correct and precise form of the "unique representation" result,
   with the restricted domain x ∈ ℚ(√2) and codomain (a,b) ∈ ℚ × ℚ.
-/
theorem Ag_rep_unique_in_Q_ext (x : ℝ) (hx : InQAdjSqrt2Ag x) :
    ∃! (p : ℚ × ℚ), (p.1 : ℝ) + (p.2 : ℝ) * uAg = x := by
  obtain ⟨a₀, b₀, h₀⟩ := hx
  use (a₀, b₀)
  refine ⟨h₀, fun ⟨a, b⟩ hab ↦ ?_⟩
  simp only [Prod.mk.injEq]
  -- Both (a, b) and (a₀, b₀) satisfy the equation
  have h_diff : (a : ℝ) + (b : ℝ) * uAg = (a₀ : ℝ) + (b₀ : ℝ) * uAg := by rw [hab, h₀]
  rw [uAg_eq] at h_diff
  -- Rewrite in standard form: (2a + b) + b*√2 = (2a₀ + b₀) + b₀*√2
  have h_canonical : ((2 * a + b : ℚ) : ℝ) + ((b : ℚ) : ℝ) * sqrt2
                   = ((2 * a₀ + b₀ : ℚ) : ℝ) + ((b₀ : ℚ) : ℝ) * sqrt2 := by
    have h_eq : (a : ℝ) + (b : ℝ) * ((1 + sqrt2) / 2)
              = (a₀ : ℝ) + (b₀ : ℝ) * ((1 + sqrt2) / 2) := h_diff
    field_simp at h_eq
    push_cast at h_eq ⊢
    linarith [h_eq]
  -- Apply Q-linear independence
  have ⟨heq1, heq2⟩ := sqrt2_Q_lin_indep (2*a + b) b (2*a₀ + b₀) b₀ h_canonical
  constructor
  · have h2a : (2 : ℚ) * (a - a₀) = 0 := by linarith [heq1]
    have : (a : ℚ) - a₀ = 0 := by linarith [h2a]
    linarith
  · exact heq2

end -- noncomputable section

end DkMath.SilverRatio.SilverRatioUnit
