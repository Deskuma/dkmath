/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.CommonLattice
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.NumberTheory.PrimorialUniverse.UnitIntersectionClassification"

/-!
# Two-unit intersection classification

This module closes the existence question left by PUU-L003.  Two positive
real unit universes have a positive common lattice point exactly when some
positive coprime natural coordinates synchronize them.  Every arbitrary
positive common coordinate pair is normalized to that coprime synchronization
by dividing both coordinates by their gcd.

The three semantic cases are: equal unit values (complete synchronization),
commensurable unequal unit values (partial synchronization), and no positive
common point (incommensurability in this finite integer sense).  This module
does not identify commensurability with Mathlib's rational/irrational APIs and
does not introduce wheels, PowerSwap, Legendre, or generic lattice theory.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Commensurability and positive intersections -/

/-- Two positive units are commensurable when positive coprime coordinates
    synchronize them. -/
def UnitsCommensurable (u₁ u₂ : PositiveUnit) : Prop :=
  ∃ a b : ℕ, UnitSynchronizesBy u₁ u₂ a b

/-- The two units share a positive natural-coordinate lattice point. -/
def HasPositiveCommonLatticePoint
    (u₁ u₂ : PositiveUnit) : Prop :=
  ∃ m n : ℕ,
    0 < m ∧
    0 < n ∧
    ∃ X : ℝ, HasCommonUnitCoordinates u₁ u₂ m n X

/-- Commensurable unequal units form the partial-synchronization case. -/
def UnitsPartiallySynchronize (u₁ u₂ : PositiveUnit) : Prop :=
  UnitsCommensurable u₁ u₂ ∧ u₁.val ≠ u₂.val

/-! ## Normalization of a positive common point -/

/-- A positive common coordinate pair yields a coprime synchronization.

The normalization is `a = m / gcd m n` and `b = n / gcd m n`.  Positivity
ensures that the gcd is nonzero, so the normalized coordinates remain
positive.
-/
theorem exists_coprimeSynchronization_of_positiveCommonCoordinates
    {u₁ u₂ : PositiveUnit} {m n : ℕ} {X : ℝ}
    (hm : 0 < m)
    (hn : 0 < n)
    (hcommon : HasCommonUnitCoordinates u₁ u₂ m n X) :
    ∃ a b : ℕ,
      UnitSynchronizesBy u₁ u₂ a b := by
  let g : ℕ := Nat.gcd m n
  let a : ℕ := m / g
  let b : ℕ := n / g
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left n hm
  have hga : g ≤ m := by
    dsimp [g]
    exact Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)
  have hgb : g ≤ n := by
    dsimp [g]
    exact Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.div_pos hga hg
  have hb : 0 < b := by
    dsimp [b]
    exact Nat.div_pos hgb hg
  have hcop : Nat.Coprime a b := by
    dsimp [a, b, g]
    exact Nat.coprime_div_gcd_div_gcd hg
  have hm_eq : m = a * g := by
    dsimp [a, g]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm
  have hn_eq : n = b * g := by
    dsimp [b, g]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm
  have hsync : (a : ℝ) * u₁.val = (b : ℝ) * u₂.val := by
    have hscaled :
        (a : ℝ) * ((g : ℝ) * u₁.val) =
          (b : ℝ) * ((g : ℝ) * u₂.val) := by
      calc
        (a : ℝ) * ((g : ℝ) * u₁.val) =
            (((a * g : ℕ) : ℝ) * u₁.val) := by
              simp only [Nat.cast_mul]
              ring
        _ = (m : ℝ) * u₁.val := by rw [hm_eq]
        _ = (n : ℝ) * u₂.val := hcommon.1.symm.trans hcommon.2
        _ = (((b * g : ℕ) : ℝ) * u₂.val) := by
              rw [hn_eq]
        _ = (b : ℝ) * ((g : ℝ) * u₂.val) := by
              rw [Nat.cast_mul]
              ring
    apply mul_right_cancel₀ (ne_of_gt (show 0 < (g : ℝ) from by exact_mod_cast hg))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled
  exact ⟨a, b, ha, hb, hcop, hsync⟩

/-! ## Existence equivalence -/

/-- A synchronization supplies its canonical positive common lattice point. -/
theorem unitsCommensurable_hasPositiveCommonLatticePoint
    {u₁ u₂ : PositiveUnit} :
    UnitsCommensurable u₁ u₂ →
      HasPositiveCommonLatticePoint u₁ u₂ := by
  rintro ⟨a, b, hsync⟩
  refine ⟨a, b, hsync.1, hsync.2.1, ?_⟩
  exact ⟨(a : ℝ) * u₁.val, syncCoordinates_have_common_point hsync⟩

/-- Positive common lattice points are exactly integer commensurability. -/
theorem hasPositiveCommonLatticePoint_iff_unitsCommensurable
    (u₁ u₂ : PositiveUnit) :
    HasPositiveCommonLatticePoint u₁ u₂ ↔
      UnitsCommensurable u₁ u₂ := by
  constructor
  · rintro ⟨m, n, hm, hn, X, hcommon⟩
    exact exists_coprimeSynchronization_of_positiveCommonCoordinates hm hn hcommon
  · exact unitsCommensurable_hasPositiveCommonLatticePoint

/-- Negated form of the positive-intersection equivalence. -/
theorem noPositiveCommonLatticePoint_iff_not_unitsCommensurable
    (u₁ u₂ : PositiveUnit) :
    (¬ HasPositiveCommonLatticePoint u₁ u₂) ↔
      ¬ UnitsCommensurable u₁ u₂ := by
  exact not_congr (hasPositiveCommonLatticePoint_iff_unitsCommensurable u₁ u₂)

/-! ## Complete and partial synchronization -/

/-- Equal unit values are completely synchronized by `(1,1)`. -/
theorem equalUnits_unitsCommensurable
    {u₁ u₂ : PositiveUnit}
    (h : u₁.val = u₂.val) :
    UnitsCommensurable u₁ u₂ := by
  refine ⟨1, 1, by simp, by simp, by simp, ?_⟩
  simp [h]

/-- Equal units share every same-coordinate natural point. -/
theorem equalUnits_allCoordinates_common
    {u₁ u₂ : PositiveUnit}
    (h : u₁.val = u₂.val)
    (n : ℕ) :
    ∃ X : ℝ,
      HasCommonUnitCoordinates u₁ u₂ n n X := by
  refine ⟨(n : ℝ) * u₁.val, rfl, ?_⟩
  simp [h]

/-- A partial synchronization still has positive common lattice points. -/
theorem partiallySynchronized_hasPositiveCommonLatticePoint
    {u₁ u₂ : PositiveUnit}
    (hpartial : UnitsPartiallySynchronize u₁ u₂) :
    HasPositiveCommonLatticePoint u₁ u₂ :=
  unitsCommensurable_hasPositiveCommonLatticePoint hpartial.1

/-- Unequal commensurable units have no positive same-coordinate common point. -/
theorem partiallySynchronized_no_positive_sameCoordinateCommonPoint
    {u₁ u₂ : PositiveUnit}
    (hpartial : UnitsPartiallySynchronize u₁ u₂) :
    ¬ ∃ n : ℕ,
      0 < n ∧
      ∃ X : ℝ,
        HasCommonUnitCoordinates u₁ u₂ n n X := by
  rintro ⟨n, hn, X, hcommon⟩
  apply hpartial.2
  apply sameCoordinate_synchronization_unit_eq hn
  exact hcommon.1.symm.trans hcommon.2

/-! ## The intersection trichotomy -/

/-- Complete synchronization, partial synchronization, or no positive
    synchronization exhausts the two-unit intersection cases. -/
theorem unitIntersection_trichotomy
    (u₁ u₂ : PositiveUnit) :
    u₁.val = u₂.val ∨
      UnitsPartiallySynchronize u₁ u₂ ∨
      ¬ UnitsCommensurable u₁ u₂ := by
  by_cases hEqual : u₁.val = u₂.val
  · exact Or.inl hEqual
  · by_cases hComm : UnitsCommensurable u₁ u₂
    · exact Or.inr (Or.inl ⟨hComm, hEqual⟩)
    · exact Or.inr (Or.inr hComm)

/-! ## Small regression -/

theorem regressionUnits_partialSynchronization :
    UnitsPartiallySynchronize regressionUnitThree regressionUnitTwo := by
  refine ⟨?_, ?_⟩
  · exact ⟨2, 3, two_three_synchronization_regression⟩
  · norm_num [regressionUnitThree, regressionUnitTwo]

end DkMath.NumberTheory.PrimorialUniverse
