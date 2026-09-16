/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PascalPrimeDial
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PascalPrimeCoordinateDecoder"

namespace DkMath
namespace NumberTheory

noncomputable section

/-!
# Pascal prime-coordinate birth decoder

This finite decoder records where prime-indexed Pascal dials first appear.
The `Nat.Prime` predicate is part of the coordinate index and is not derived
here from a Pascal-only primality criterion.  The module is deliberately
prime-only: prime powers and von Mangoldt multiplicities belong to later
checkpoints.
-/

/-- A prime-indexed dial is visible when an inner coefficient has positive height. -/
def PascalPrimeDialVisibleInRow (p n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < n ∧ 0 < pascalPrimeDialHeight p n k

/-- A prime dial is visible in its own Pascal row. -/
theorem prime_pascalPrimeDialVisibleInRow_self
    {p : ℕ} (hp : p.Prime) :
    PascalPrimeDialVisibleInRow p p := by
  refine ⟨1, by omega, hp.one_lt, ?_⟩
  have h := prime_uniformPrimeDialHeight_self hp 1 (by omega) hp.one_lt
  omega

/-- Visibility of a prime dial cannot occur before its prime-indexed row. -/
private theorem prime_le_row_of_visible
    {p n : ℕ} (hp : p.Prime)
    (hvis : PascalPrimeDialVisibleInRow p n) : p ≤ n := by
  by_contra hpn
  have hnp : n < p := by omega
  obtain ⟨k, hkpos, hkn, hkheight⟩ := hvis
  have hz := pascalPrimeDialHeight_eq_zero_of_row_lt hp hnp (k := k)
  omega

/-- A prime dial has zero height throughout every earlier row. -/
theorem prime_not_pascalPrimeDialVisibleInRow_of_row_lt
    {p n : ℕ} (hp : p.Prime) (hnp : n < p) :
    ¬ PascalPrimeDialVisibleInRow p n := by
  rintro ⟨k, hkpos, hkn, hkheight⟩
  have hz := pascalPrimeDialHeight_eq_zero_of_row_lt hp hnp (k := k)
  omega

/-- Finite set of prime coordinates visible in one Pascal row. -/
noncomputable def pascalRowPrimeCoordinateSupport (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun p =>
    Nat.Prime p ∧ PascalPrimeDialVisibleInRow p n

/-- Membership in one-row support is exactly bounded prime visibility. -/
@[simp] theorem mem_pascalRowPrimeCoordinateSupport_iff
    {p n : ℕ} :
    p ∈ pascalRowPrimeCoordinateSupport n ↔
      p ≤ n ∧ Nat.Prime p ∧ PascalPrimeDialVisibleInRow p n := by
  simp [pascalRowPrimeCoordinateSupport]

/-- The prime coordinate occurs in the support of its own row. -/
theorem prime_mem_pascalRowPrimeCoordinateSupport_self
    {p : ℕ} (hp : p.Prime) :
    p ∈ pascalRowPrimeCoordinateSupport p := by
  rw [mem_pascalRowPrimeCoordinateSupport_iff]
  exact ⟨le_rfl, hp, prime_pascalPrimeDialVisibleInRow_self hp⟩

/-- Earlier rows contain no coordinate indexed by a larger prime. -/
theorem prime_not_mem_pascalRowPrimeCoordinateSupport_of_row_lt
    {p n : ℕ} (_hp : p.Prime) (hnp : n < p) :
    p ∉ pascalRowPrimeCoordinateSupport n := by
  rw [mem_pascalRowPrimeCoordinateSupport_iff]
  intro h
  omega

/-- Cumulative finite support through all rows up to `n`. -/
noncomputable def pascalPrimeCoordinateSupportUpTo (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun p =>
    Nat.Prime p ∧ ∃ d ≤ n, PascalPrimeDialVisibleInRow p d

/-- Cumulative support contains exactly the primes at most `n`. -/
theorem mem_pascalPrimeCoordinateSupportUpTo_iff
    {p n : ℕ} :
    p ∈ pascalPrimeCoordinateSupportUpTo n ↔ Nat.Prime p ∧ p ≤ n := by
  constructor
  · intro h
    simp only [pascalPrimeCoordinateSupportUpTo, Finset.mem_filter,
      Finset.mem_range] at h
    rcases h with ⟨hbound, hprime, d, hdn, hvis⟩
    exact ⟨hprime, by omega⟩
  · rintro ⟨hp, hpn⟩
    simp only [pascalPrimeCoordinateSupportUpTo, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨by omega, hp, p, by omega,
      prime_pascalPrimeDialVisibleInRow_self hp⟩

/-- New prime coordinates appearing at row `n`, as a finite difference. -/
def pascalPrimeCoordinateBirthSupport (n : ℕ) : Finset ℕ :=
  pascalPrimeCoordinateSupportUpTo n \
    pascalPrimeCoordinateSupportUpTo (n - 1)

/-- Birth support is `{n}` for prime `n` and empty otherwise. -/
theorem mem_pascalPrimeCoordinateBirthSupport_iff
    {p n : ℕ} :
    p ∈ pascalPrimeCoordinateBirthSupport n ↔ Nat.Prime p ∧ p = n := by
  rw [pascalPrimeCoordinateBirthSupport, Finset.mem_sdiff]
  rw [mem_pascalPrimeCoordinateSupportUpTo_iff,
    mem_pascalPrimeCoordinateSupportUpTo_iff]
  constructor
  · rintro ⟨⟨hp, hpn⟩, hprev⟩
    have hnot : ¬ p ≤ n - 1 := by
      intro h
      exact hprev ⟨hp, h⟩
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, rfl⟩
    constructor
    · exact ⟨hp, le_rfl⟩
    · intro h
      rcases h with ⟨_, hle⟩
      exact (Nat.not_le_of_lt (Nat.sub_lt hp.pos (by omega))) hle

/-- Singleton/empty normal form for the prime-coordinate birth event. -/
theorem pascalPrimeCoordinateBirthSupport_eq (n : ℕ) :
    pascalPrimeCoordinateBirthSupport n =
      if Nat.Prime n then {n} else ∅ := by
  ext p
  rw [mem_pascalPrimeCoordinateBirthSupport_iff]
  by_cases hp : Nat.Prime n
  · constructor
    · rintro ⟨_, rfl⟩
      simp [hp]
    · intro h
      have : p = n := by simpa [hp] using h
      simp [this, hp]
  · constructor
    · rintro ⟨hp', rfl⟩
      exact False.elim (hp hp')
    · intro h
      simp [hp] at h

/-- Boolean-valued natural indicator of a coordinate birth. -/
def pascalPrimeBirthIndicator (n p : ℕ) : ℕ :=
  if p ∈ pascalPrimeCoordinateBirthSupport n then 1 else 0

/-- A prime coordinate has unit indicator at its birth row. -/
@[simp] theorem pascalPrimeBirthIndicator_self
    {p : ℕ} (hp : p.Prime) :
    pascalPrimeBirthIndicator p p = 1 := by
  simp [pascalPrimeBirthIndicator,
    mem_pascalPrimeCoordinateBirthSupport_iff, hp]

/-- Prime-only logarithmic weight attached to a birth event. -/
noncomputable def pascalPrimeBirthLogWeight (n p : ℕ) : ℝ :=
  if p ∈ pascalPrimeCoordinateBirthSupport n then
    Real.log (p : ℝ)
  else 0

/-- Birth log weights are nonnegative. -/
theorem pascalPrimeBirthLogWeight_nonneg (n p : ℕ) :
    0 ≤ pascalPrimeBirthLogWeight n p := by
  by_cases h : p ∈ pascalPrimeCoordinateBirthSupport n
  · simp only [pascalPrimeBirthLogWeight, h, ↓reduceIte]
    obtain ⟨hp, rfl⟩ := (mem_pascalPrimeCoordinateBirthSupport_iff.mp h)
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · simp [pascalPrimeBirthLogWeight, h]

/-- At a prime's birth row, its log weight is `log p`. -/
@[simp] theorem pascalPrimeBirthLogWeight_self
    {p : ℕ} (hp : p.Prime) :
    pascalPrimeBirthLogWeight p p = Real.log (p : ℝ) := by
  simp [pascalPrimeBirthLogWeight,
    mem_pascalPrimeCoordinateBirthSupport_iff, hp]

/-- Sum of prime log weights born in one Pascal row. -/
noncomputable def pascalPrimeBirthLogMass (n : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateBirthSupport n, Real.log (p : ℝ)

/-- The row log mass is the prime-only Chebyshev-style increment. -/
theorem pascalPrimeBirthLogMass_eq (n : ℕ) :
    pascalPrimeBirthLogMass n =
      if Nat.Prime n then Real.log (n : ℝ) else 0 := by
  rw [pascalPrimeBirthLogMass, pascalPrimeCoordinateBirthSupport_eq]
  split_ifs <;> simp_all

/-- Successor rows update cumulative support by at most one new prime. -/
theorem pascalPrimeCoordinateSupportUpTo_succ (N : ℕ) :
    pascalPrimeCoordinateSupportUpTo (N + 1) =
      if Nat.Prime (N + 1) then
        insert (N + 1) (pascalPrimeCoordinateSupportUpTo N)
      else pascalPrimeCoordinateSupportUpTo N := by
  ext p
  rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
  by_cases hp : Nat.Prime (N + 1)
  · simp only [hp, ite_true, Finset.mem_insert, mem_pascalPrimeCoordinateSupportUpTo_iff]
    constructor
    · rintro ⟨hpp, hle⟩
      by_cases heq : p = N + 1
      · exact Or.inl heq
      · exact Or.inr ⟨hpp, by omega⟩
    · intro h
      rcases h with h | ⟨hpp, hle⟩
      · subst p; exact ⟨hp, by omega⟩
      · exact ⟨hpp, by omega⟩
  · simp only [hp, ite_false, mem_pascalPrimeCoordinateSupportUpTo_iff]
    constructor
    · rintro ⟨hpp, hle⟩
      by_cases heq : p = N + 1
      · subst p; exact False.elim (hp hpp)
      · exact ⟨hpp, by omega⟩
    · rintro ⟨hpp, hle⟩
      exact ⟨hpp, by omega⟩

end
end NumberTheory
end DkMath
