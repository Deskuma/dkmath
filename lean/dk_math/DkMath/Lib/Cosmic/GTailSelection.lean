/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail

#print "file: DkMath.Lib.Cosmic.GTailSelection"

/-!
# Finite selection of binomial terms

Indices denote powers of `x`; out-of-range indices are ignored.
This neutral semiring API adapts the canonical `GTail` family.
-/
open scoped BigOperators

namespace DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]


/-- Binomial term indexed by the power of `x`. -/
def selectedTerm (d k : ℕ) (x u : R) : R :=
  (Nat.choose d k : R) * x ^ k * u ^ (d - k)

/-- Body retains selected indices in `0..d`. -/
def selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) : R :=
  ∑ k ∈ (Finset.range (d + 1)).filter (fun k => k ∈ S), selectedTerm d k x u

/-- Gap retains unselected indices in `0..d`. -/
def selectedGap (d : ℕ) (S : Finset ℕ) (x u : R) : R :=
  ∑ k ∈ (Finset.range (d + 1)).filter (fun k => k ∉ S), selectedTerm d k x u


/-- Exact Big = Gap + Body balance. -/
theorem selectedGap_add_selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) :
    (x + u) ^ d = selectedGap d S x u + selectedBody d S x u := by
  rw [selectedGap, selectedBody,
    add_comm (∑ k ∈ (Finset.range (d + 1)).filter (fun k => k ∉ S),
      selectedTerm d k x u),
    Finset.sum_filter_add_sum_filter_not]
  simpa [selectedTerm, mul_assoc, mul_comm, mul_left_comm] using add_pow x u d

@[simp] theorem selectedBody_empty (d : ℕ) (x u : R) :
    selectedBody d ∅ x u = 0 := by
  simp [selectedBody]

@[simp] theorem selectedGap_empty (d : ℕ) (x u : R) :
    selectedGap d ∅ x u = (x + u) ^ d := by
  simpa using (selectedGap_add_selectedBody d ∅ x u).symm

@[simp] theorem selectedGap_full (d : ℕ) (x u : R) :
    selectedGap d (Finset.range (d + 1)) x u = 0 := by
  unfold selectedGap
  have h : (Finset.range (d + 1)).filter (fun k => k ∉ Finset.range (d + 1)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk
    exact not_not.mpr hk
  rw [h, Finset.sum_empty]

@[simp] theorem selectedBody_full (d : ℕ) (x u : R) :
    selectedBody d (Finset.range (d + 1)) x u = (x + u) ^ d := by
  simpa using (selectedGap_add_selectedBody d (Finset.range (d + 1)) x u).symm


/-- Bounded complement swaps Body and Gap, even for unbounded input selections. -/
theorem selectedBody_complement (d : ℕ) (S : Finset ℕ) (x u : R) :
    selectedBody d (Finset.range (d + 1) \ S) x u = selectedGap d S x u := by
  unfold selectedBody selectedGap
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- The other direction of bounded complement swap. -/
theorem selectedGap_complement (d : ℕ) (S : Finset ℕ) (x u : R) :
    selectedGap d (Finset.range (d + 1) \ S) x u = selectedBody d S x u := by
  unfold selectedBody selectedGap
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- A singleton in range extracts one binomial term. -/
theorem selectedBody_singleton (d k : ℕ) (x u : R) (hk : k ≤ d) :
    selectedBody d {k} x u = selectedTerm d k x u := by
  have h : (Finset.range (d + 1)).filter (fun j => j ∈ ({k} : Finset ℕ)) = {k} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [selectedBody, h, Finset.sum_singleton]


/-- Interval Gap is the canonical prefix. -/
theorem selectedGap_Ico (d r : ℕ) (x u : R) (hr : r ≤ d) :
    selectedGap d (Finset.Ico r (d + 1)) x u =
      ∑ j ∈ Finset.range r, (Nat.choose d j : R) * x ^ j * u ^ (d - j) := by
  have h : (Finset.range (d + 1)).filter (fun k => k ∉ Finset.Ico r (d + 1)) =
      Finset.range r := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [selectedGap, h]
  rfl

/-- Interval Body factors as the boundary power times canonical GTail. -/
theorem selectedBody_Ico (d r : ℕ) (x u : R) (hr : r ≤ d) :
    selectedBody d (Finset.Ico r (d + 1)) x u = x ^ r * GTail d r x u := by
  have h : (Finset.range (d + 1)).filter (fun k => k ∈ Finset.Ico r (d + 1)) =
      Finset.Ico r (d + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [selectedBody, h]
  have hu : r + (d + 1 - r) = d + 1 := by omega
  have hreindex :=
    Finset.sum_Ico_add' (fun k => selectedTerm d k x u) 0 (d + 1 - r) r
  simp only [Nat.zero_add, Nat.Ico_zero_eq_range] at hreindex
  rw [Nat.add_comm (d + 1 - r) r, hu] at hreindex
  rw [← hreindex]
  unfold GTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [selectedTerm, pow_add, Nat.add_comm, mul_assoc, mul_left_comm, mul_comm]

end DkMath.CosmicFormula
