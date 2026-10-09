/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailFactor
import DkMath.Lib.Cosmic.GTailPascal
import Mathlib.Data.Nat.ModEq

#print "file: DkMath.Lib.Cosmic.GTailTransport"

/-!
# Transport of selected Pascal terms

Terms enter and leave Body through differences of active index sets. Their
additive accounting holds over every commutative semiring, without subtraction
or cancellation. Big is conserved. Natural modular observations are conserved
only under explicit divisibility hypotheses on every moved term. Coefficient
gcd, support and factor shape are not asserted to be invariant.
-/

open scoped BigOperators

namespace DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]

/-- Terms entering Body when its selection changes from `S` to `T`. -/
def sumMovedIn (d : ℕ) (S T : Finset ℕ) (x u : R) : R :=
  ∑ k ∈ activeSelectedIndices d T \ activeSelectedIndices d S, selectedTerm d k x u

/-- Terms leaving Body when its selection changes from `S` to `T`. -/
def sumMovedOut (d : ℕ) (S T : Finset ℕ) (x u : R) : R :=
  sumMovedIn d T S x u

private theorem sum_selection_transport (A B : Finset ℕ) (f : ℕ → R) :
    (∑ k ∈ B, f k) + (∑ k ∈ A \ B, f k) =
      (∑ k ∈ A, f k) + (∑ k ∈ B \ A, f k) := by
  have hpart (C D : Finset ℕ) :
      (∑ k ∈ C, f k) = (∑ k ∈ C \ D, f k) + ∑ k ∈ C ∩ D, f k := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter C D), Finset.sdiff_union_inter]
  rw [hpart A B, hpart B A, Finset.inter_comm B A]
  ac_rfl

/-- Arbitrary Body transport accounts for both entering and departing terms. -/
theorem selectedBody_transport (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedBody d T x u + sumMovedOut d S T x u =
      selectedBody d S x u + sumMovedIn d S T x u :=
  sum_selection_transport (activeSelectedIndices d S) (activeSelectedIndices d T)
    (fun k => selectedTerm d k x u)

/-- Arbitrary Gap transport has the opposite movement accounting. -/
theorem selectedGap_transport (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedGap d T x u + sumMovedIn d S T x u =
      selectedGap d S x u + sumMovedOut d S T x u := by
  let U := Finset.range (d + 1)
  have hgap (V : Finset ℕ) :
      selectedGap d V x u = ∑ k ∈ U \ activeSelectedIndices d V, selectedTerm d k x u := by
    unfold selectedGap
    congr 1
    ext k
    simp only [U, Finset.mem_filter, Finset.mem_sdiff, mem_activeSelectedIndices,
      Finset.mem_range]
    simp only [Nat.lt_succ_iff]
    tauto
  have hdiff (V W : Finset ℕ) :
      (U \ activeSelectedIndices d V) \ (U \ activeSelectedIndices d W) =
        activeSelectedIndices d W \ activeSelectedIndices d V := by
    ext k
    simp only [U, Finset.mem_sdiff, mem_activeSelectedIndices, Finset.mem_range]
    simp only [Nat.lt_succ_iff]
    tauto
  rw [hgap S, hgap T]
  have h := sum_selection_transport (U \ activeSelectedIndices d S)
    (U \ activeSelectedIndices d T) (fun k => selectedTerm d k x u)
  rw [hdiff S T, hdiff T S] at h
  exact h

/-- Big balance is conserved, directly by the existing selection balance kernel. -/
theorem selected_balance_transport (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedGap d S x u + selectedBody d S x u =
      selectedGap d T x u + selectedBody d T x u := by
  rw [← selectedGap_add_selectedBody d S x u, ← selectedGap_add_selectedBody d T x u]

/-- Insert one new in-range term into Body, without duplicating other terms. -/
theorem selectedBody_insert (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hnot : k ∉ S) :
    selectedBody d (insert k S) x u = selectedBody d S x u + selectedTerm d k x u := by
  have hactive : activeSelectedIndices d (insert k S) = insert k (activeSelectedIndices d S) := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [hk]
    · simp [hj]
  change (∑ j ∈ activeSelectedIndices d (insert k S), selectedTerm d j x u) = _
  rw [hactive, Finset.sum_insert (by simp [hnot]), add_comm]
  rfl

/-- Inserting a Body term removes exactly that term from Gap. -/
theorem selectedGap_insert (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hnot : k ∉ S) :
    selectedGap d S x u = selectedGap d (insert k S) x u + selectedTerm d k x u := by
  have hfilter : (Finset.range (d + 1)).filter (fun j => j ∉ S) =
      insert k ((Finset.range (d + 1)).filter (fun j => j ∉ insert k S)) := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [hk, hnot, Finset.mem_range]
    · simp [hj]
  rw [selectedGap, hfilter, Finset.sum_insert (by simp), add_comm]
  rfl

/-- Erasing an in-range Body term records its departure additively. -/
theorem selectedBody_erase (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hmem : k ∈ S) :
    selectedBody d S x u = selectedBody d (S.erase k) x u + selectedTerm d k x u := by
  simpa only [Finset.insert_erase hmem] using
    selectedBody_insert d k (S.erase k) x u hk (Finset.notMem_erase k S)

/-- Erasing an in-range Body term moves it back into Gap. -/
theorem selectedGap_erase (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hmem : k ∈ S) :
    selectedGap d (S.erase k) x u = selectedGap d S x u + selectedTerm d k x u := by
  simpa only [Finset.insert_erase hmem] using
    selectedGap_insert d k (S.erase k) x u hk (Finset.notMem_erase k S)

/-- Repeated insertion of an already selected index is a no-op. -/
theorem selected_insert_of_mem (d k : ℕ) (S : Finset ℕ) (x u : R) (hmem : k ∈ S) :
    selectedBody d (insert k S) x u = selectedBody d S x u ∧
      selectedGap d (insert k S) x u = selectedGap d S x u := by
  simp only [Finset.insert_eq_of_mem hmem, and_self]

/-- Insertion outside the binomial range changes neither Body nor Gap. -/
theorem selected_insert_of_lt (d k : ℕ) (S : Finset ℕ) (x u : R) (hdk : d < k) :
    selectedBody d (insert k S) x u = selectedBody d S x u ∧
      selectedGap d (insert k S) x u = selectedGap d S x u := by
  have hb : (Finset.range (d + 1)).filter (fun j => j ∈ insert k S) =
      (Finset.range (d + 1)).filter (fun j => j ∈ S) := by
    ext j
    by_cases hj : j = k
    · subst j
      have hkrange : ¬ k < d + 1 := by omega
      simp [Finset.mem_range, hkrange]
    · simp [hj]
  have hg : (Finset.range (d + 1)).filter (fun j => j ∉ insert k S) =
      (Finset.range (d + 1)).filter (fun j => j ∉ S) := by
    ext j
    by_cases hj : j = k
    · subst j
      have hkrange : ¬ k < d + 1 := by omega
      simp [Finset.mem_range, hkrange]
    · simp [hj]
  simp only [selectedBody, selectedGap, hb, hg, and_self]

/-- Erasure outside the binomial range changes neither Body nor Gap. -/
theorem selected_erase_of_lt (d k : ℕ) (S : Finset ℕ) (x u : R) (hdk : d < k) :
    selectedBody d (S.erase k) x u = selectedBody d S x u ∧
      selectedGap d (S.erase k) x u = selectedGap d S x u := by
  have hb : (Finset.range (d + 1)).filter (fun j => j ∈ S.erase k) =
      (Finset.range (d + 1)).filter (fun j => j ∈ S) := by
    ext j
    by_cases hj : j = k
    · subst j
      have hkrange : ¬ k < d + 1 := by omega
      simp [Finset.mem_range, hkrange]
    · simp [hj]
  have hg : (Finset.range (d + 1)).filter (fun j => j ∉ S.erase k) =
      (Finset.range (d + 1)).filter (fun j => j ∉ S) := by
    ext j
    by_cases hj : j = k
    · subst j
      have hkrange : ¬ k < d + 1 := by omega
      simp [Finset.mem_range, hkrange]
    · simp [hj]
  simp only [selectedBody, selectedGap, hb, hg, and_self]

/--
Increasing the tail depth removes its first layers from the selected Body.
The layer index `r+k` is the power of `x`; canonical GTail supplies the split.
-/
theorem selectedBody_Ico_split_at (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d) :
    selectedBody d (Finset.Ico r (d + 1)) x u =
      x ^ r * (∑ k ∈ Finset.range (s - r),
        (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))) +
        selectedBody d (Finset.Ico s (d + 1)) x u := by
  rw [selectedBody_Ico d r x u (hrs.trans hsd), GTail_split_at d r s x u hrs hsd,
    mul_add, selectedBody_Ico d s x u hsd]
  have hexp : r + (s - r) = s := by omega
  rw [← mul_assoc, ← pow_add, hexp]

/--
Natural modular observations are conserved if every entering and departing
term is divisible by the modulus. The modulus may be zero.
-/
theorem selected_modEq_of_dvd_moved (d : ℕ) (S T : Finset ℕ) (x u m : ℕ)
    (hterms : ∀ k ∈ (activeSelectedIndices d T \ activeSelectedIndices d S) ∪
        (activeSelectedIndices d S \ activeSelectedIndices d T), m ∣ selectedTerm d k x u) :
    Nat.ModEq m (selectedBody d S x u) (selectedBody d T x u) ∧
      Nat.ModEq m (selectedGap d S x u) (selectedGap d T x u) := by
  have hin : m ∣ sumMovedIn d S T x u := by
    apply Finset.dvd_sum
    intro k hk
    exact hterms k (Finset.mem_union_left _ hk)
  have hout : m ∣ sumMovedOut d S T x u := by
    unfold sumMovedOut sumMovedIn
    apply Finset.dvd_sum
    intro k hk
    exact hterms k (Finset.mem_union_right _ hk)
  have hinzero := Nat.mod_eq_zero_of_dvd hin
  have houtzero := Nat.mod_eq_zero_of_dvd hout
  constructor
  · change selectedBody d S x u % m = selectedBody d T x u % m
    have h := congrArg (fun n : ℕ => n % m) (selectedBody_transport d S T x u)
    simpa only [Nat.add_mod, hinzero, houtzero, Nat.add_zero, Nat.mod_mod] using h.symm
  · change selectedGap d S x u % m = selectedGap d T x u % m
    have h := congrArg (fun n : ℕ => n % m) (selectedGap_transport d S T x u)
    simpa only [Nat.add_mod, hinzero, houtzero, Nat.add_zero, Nat.mod_mod] using h.symm

end DkMath.CosmicFormula
