/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailTransport
import Mathlib.Tactic.NormNum

#print "file: DkMathTest.CosmicFormula.GTailTransport"

/-!
# Regression tests for selection transport and guarded conservation

General semiring movement is separated from conditional natural congruence.
Endpoint insertion conserves Big but changes coefficient gcd and can change
both Body and Gap residues. No degree-seven norm factorization is used.
-/

open scoped BigOperators

namespace DkMathTest.GTailTransport

open DkMath.CosmicFormula

variable {R : Type*} [CommSemiring R]

-- Single insertion and its opposite Gap accounting at degree three.
example (x u : R) :
    selectedBody 3 (insert 0 {1}) x u = selectedBody 3 {1} x u + u ^ 3 ∧
      selectedGap 3 {1} x u = selectedGap 3 (insert 0 {1}) x u + u ^ 3 := by
  constructor
  · simpa only [selectedTerm, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      one_mul, mul_one, Nat.sub_zero] using
      selectedBody_insert 3 0 {1} x u (by decide) (by decide)
  · simpa only [selectedTerm, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      one_mul, mul_one, Nat.sub_zero] using
      selectedGap_insert 3 0 {1} x u (by decide) (by decide)

example (x u : R) :
    selectedBody 3 {1, 2} x u = selectedBody 3 (({1, 2} : Finset ℕ).erase 1) x u +
      3 * x * u ^ 2 ∧
    selectedGap 3 (({1, 2} : Finset ℕ).erase 1) x u = selectedGap 3 {1, 2} x u +
      3 * x * u ^ 2 := by
  constructor
  · simpa [selectedTerm] using selectedBody_erase 3 1 {1, 2} x u (by decide) (by decide)
  · simpa [selectedTerm] using selectedGap_erase 3 1 {1, 2} x u (by decide) (by decide)

-- Both entering and departing indices matter; the shared index 3 is retained.
example (x u : R) :
    selectedBody 5 {2, 3} x u + 5 * x * u ^ 4 =
      selectedBody 5 {1, 3} x u + 10 * x ^ 2 * u ^ 3 ∧
    selectedGap 5 {2, 3} x u + 10 * x ^ 2 * u ^ 3 =
      selectedGap 5 {1, 3} x u + 5 * x * u ^ 4 := by
  have hinset : activeSelectedIndices 5 {2, 3} \ activeSelectedIndices 5 {1, 3} = {2} := by
    decide
  have houtset : activeSelectedIndices 5 {1, 3} \ activeSelectedIndices 5 {2, 3} = {1} := by
    decide
  have hin : sumMovedIn 5 {1, 3} {2, 3} x u = 10 * x ^ 2 * u ^ 3 := by
    norm_num [sumMovedIn, hinset, selectedTerm, Nat.choose]
  have hout : sumMovedOut 5 {1, 3} {2, 3} x u = 5 * x * u ^ 4 := by
    norm_num [sumMovedOut, sumMovedIn, houtset, selectedTerm, Nat.choose]
  exact ⟨by simpa only [hin, hout] using selectedBody_transport 5 {1, 3} {2, 3} x u,
    by simpa only [hin, hout] using selectedGap_transport 5 {1, 3} {2, 3} x u⟩

example (d : ℕ) (S : Finset ℕ) (x u : R) :
    sumMovedIn d S S x u = 0 ∧ sumMovedOut d S S x u = 0 := by
  simp [sumMovedIn, sumMovedOut]

example (d : ℕ) (S : Finset ℕ) (x u : R) :
    selectedBody d S x u + sumMovedOut d S S x u =
      selectedBody d S x u + sumMovedIn d S S x u :=
  selectedBody_transport d S S x u

example (d : ℕ) (x u : R) :
    selectedGap d ∅ x u + selectedBody d ∅ x u =
      selectedGap d (Finset.range (d + 1)) x u +
        selectedBody d (Finset.range (d + 1)) x u :=
  selected_balance_transport d ∅ (Finset.range (d + 1)) x u

example (d : ℕ) (x u : R) :
    sumMovedOut d ∅ (Finset.range (d + 1)) x u = 0 ∧
      sumMovedIn d (Finset.range (d + 1)) ∅ x u = 0 := by
  simp [sumMovedIn, sumMovedOut, activeSelectedIndices]

example (d : ℕ) (x u : R) :
    sumMovedIn d ∅ (Finset.range (d + 1)) x u = (x + u) ^ d := by
  have h := selectedBody_transport d ∅ (Finset.range (d + 1)) x u
  simpa [sumMovedOut, sumMovedIn, activeSelectedIndices] using h.symm

example (x u : R) :
    selectedBody 3 (insert 2 {1, 2}) x u = selectedBody 3 {1, 2} x u ∧
      selectedGap 3 (insert 2 {1, 2}) x u = selectedGap 3 {1, 2} x u :=
  selected_insert_of_mem 3 2 {1, 2} x u (by decide)

example (x u : R) :
    selectedBody 3 (insert 100 {1}) x u = selectedBody 3 {1} x u ∧
      selectedGap 3 (insert 100 {1}) x u = selectedGap 3 {1} x u :=
  selected_insert_of_lt 3 100 {1} x u (by decide)

example (x u : R) :
    selectedBody 3 (({1, 100} : Finset ℕ).erase 100) x u = selectedBody 3 {1, 100} x u ∧
      selectedGap 3 (({1, 100} : Finset ℕ).erase 100) x u = selectedGap 3 {1, 100} x u :=
  selected_erase_of_lt 3 100 {1, 100} x u (by decide)

example (x u : R) :
    selectedBody 0 {0} x u = selectedBody 0 ∅ x u + 1 ∧
      selectedGap 0 ∅ x u = selectedGap 0 {0} x u + 1 := by
  constructor
  · simpa [selectedTerm] using selectedBody_insert 0 0 ∅ x u le_rfl (by simp)
  · simpa [selectedTerm] using selectedGap_insert 0 0 ∅ x u le_rfl (by simp)

example (x u : R) :
    selectedBody 0 (insert 1 {0}) x u = selectedBody 0 {0} x u ∧
      selectedGap 0 (insert 1 {0}) x u = selectedGap 0 {0} x u :=
  selected_insert_of_lt 0 1 {0} x u (by decide)

-- Vanishing moved terms leave the corresponding observed values unchanged.
example (u : R) : selectedBody 3 (insert 1 {2}) 0 u = selectedBody 3 {2} 0 u := by
  simpa [selectedTerm] using selectedBody_insert 3 1 {2} (0 : R) u (by decide) (by decide)

example (x : R) : selectedGap 3 {2} x 0 = selectedGap 3 (insert 1 {2}) x 0 := by
  simpa [selectedTerm] using selectedGap_insert 3 1 {2} x (0 : R) (by decide) (by decide)

example (x u : R) :
    selectedBody 3 (Finset.Ico 1 4) x u =
      x * (3 * u ^ 2) + selectedBody 3 (Finset.Ico 2 4) x u := by
  simpa [Finset.sum_range_succ] using selectedBody_Ico_split_at 3 1 2 x u (by decide) (by decide)

-- Endpoint insertion: conserved Big, but coefficient content changes from 7 to 1.
example : coeffGCD 7 (Finset.Ico 1 7) = 7 ∧ coeffGCD 7 (insert 0 (Finset.Ico 1 7)) = 1 := by
  exact ⟨coeffGCD_prime_interior 7 (by decide),
    coeffGCD_eq_one_of_zero_mem 7 (insert 0 (Finset.Ico 1 7)) (by simp)⟩

example (x u : R) :
    selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u =
      selectedBody 7 (Finset.Ico 1 7) x u + u ^ 7 ∧
    selectedGap 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u + u ^ 7 := by
  constructor
  · simpa [selectedTerm] using selectedBody_insert 7 0 (Finset.Ico 1 7) x u (by decide) (by simp)
  · simpa [selectedTerm] using selectedGap_insert 7 0 (Finset.Ico 1 7) x u (by decide) (by simp)

example (x u : R) :
    selectedGap 7 (Finset.Ico 1 7) x u + selectedBody 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u +
        selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u :=
  selected_balance_transport 7 (Finset.Ico 1 7) (insert 0 (Finset.Ico 1 7)) x u

-- Prime-divisible moved coefficients guard both modular observations.
example (p x u : ℕ) (hp : Nat.Prime p) :
    Nat.ModEq p (selectedBody p ∅ x u) (selectedBody p (Finset.Ico 1 p) x u) ∧
      Nat.ModEq p (selectedGap p ∅ x u) (selectedGap p (Finset.Ico 1 p) x u) := by
  apply selected_modEq_of_dvd_moved
  intro k hk
  have hkactive : k ∈ activeSelectedIndices p (Finset.Ico 1 p) := by
    simpa [activeSelectedIndices] using hk
  rw [activeSelectedIndices_interior] at hkactive
  obtain ⟨hkpos, hkp⟩ := Finset.mem_Ico.mp hkactive
  have hc := hp.dvd_choose_self (by omega : k ≠ 0) hkp
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _

-- Both entering and departing prime-divisible terms, at degree five.
example (x u : ℕ) :
    Nat.ModEq 5 (selectedBody 5 {1, 3} x u) (selectedBody 5 {2, 3} x u) ∧
      Nat.ModEq 5 (selectedGap 5 {1, 3} x u) (selectedGap 5 {2, 3} x u) := by
  apply selected_modEq_of_dvd_moved
  intro k hk
  have hmove : k = 1 ∨ k = 2 := by
    have hset : (activeSelectedIndices 5 {2, 3} \ activeSelectedIndices 5 {1, 3}) ∪
        (activeSelectedIndices 5 {1, 3} \ activeSelectedIndices 5 {2, 3}) = {1, 2} := by decide
    simpa only [hset, Finset.mem_insert, Finset.mem_singleton] using hk
  have hc : 5 ∣ Nat.choose 5 k := (show Nat.Prime 5 by decide).dvd_choose_self
    (by omega) (by omega)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _

-- Modulus zero is supported when moved terms themselves vanish.
example :
    Nat.ModEq 0 (selectedBody 3 {1} 0 0) (selectedBody 3 {2} 0 0) ∧
      Nat.ModEq 0 (selectedGap 3 {1} 0 0) (selectedGap 3 {2} 0 0) := by
  apply selected_modEq_of_dvd_moved
  decide

-- A moved unit endpoint violates the guard and changes both residues.
example : ¬ 7 ∣ selectedTerm 7 0 (1 : ℕ) 1 := by decide

example :
    ¬ Nat.ModEq 7 (selectedBody 7 (Finset.Ico 1 7) 1 1)
      (selectedBody 7 (insert 0 (Finset.Ico 1 7)) 1 1) ∧
    ¬ Nat.ModEq 7 (selectedGap 7 (Finset.Ico 1 7) 1 1)
      (selectedGap 7 (insert 0 (Finset.Ico 1 7)) 1 1) := by decide

end DkMathTest.GTailTransport

#print axioms DkMath.CosmicFormula.selectedBody_transport
#print axioms DkMath.CosmicFormula.selectedGap_transport
#print axioms DkMath.CosmicFormula.selected_balance_transport
#print axioms DkMath.CosmicFormula.selectedBody_insert
#print axioms DkMath.CosmicFormula.selectedGap_insert
#print axioms DkMath.CosmicFormula.selectedBody_erase
#print axioms DkMath.CosmicFormula.selectedGap_erase
#print axioms DkMath.CosmicFormula.selected_insert_of_mem
#print axioms DkMath.CosmicFormula.selected_insert_of_lt
#print axioms DkMath.CosmicFormula.selected_erase_of_lt
#print axioms DkMath.CosmicFormula.selectedBody_Ico_split_at
#print axioms DkMath.CosmicFormula.selected_modEq_of_dvd_moved
