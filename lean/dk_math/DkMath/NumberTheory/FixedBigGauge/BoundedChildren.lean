/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.PrimeGauge.GoldbachRefinement

/-! # Truncated child fibers

The real Goldbach interval sees only an initial segment of a modular child
fiber. More than two visible children suffice to avoid two raw holes, but
this condition must be supplied, and survival at other primes is separate.
-/

namespace DkMath.NumberTheory.FixedBigGauge

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.PrimeGauge
open DkMath.NumberTheory.StructuralArithmetic

/-- Actual child indices visible below the Goldbach boundary. -/
def boundedChildIndices (n M r q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j => r + j * M < n - 1)

@[simp] theorem mem_boundedChildIndices {n M r q j : ℕ} :
    j ∈ boundedChildIndices n M r q ↔ j < q ∧ r + j * M < n - 1 := by
  simp [boundedChildIndices]

/-- Visibility is downward closed in the child index. -/
theorem boundedChildIndices_initial {n M r q i j : ℕ}
    (hj : j ∈ boundedChildIndices n M r q) (hij : i ≤ j) :
    i ∈ boundedChildIndices n M r q := by
  obtain ⟨hjq, hjn⟩ := mem_boundedChildIndices.mp hj
  exact mem_boundedChildIndices.mpr
    ⟨lt_of_le_of_lt hij hjq, lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right M hij) r) hjn⟩

/-- Once the modulus reaches the interval width, only index zero can appear. -/
theorem boundedChildIndices_eq_zero_of_large_modulus {n M r q j : ℕ}
    (hM : n - 1 ≤ M) (hj : j ∈ boundedChildIndices n M r q) : j = 0 := by
  have h := (mem_boundedChildIndices.mp hj).2
  by_contra hj0
  have hj1 : 1 ≤ j := by omega
  have hMj : M ≤ j * M := by simpa using Nat.mul_le_mul_right M hj1
  omega

/-- For a fixed modulus and parent, one tick admits exactly a boundary equality. -/
theorem boundedChildIndices_succ {n M r q j : ℕ} (hn : 1 ≤ n) :
    j ∈ boundedChildIndices (n + 1) M r q ↔
      j ∈ boundedChildIndices n M r q ∨ (j < q ∧ r + j * M = n - 1) := by
  simp only [mem_boundedChildIndices]
  omega

/-- Exact conservation within the visible arc, for any finite forbidden set. -/
theorem bounded_survivors_add_reserved (n M r q : ℕ) (F : Finset ℕ) :
    (boundedChildIndices n M r q \ F).card +
      (boundedChildIndices n M r q ∩ F).card = (boundedChildIndices n M r q).card :=
  Finset.card_sdiff_add_card_inter _ _

/-- A visible arc with more than two seats cannot be covered by two holes. -/
theorem bounded_survivor_of_two_holes {n M r q : ℕ} {F : Finset ℕ}
    (hF : F.card ≤ 2) (hvisible : 2 < (boundedChildIndices n M r q).card) :
    (boundedChildIndices n M r q \ F).Nonempty := by
  apply Finset.card_pos.mp
  have h := Finset.le_card_sdiff F (boundedChildIndices n M r q)
  omega

/-- A concrete magnitude hypothesis supplies three visible seats. -/
theorem three_le_bounded_card {n M r q : ℕ}
    (hq : 2 < q) (hwidth : r + 2 * M < n - 1) :
    3 ≤ (boundedChildIndices n M r q).card := by
  have hsub : ({0, 1, 2} : Finset ℕ) ⊆ boundedChildIndices n M r q := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;>
      simp only [mem_boundedChildIndices] <;> omega
  have h := Finset.card_le_card hsub
  norm_num at h
  exact h

/-- The modular q-2 theorem becomes usable only with actual visible capacity. -/
theorem bounded_paired_survivor {n q r : ℕ} {S : Finset ℕ}
    (hS : KnownPrimeScales S) (hq : Nat.Prime q) (hfresh : q ∉ S)
    (hr : r < primeWorldModulus S) (hphase : ¬ q ∣ 2 * n)
    (hvisible : 2 < (boundedChildIndices n (primeWorldModulus S) r q).card) :
    (boundedChildIndices n (primeWorldModulus S) r q \
      pairedReservedChildIndices n S q r).Nonempty := by
  apply bounded_survivor_of_two_holes _ hvisible
  exact le_of_eq (pairedReservedChildIndices_card_eq_two hS hq hfresh hr hphase)

end DkMath.NumberTheory.FixedBigGauge
