/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.NumberTheory.Goldbach.Basic"

/-!
# Fixed-center degree-two GN fibers

The center condition is essential: representing an arbitrary odd integer by
`GN 2 1 u` says nothing about its reflected partner. Here `u = 0` is allowed,
so the fiber includes equal prime pairs and the endpoint `2 + 2 = 4`.
All subtraction identities over naturals carry the required order bound.
-/

namespace DkMath.NumberTheory

open CosmicFormulaBinom

/-- The usual prime-pair statement for the even target `2*n`. -/
def GoldbachPairAt (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n

/-- Prime pairs on a degree-two GN fiber with fixed center `n`. -/
def GoldbachGNFiberAt (n : ℕ) : Prop :=
  ∃ x u : ℕ, x + u = n ∧ Nat.Prime x ∧ Nat.Prime (GN 2 x u)

/-- The universal strong Goldbach proposition, without an assumed proof. -/
def StrongGoldbach : Prop := ∀ n : ℕ, 2 ≤ n → GoldbachPairAt n

/-- Conventional formulation over all even natural targets at least four. -/
def GoldbachEvenStatement : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Parametrizing an even target by its half preserves the conventional statement exactly. -/
theorem strongGoldbach_iff_evenStatement : StrongGoldbach ↔ GoldbachEvenStatement := by
  constructor
  · intro h N hEven hN
    obtain ⟨n, hn⟩ := hEven
    obtain ⟨p, q, hp, hq, hsum⟩ := h n (by omega)
    exact ⟨p, q, hp, hq, by omega⟩
  · intro h n hn
    exact h (2 * n) ⟨n, by omega⟩ (by omega)

/-- The degree-two GN row is the affine map `x + 2*u`. -/
theorem goldbach_GN_two (x u : ℕ) : GN 2 x u = x + 2 * u := by
  rw [GN_eq_sum]
  norm_num [Finset.sum_range_succ]
  ring

/-- Every odd target has a degree-two representation; primality is not needed. -/
theorem goldbach_odd_GN_representation (k : ℕ) : GN 2 1 k = 2 * k + 1 := by
  rw [goldbach_GN_two]
  omega

/-- Ordering the pair gives the exact fixed-center GN reformulation. -/
theorem goldbachPairAt_iff_gnFiberAt (n : ℕ) :
    GoldbachPairAt n ↔ GoldbachGNFiberAt n := by
  constructor
  · rintro ⟨p, q, hp, hq, hsum⟩
    have ordered : ∀ a b : ℕ, Nat.Prime a → Nat.Prime b →
        a + b = 2 * n → a ≤ b → GoldbachGNFiberAt n := by
      intro a b ha hb hab hle
      have han : a ≤ n := by omega
      refine ⟨a, n - a, by omega, ha, ?_⟩
      have heq : GN 2 a (n - a) = b := by rw [goldbach_GN_two]; omega
      rwa [heq]
    rcases le_total p q with h | h
    · exact ordered p q hp hq hsum h
    · exact ordered q p hq hp (by omega) h
  · rintro ⟨x, u, hn, hx, hgn⟩
    refine ⟨x, GN 2 x u, hx, hgn, ?_⟩
    rw [goldbach_GN_two]
    omega

/-- Admissible offsets keep both endpoints at least two, including `u=0`. -/
def goldbachOffsets (n : ℕ) : Finset ℕ := Finset.range (n - 1)

/-- On the admissible finite fiber, the left endpoint is at least two. -/
theorem goldbachOffset_bounds {n u : ℕ} (hu : u ∈ goldbachOffsets n) :
    u ≤ n ∧ 2 ≤ n - u ∧ 2 ≤ n + u ∧ n - u ≤ 2 * n ∧ n + u ≤ 2 * n := by
  simp only [goldbachOffsets, Finset.mem_range] at hu
  omega

/-- The complete finite search fiber is exactly the usual Goldbach pair statement. -/
theorem goldbachPairAt_iff_exists_offset (n : ℕ) :
    GoldbachPairAt n ↔
      ∃ u ∈ goldbachOffsets n, Nat.Prime (n - u) ∧ Nat.Prime (n + u) := by
  rw [goldbachPairAt_iff_gnFiberAt]
  constructor
  · rintro ⟨x, u, hn, hx, hgn⟩
    have hx2 := hx.two_le
    refine ⟨u, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · have : n - u = x := by omega
      rwa [this]
    · have : GN 2 x u = n + u := by rw [goldbach_GN_two]; omega
      rwa [this] at hgn
  · rintro ⟨u, hu, hl, hr⟩
    have hb := goldbachOffset_bounds hu
    refine ⟨n - u, u, by omega, hl, ?_⟩
    have : GN 2 (n - u) u = n + u := by rw [goldbach_GN_two]; omega
    rwa [this]

/-- The symmetric-offset endpoint in the strategy note is equivalent as well. -/
theorem goldbachPairAt_iff_exists_lt (n : ℕ) :
    GoldbachPairAt n ↔ ∃ u < n, Nat.Prime (n - u) ∧ Nat.Prime (n + u) := by
  rw [goldbachPairAt_iff_exists_offset]
  constructor
  · rintro ⟨u, hu, hl, hr⟩
    exact ⟨u, by have := goldbachOffset_bounds hu; omega, hl, hr⟩
  · rintro ⟨u, hu, hl, hr⟩
    exact ⟨u, Finset.mem_range.mpr (by have := hl.two_le; omega), hl, hr⟩

/-- The square Body is the product of the two canonical reflected factors. -/
def goldbachBody (n u : ℕ) : ℕ := (n - u) * (n + u)

/-- Exact Big = Body + Gap conservation on a natural-number square fiber. -/
theorem goldbachBody_add_gap {n u : ℕ} (hu : u ≤ n) :
    goldbachBody n u + u ^ 2 = n ^ 2 := by
  have hsub := Nat.sub_add_cancel hu
  unfold goldbachBody
  nlinarith

/-- Subtracting the gap yields the difference-of-squares Body identity. -/
theorem goldbachBody_eq_square_sub_square {n u : ℕ} (hu : u ≤ n) :
    goldbachBody n u = n ^ 2 - u ^ 2 := by
  have := goldbachBody_add_gap hu
  omega

/-- The arithmetic Body is the existing Cosmic Formula `BodyN` at degree two. -/
theorem goldbachBody_eq_BodyN {n u : ℕ} (hu : u ≤ n) :
    goldbachBody n u = BodyN 2 (n - u) u := by
  simp only [BodyN, goldbach_GN_two, goldbachBody]
  congr 1
  omega

end DkMath.NumberTheory
