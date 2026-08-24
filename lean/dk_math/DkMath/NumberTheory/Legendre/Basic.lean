/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import DkMath.NumberTheory.Primitive.SquareBody

#print "file: DkMath.NumberTheory.Legendre.Basic"

/-!
## Legendre.Basic

Stable square-cell, square-offset, support, and finite-window vocabulary.
This application layer depends on Primitive square-body semantics and remains
finite arithmetic; the refactor introduces no new Legendre proof.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-- The open interval between the consecutive squares anchored at `n`. -/
def SquareCell (n m : ℕ) : Prop :=
  n ^ 2 < m ∧ m < (n + 1) ^ 2

/-- The offset coordinates of a point in a consecutive-square cell. -/
def SquareOffset (n r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ 2 * n

/-- A fixed prime direction forbids an offset when it divides the anchored point. -/
def SquareOffsetForbiddenBy (n q r : ℕ) : Prop :=
  q ∣ n ^ 2 + r

/-- An offset is covered when at least one old bounded prime wave forbids it. -/
def SquareOffsetCovered (n r : ℕ) : Prop :=
  ∃ q, q ∈ primeScalesUpTo n ∧ SquareOffsetForbiddenBy n q r

/-- The finite-world cover predicate in explicit prime-and-bound form. -/
theorem squareOffsetCovered_iff_exists_prime_dvd
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      ∃ q, Nat.Prime q ∧ q ≤ n ∧ q ∣ n ^ 2 + r := by
  constructor
  · rintro ⟨q, hq, hdiv⟩
    exact ⟨q, (mem_primeScalesUpTo.mp hq).1,
      (mem_primeScalesUpTo.mp hq).2, hdiv⟩
  · rintro ⟨q, hq, hqle, hdiv⟩
    exact ⟨q, (mem_primeScalesUpTo.mpr ⟨hq, hqle⟩), hdiv⟩

/-- Support-disjointness is exactly failure of the old prime-wave cover. -/
theorem supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered
    {n r : ℕ} :
    SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) ↔
      ¬ SquareOffsetCovered n r := by
  constructor
  · intro hdisj hcovered
    rcases hcovered with ⟨q, hq, hdiv⟩
    exact supportDisjointFrom_primeScalesUpTo_iff.mp hdisj
      (mem_primeScalesUpTo.mp hq).1 (mem_primeScalesUpTo.mp hq).2 hdiv
  · intro hnot
    apply supportDisjointFrom_primeScalesUpTo_iff.mpr
    intro q hq hqle hdiv
    exact hnot ⟨q, mem_primeScalesUpTo.mpr ⟨hq, hqle⟩, hdiv⟩

/-- The canonical forbidden residue phase of a square anchor modulo `q`. -/
def squareAnchorForbiddenResidue (n q : ℕ) : ℕ :=
  (q - (n ^ 2 % q)) % q

/-- A fixed positive wave forbids exactly one residue phase of the offset. -/
theorem squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
    {n q r : ℕ} (hq : 0 < q) :
    SquareOffsetForbiddenBy n q r ↔
      r % q = squareAnchorForbiddenResidue n q := by
  have hnmod : n ^ 2 % q < q := Nat.mod_lt _ hq
  have hrmod : r % q < q := Nat.mod_lt _ hq
  rw [SquareOffsetForbiddenBy, Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  dsimp [squareAnchorForbiddenResidue]
  by_cases hzero : n ^ 2 % q = 0
  · simp [hzero, Nat.mod_eq_of_lt hrmod]
  · have hpos : 0 < n ^ 2 % q := Nat.pos_of_ne_zero hzero
    have hsub : q - n ^ 2 % q < q := by omega
    rw [Nat.mod_eq_of_lt hsub]
    by_cases hsum : n ^ 2 % q + r % q < q
    · rw [Nat.mod_eq_of_lt hsum]
      omega
    · have hqsum : q ≤
          n ^ 2 % q % q + r % q % q := by
        simpa [Nat.mod_eq_of_lt hnmod, Nat.mod_eq_of_lt hrmod] using hsum
      have hrel := Nat.add_mod_add_of_le_add_mod hqsum
      have hrel' :
          (n ^ 2 % q + r % q) % q + q =
            n ^ 2 % q + r % q := by
        simpa [Nat.mod_eq_of_lt hnmod, Nat.mod_eq_of_lt hrmod] using hrel
      omega

/-!
### PRIM-L005: square-anchor prime-wave overlaps

The next definitions keep the finite support of an offset explicit.  A support
cardinality counts distinct old prime waves; it is not a valuation and carries
no information about the depth of a prime-power divisor.
-/

/-- The old prime waves that cover one square offset. -/
noncomputable def squareOffsetPrimeSupport (n r : ℕ) : Finset ℕ := by
  classical
  exact (primeScalesUpTo n).filter (fun q => SquareOffsetForbiddenBy n q r)

/-- Membership in the offset support is bounded primality plus divisibility. -/
@[simp] theorem mem_squareOffsetPrimeSupport
    {n r q : ℕ} :
    q ∈ squareOffsetPrimeSupport n r ↔
      Nat.Prime q ∧ q ≤ n ∧ q ∣ n ^ 2 + r := by
  simp [squareOffsetPrimeSupport, SquareOffsetForbiddenBy, and_assoc]

/-- Ordinary square-offset coverage is exactly nonempty prime-wave support. -/
theorem squareOffsetCovered_iff_primeSupport_nonempty
    {n r : ℕ} :
    SquareOffsetCovered n r ↔ (squareOffsetPrimeSupport n r).Nonempty := by
  rw [squareOffsetCovered_iff_exists_prime_dvd]
  constructor
  · rintro ⟨q, hq, hqle, hdiv⟩
    exact ⟨q, mem_squareOffsetPrimeSupport.mpr ⟨hq, hqle, hdiv⟩⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (mem_squareOffsetPrimeSupport.mp hq).1,
      (mem_squareOffsetPrimeSupport.mp hq).2.1,
      (mem_squareOffsetPrimeSupport.mp hq).2.2⟩

/-- Coverage has positive support cardinality exactly when it is nonempty. -/
theorem squareOffsetCovered_iff_primeSupport_card_pos
    {n r : ℕ} :
    SquareOffsetCovered n r ↔ 0 < (squareOffsetPrimeSupport n r).card := by
  rw [squareOffsetCovered_iff_primeSupport_nonempty, Finset.card_pos]

/-- Two distinct old prime waves overlap exactly when their product divides the point. -/
theorem squareOffsetForbiddenBy_pair_iff_product_dvd
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    SquareOffsetForbiddenBy n p r ∧ SquareOffsetForbiddenBy n q r ↔
      p * q ∣ n ^ 2 + r := by
  constructor
  · rintro ⟨hpdiv, hqdiv⟩
    exact hp.dvd_mul_of_dvd_ne hpq hq hpdiv hqdiv
  · intro hprod
    exact ⟨dvd_trans (dvd_mul_right p q) hprod,
      dvd_trans (dvd_mul_left q p) hprod⟩

/-- A two-wave overlap is one forbidden residue phase modulo the product modulus. -/
theorem squareOffsetForbiddenBy_pair_iff_product_phase
    {n p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    SquareOffsetForbiddenBy n p r ∧ SquareOffsetForbiddenBy n q r ↔
      r % (p * q) = squareAnchorForbiddenResidue n (p * q) := by
  calc
    SquareOffsetForbiddenBy n p r ∧ SquareOffsetForbiddenBy n q r ↔
        p * q ∣ n ^ 2 + r :=
      squareOffsetForbiddenBy_pair_iff_product_dvd hp hq hpq
    _ ↔ SquareOffsetForbiddenBy n (p * q) r := by
      constructor
      · intro h
        exact h
      · intro h
        exact h
    _ ↔ r % (p * q) = squareAnchorForbiddenResidue n (p * q) :=
      squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
        (Nat.mul_pos hp.pos hq.pos)

/-- Whether an offset is covered by at least two distinct old prime waves.

This is a support-cardinality predicate: repeated divisibility by one prime
power is deliberately not counted as additional support.
-/
def SquareOffsetOverlap (n r : ℕ) : Prop :=
  2 ≤ (squareOffsetPrimeSupport n r).card

/-- Overlap has an exact witness consisting of two distinct support primes. -/
theorem squareOffsetOverlap_iff_exists_distinct_support
    {n r : ℕ} :
    SquareOffsetOverlap n r ↔
      ∃ p q, p ≠ q ∧ p ∈ squareOffsetPrimeSupport n r ∧
        q ∈ squareOffsetPrimeSupport n r := by
  constructor
  · intro hcard
    dsimp [SquareOffsetOverlap] at hcard
    have hpos : 0 < (squareOffsetPrimeSupport n r).card :=
      Nat.zero_lt_of_lt hcard
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hgt : 1 < (squareOffsetPrimeSupport n r).card := by omega
    obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne hgt p
    exact ⟨p, q, Ne.symm hqp, hp, hq⟩
  · rintro ⟨p, q, hpq, hp, hq⟩
    have hsubset : ({p, q} : Finset ℕ) ⊆ squareOffsetPrimeSupport n r := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp
      · exact hq
    have hcard := Finset.card_le_card hsubset
    change 2 ≤ (squareOffsetPrimeSupport n r).card
    have hpair : ({p, q} : Finset ℕ).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hpq
    rw [hpair] at hcard
    exact hcard

/-- Exact conversion between square-cell and square-offset coordinates. -/
theorem squareCell_iff_exists_squareOffset (n m : ℕ) :
    SquareCell n m ↔
      ∃ r, SquareOffset n r ∧ m = n ^ 2 + r := by
  have hsquare : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
    ring
  constructor
  · intro hcell
    dsimp [SquareCell] at hcell
    rcases hcell with ⟨hlo, hhi⟩
    have hbase : n ^ 2 ≤ m := by omega
    refine ⟨m - n ^ 2, ?_, ?_⟩
    · dsimp [SquareOffset]
      constructor <;> omega
    · rw [hsquare] at hhi
      omega
  · rintro ⟨r, hr, rfl⟩
    dsimp [SquareCell, SquareOffset] at hr ⊢
    rw [hsquare]
    omega

/--
The usual Legendre statement: every positive square interval contains a prime.
-/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ p, Nat.Prime p ∧ SquareCell n p

/--
The local provider form: an offset in every square cell avoids all prime
directions at most the anchor.
-/
def SquareAnchoredSupportEscape : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ r, SquareOffset n r ∧
          SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)

/-- The square-cell offsets as a finite interval. -/
def squareOffsets (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 (2 * n)

/-- Membership in `squareOffsets` is exactly the existing square-offset shell. -/
@[simp] theorem mem_squareOffsets
    {n r : ℕ} :
    r ∈ squareOffsets n ↔ SquareOffset n r := by
  simp [squareOffsets, SquareOffset]

/-- The square-offset window has exactly its geometric length many seats. -/
@[simp] theorem card_squareOffsets (n : ℕ) :
    (squareOffsets n).card = 2 * n := by
  simp [squareOffsets, Nat.card_Icc]


end DkMath.NumberTheory.Legendre
