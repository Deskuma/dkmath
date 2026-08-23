/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Interval
import DkMath.NumberTheory.Primitive.SquareBody

#print "file: DkMath.NumberTheory.Legendre"

/-!
## Legendre's conjecture as a square-anchored support escape

The formalization in this file separates the proved arithmetic framework from
the unresolved provider.  A support-free point in the open interval between
two consecutive squares is prime by the generic square-Body theorem.  The
universal existence of such a point is recorded explicitly as
`SquareAnchoredSupportEscape`; it is the Legendre-equivalent frontier and is
not assumed here.
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

/-!
### PRIM-L006: local wave seats

The following finite sets distinguish a single anchored wave from its prime
specialization.  Their cardinalities count seats in the local window, not
global residue density.
-/

/-- The square-window seats hit by an anchored wave of modulus `m`. -/
noncomputable def squareWaveOffsets (n m : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => SquareOffsetForbiddenBy n m r)

/-- Membership in a generic anchored wave is window membership plus divisibility. -/
@[simp] theorem mem_squareWaveOffsets
    {n m r : ℕ} :
    r ∈ squareWaveOffsets n m ↔
      SquareOffset n r ∧ m ∣ n ^ 2 + r := by
  simp [squareWaveOffsets, SquareOffsetForbiddenBy]

/-- The seats in the square window hit by one old prime wave. -/
noncomputable def squarePrimeWaveOffsets (n q : ℕ) : Finset ℕ :=
  squareWaveOffsets n q

/-- Membership in a prime wave seat set does not require primality of its modulus. -/
@[simp] theorem mem_squarePrimeWaveOffsets
    {n q r : ℕ} :
    r ∈ squarePrimeWaveOffsets n q ↔
      SquareOffset n r ∧ SquareOffsetForbiddenBy n q r := by
  simp [squarePrimeWaveOffsets, squareWaveOffsets]

/-- Two hits of a positive wave larger than the window must be the same seat. -/
theorem eq_of_mem_squareWaveOffsets_of_two_mul_lt_modulus
    {n m r₁ r₂ : ℕ}
    (hm : 0 < m)
    (hlarge : 2 * n < m)
    (hr₁ : r₁ ∈ squareWaveOffsets n m)
    (hr₂ : r₂ ∈ squareWaveOffsets n m) :
    r₁ = r₂ := by
  have hphase₁ :=
    (squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
      (n := n) (q := m) (r := r₁) hm).mp (mem_squareWaveOffsets.mp hr₁).2
  have hphase₂ :=
    (squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
      (n := n) (q := m) (r := r₂) hm).mp (mem_squareWaveOffsets.mp hr₂).2
  have hmod : r₁ ≡ r₂ [MOD m] := by
    rw [Nat.ModEq]
    exact hphase₁.trans hphase₂.symm
  have hr₁le : r₁ ≤ 2 * n := (mem_squareWaveOffsets.mp hr₁).1.2
  have hr₂le : r₂ ≤ 2 * n := (mem_squareWaveOffsets.mp hr₂).1.2
  apply hmod.eq_of_lt_of_lt
  · exact lt_of_le_of_lt hr₁le hlarge
  · exact lt_of_le_of_lt hr₂le hlarge

/-- A wave whose modulus is longer than the square window has at most one hit. -/
theorem card_squareWaveOffsets_le_one_of_two_mul_lt_modulus
    {n m : ℕ}
    (hm : 0 < m)
    (hlarge : 2 * n < m) :
    (squareWaveOffsets n m).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r₁ hr₁ r₂ hr₂
  exact eq_of_mem_squareWaveOffsets_of_two_mul_lt_modulus hm hlarge hr₁ hr₂

/-- The simultaneous seats of two old prime waves. -/
noncomputable def squarePrimePairOverlapOffsets (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n p r ∧ SquareOffsetForbiddenBy n q r)

/-- Membership in a pair-overlap seat set is simultaneous divisibility. -/
@[simp] theorem mem_squarePrimePairOverlapOffsets
    {n p q r : ℕ} :
    r ∈ squarePrimePairOverlapOffsets n p q ↔
      SquareOffset n r ∧ SquareOffsetForbiddenBy n p r ∧
        SquareOffsetForbiddenBy n q r := by
  simp [squarePrimePairOverlapOffsets]

/-- Distinct prime-wave overlap is exactly the product wave. -/
theorem squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    squarePrimePairOverlapOffsets n p q = squareWaveOffsets n (p * q) := by
  ext r
  rw [mem_squarePrimePairOverlapOffsets, mem_squareWaveOffsets]
  rw [squareOffsetForbiddenBy_pair_iff_product_dvd hp hq hpq]

/-- A large product modulus makes a distinct-prime overlap locally unique. -/
theorem card_squarePrimePairOverlapOffsets_le_one_of_two_mul_lt_product
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hlarge : 2 * n < p * q) :
    (squarePrimePairOverlapOffsets n p q).card ≤ 1 := by
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq]
  exact card_squareWaveOffsets_le_one_of_two_mul_lt_modulus
    (Nat.mul_pos hp.pos hq.pos) hlarge

/-- The finite subset of square offsets hit by an old prime wave. -/
noncomputable def coveredSquareOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (SquareOffsetCovered n)

/-- The finite subset of square offsets escaping every old prime wave. -/
noncomputable def escapingSquareOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => ¬ SquareOffsetCovered n r)

/-- Membership in the finite covered-offset set. -/
@[simp] theorem mem_coveredSquareOffsets
    {n r : ℕ} :
    r ∈ coveredSquareOffsets n ↔
      SquareOffset n r ∧ SquareOffsetCovered n r := by
  classical
  simp [coveredSquareOffsets, mem_squareOffsets]

/-- Membership in the finite escaping-offset set. -/
@[simp] theorem mem_escapingSquareOffsets
    {n r : ℕ} :
    r ∈ escapingSquareOffsets n ↔
      SquareOffset n r ∧ ¬ SquareOffsetCovered n r := by
  classical
  simp [escapingSquareOffsets, mem_squareOffsets]

/-- Escaping membership is the square-shell support-disjointness condition. -/
theorem mem_escapingSquareOffsets_iff_supportDisjointFrom
    {n r : ℕ} :
    r ∈ escapingSquareOffsets n ↔
      SquareOffset n r ∧
        SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r) := by
  rw [mem_escapingSquareOffsets,
    supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered]

/-- The bad local event that every square-shell offset is covered. -/
def SquareOffsetsFullyCovered (n : ℕ) : Prop :=
  ∀ r, SquareOffset n r → SquareOffsetCovered n r

/-- The total number of old-prime incidences across the square shell. -/
noncomputable def squareCoverIncidenceCount (n : ℕ) : ℕ :=
  ∑ r ∈ squareOffsets n, (squareOffsetPrimeSupport n r).card

/-- Full finite cover forces at least one old-prime incidence per offset. -/
theorem card_squareOffsets_le_squareCoverIncidenceCount_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    (squareOffsets n).card ≤ squareCoverIncidenceCount n := by
  classical
  unfold squareCoverIncidenceCount
  calc
    (squareOffsets n).card = ∑ r ∈ squareOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareOffsets n, (squareOffsetPrimeSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hcovered : SquareOffsetCovered n r :=
        hfull r (mem_squareOffsets.mp hr)
      exact (Finset.card_pos.mpr
        (squareOffsetCovered_iff_primeSupport_nonempty.mp hcovered))

/-- Full cover gives the incidence lower bound in the explicit window length. -/
theorem two_mul_le_squareCoverIncidenceCount_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    2 * n ≤ squareCoverIncidenceCount n := by
  rw [← card_squareOffsets]
  exact card_squareOffsets_le_squareCoverIncidenceCount_of_fullyCovered hfull

/-- The incidence ledger is exactly the transposed sum of local prime-wave seats. -/
theorem squareCoverIncidenceCount_eq_sum_primeWave_cards
    (n : ℕ) :
    squareCoverIncidenceCount n =
      ∑ q ∈ primeScalesUpTo n, (squarePrimeWaveOffsets n q).card := by
  classical
  unfold squareCoverIncidenceCount
  calc
    (∑ r ∈ squareOffsets n, (squareOffsetPrimeSupport n r).card) =
        ∑ r ∈ squareOffsets n, ∑ q ∈ primeScalesUpTo n,
          if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetPrimeSupport]
    _ = ∑ q ∈ primeScalesUpTo n, ∑ r ∈ squareOffsets n,
          if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ primeScalesUpTo n, (squarePrimeWaveOffsets n q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [squarePrimeWaveOffsets, squareWaveOffsets]

/-- The repeated-support excess beyond one mandatory incidence per seat. -/
noncomputable def squareCoverOverlapExcess (n : ℕ) : ℕ :=
  ∑ r ∈ squareOffsets n,
    ((squareOffsetPrimeSupport n r).card - 1)

/-- Under full cover, total incidence is window length plus overlap excess. -/
theorem squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverIncidenceCount n =
      2 * n + squareCoverOverlapExcess n := by
  classical
  unfold squareCoverIncidenceCount squareCoverOverlapExcess
  calc
    (∑ r ∈ squareOffsets n, (squareOffsetPrimeSupport n r).card) =
        ∑ r ∈ squareOffsets n,
          (1 + ((squareOffsetPrimeSupport n r).card - 1)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hcovered : SquareOffsetCovered n r :=
        hfull r (mem_squareOffsets.mp hr)
      have hpos : 0 < (squareOffsetPrimeSupport n r).card :=
        squareOffsetCovered_iff_primeSupport_card_pos.mp hcovered
      omega
    _ = (∑ r ∈ squareOffsets n, 1) +
          (∑ r ∈ squareOffsets n,
            ((squareOffsetPrimeSupport n r).card - 1)) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * n + ∑ r ∈ squareOffsets n,
          ((squareOffsetPrimeSupport n r).card - 1) := by
      simp [card_squareOffsets]

/-- Full cover is equivalent to equality of the covered and shell sets. -/
theorem squareOffsetsFullyCovered_iff_coveredSquareOffsets_eq
    {n : ℕ} :
    SquareOffsetsFullyCovered n ↔
      coveredSquareOffsets n = squareOffsets n := by
  constructor
  · intro hfull
    ext r
    constructor
    · intro hr
      exact mem_squareOffsets.mpr (mem_coveredSquareOffsets.mp hr).1
    · intro hr
      exact mem_coveredSquareOffsets.mpr ⟨mem_squareOffsets.mp hr, hfull r
        (mem_squareOffsets.mp hr)⟩
  · intro heq r hr
    have hmem : r ∈ coveredSquareOffsets n := by
      rw [heq]
      exact mem_squareOffsets.mpr hr
    exact (mem_coveredSquareOffsets.mp hmem).2

/-- Failure of full cover is equivalent to a nonempty escaping finite set. -/
theorem not_squareOffsetsFullyCovered_iff_escaping_nonempty
    {n : ℕ} :
    ¬ SquareOffsetsFullyCovered n ↔
      (escapingSquareOffsets n).Nonempty := by
  constructor
  · intro hnot
    classical
    by_contra hne
    apply hnot
    intro r hr
    by_contra hnotcovered
    apply hne
    exact ⟨r, mem_escapingSquareOffsets.mpr ⟨hr, hnotcovered⟩⟩
  · rintro ⟨r, hr⟩ hfull
    exact (mem_escapingSquareOffsets.mp hr).2 (hfull r
      (mem_escapingSquareOffsets.mp hr).1)

/-- The existing provider is exactly failure of complete finite square-wave cover. -/
theorem squareAnchoredSupportEscape_iff_not_fully_covered :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n := by
  constructor
  · intro hEscape n hn hfull
    obtain ⟨r, hr, hdisj⟩ := hEscape n hn
    exact (supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mp
      hdisj) (hfull r hr)
  · intro hCover n hn
    obtain ⟨r, hr⟩ :=
      (not_squareOffsetsFullyCovered_iff_escaping_nonempty.mp (hCover n hn))
    have hmem := mem_escapingSquareOffsets.mp hr
    exact ⟨r, hmem.1,
      (supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered.mpr hmem.2)⟩

/--
The semantic square-escape provider expanded into its elementary bounded-prime
form.  This is a rewrite theorem, not an existence theorem.
-/
theorem squareAnchoredSupportEscape_iff_raw :
    SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n →
        ∃ r, SquareOffset n r ∧
          ∀ ⦃q : ℕ⦄, Nat.Prime q → q ≤ n → ¬ q ∣ n ^ 2 + r := by
  constructor
  · intro hEscape n hn
    obtain ⟨r, hr, hdisj⟩ := hEscape n hn
    exact ⟨r, hr, supportDisjointFrom_primeScalesUpTo_iff.mp hdisj⟩
  · intro hRaw n hn
    obtain ⟨r, hr, hdisj⟩ := hRaw n hn
    exact ⟨r, hr, supportDisjointFrom_primeScalesUpTo_iff.mpr hdisj⟩

/-- A support-free offset produces a prime point in its square cell. -/
theorem prime_of_squareAnchoredSupportEscape
    {n r : ℕ} (hn : 0 < n) (hr : SquareOffset n r)
    (hdisj : SupportDisjointFrom (primeScalesUpTo n) (n ^ 2 + r)) :
    Nat.Prime (n ^ 2 + r) := by
  have hnSq : 1 ≤ n ^ 2 := by nlinarith
  have hm : 1 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    omega
  have hmUpper : n ^ 2 + r ≤ squareBody n := by
    dsimp [SquareOffset] at hr
    dsimp [squareBody]
    omega
  exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody hm hmUpper hdisj

/-- The support-escape provider gives the usual Legendre witness. -/
theorem legendreConjecture_of_squareAnchoredSupportEscape
    (hEscape : SquareAnchoredSupportEscape) :
    LegendreConjecture := by
  intro n hn
  obtain ⟨r, hr, hdisj⟩ := hEscape n hn
  refine ⟨n ^ 2 + r, prime_of_squareAnchoredSupportEscape hn hr hdisj, ?_⟩
  exact (squareCell_iff_exists_squareOffset n (n ^ 2 + r)).2 ⟨r, hr, rfl⟩

/--
The usual conjecture is exactly the square-anchored support-escape provider.

The reverse implication uses only the fact that a prime divisor of a prime is
the prime itself, together with `q ≤ n < p` inside the square cell.  Thus this
theorem is a reduction, not a proof of the provider.
-/
theorem legendreConjecture_iff_squareAnchoredSupportEscape :
    LegendreConjecture ↔ SquareAnchoredSupportEscape := by
  constructor
  · intro hLegendre n hn
    obtain ⟨p, hp, hcell⟩ := hLegendre n hn
    obtain ⟨r, hr, hrEq⟩ :=
      (squareCell_iff_exists_squareOffset n p).1 hcell
    refine ⟨r, hr, ?_⟩
    apply supportDisjointFrom_primeScalesUpTo_iff.mpr
    intro q hq hqle hqdiv
    have hqdiv' : q ∣ p := by simpa [hrEq] using hqdiv
    have hqp : q = p :=
      ((Nat.dvd_prime hp).mp hqdiv').resolve_left hq.ne_one
    have hpLower : n ^ 2 < p := by
      rw [hrEq]
      dsimp [SquareOffset] at hr
      omega
    have hnSq : n ≤ n ^ 2 := by nlinarith
    rw [hqp] at hqle
    omega
  · exact legendreConjecture_of_squareAnchoredSupportEscape

/-- The Legendre conjecture is equivalently the finite square-offset escape frontier. -/
theorem legendreConjecture_iff_squareOffsets_not_fully_covered :
    LegendreConjecture ↔
      ∀ n : ℕ, 0 < n → ¬ SquareOffsetsFullyCovered n :=
  legendreConjecture_iff_squareAnchoredSupportEscape.trans
    squareAnchoredSupportEscape_iff_not_fully_covered

end DkMath.NumberTheory.Legendre
