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

/-- Exact occupancy of a positive anchored wave by endpoint quotient difference.

The proof counts the translated multiples `n ^ 2 + r` in the half-open local
interval `(n ^ 2, n ^ 2 + 2 * n]`.  Thus this is an actual local hit count,
not a density assertion for a full period.
-/
theorem card_squareWaveOffsets_eq_div_sub_div
    {n m : ℕ}
    (_hm : 0 < m) :
    (squareWaveOffsets n m).card =
      (n ^ 2 + 2 * n) / m - (n ^ 2) / m := by
  classical
  let t : Finset ℕ :=
    (Finset.Ioc (n ^ 2) (n ^ 2 + 2 * n)).filter (fun x => m ∣ x)
  have hcard : (squareWaveOffsets n m).card = t.card := by
    apply Finset.card_bij (fun r _ => n ^ 2 + r)
    · intro r hr
      have hr' := mem_squareWaveOffsets.mp hr
      change n ^ 2 + r ∈
        (Finset.Ioc (n ^ 2) (n ^ 2 + 2 * n)).filter (fun x => m ∣ x)
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      dsimp [SquareOffset] at hr'
      exact ⟨⟨by omega, by omega⟩, hr'.2⟩
    · intro r₁ hr₁ r₂ hr₂ hEq
      omega
    · intro x hx
      have hx' := (Finset.mem_filter.mp (show x ∈ t from hx))
      rcases hx' with ⟨hxIoc, hxdvd⟩
      have hxIoc' : n ^ 2 < x ∧ x ≤ n ^ 2 + 2 * n :=
        Finset.mem_Ioc.mp hxIoc
      have hxle : n ^ 2 ≤ x := le_of_lt hxIoc'.1
      refine ⟨x - n ^ 2, ?_, ?_⟩
      · apply mem_squareWaveOffsets.mpr
        constructor
        · dsimp [SquareOffset]
          constructor <;> omega
        · simpa [Nat.add_sub_of_le hxle] using hxdvd
      · exact Nat.add_sub_of_le hxle
  have ht : t =
      (Finset.Ioc 0 (n ^ 2 + 2 * n)).filter (fun x => m ∣ x) \
        (Finset.Ioc 0 (n ^ 2)).filter (fun x => m ∣ x) := by
    ext x
    simp [t, Finset.mem_Ioc]
    omega
  have hsub :
      (Finset.Ioc 0 (n ^ 2)).filter (fun x => m ∣ x) ⊆
        (Finset.Ioc 0 (n ^ 2 + 2 * n)).filter (fun x => m ∣ x) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIoc, hxdvd⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ?_, hxdvd⟩
    have hxIoc' := Finset.mem_Ioc.mp hxIoc
    exact ⟨hxIoc'.1, by omega⟩
  calc
    (squareWaveOffsets n m).card = t.card := hcard
    _ = ((Finset.Ioc 0 (n ^ 2 + 2 * n)).filter (fun x => m ∣ x)).card -
        ((Finset.Ioc 0 (n ^ 2)).filter (fun x => m ∣ x)).card := by
      rw [ht, Finset.card_sdiff_of_subset hsub]
    _ = (n ^ 2 + 2 * n) / m - (n ^ 2) / m := by
      rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]

/-!
### PRIM-L008: square-anchor carries

PRIM-L007 counts local hits by a difference of endpoint quotients.  The next
definition isolates the only correction beyond the complete periods in the
window: the anchor remainder and the window-length remainder can cross one
modulus boundary.  This is a finite arithmetic correction, not a density or
valuation quantity.
-/

/-- The one-bit boundary carry contributed by a square anchor and a modulus. -/
def squareWaveCarry (n m : ℕ) : ℕ :=
  ((n ^ 2 % m) + ((2 * n) % m)) / m

/-- The square-anchor carry is at most one for every positive modulus. -/
theorem squareWaveCarry_le_one
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m ≤ 1 := by
  unfold squareWaveCarry
  have hsum : n ^ 2 % m + (2 * n) % m < 2 * m := by
    have h₁ := Nat.mod_lt (n ^ 2) hm
    have h₂ := Nat.mod_lt (2 * n) hm
    omega
  have hlt : (n ^ 2 % m + (2 * n) % m) / m < 2 := by
    apply (Nat.div_lt_iff_lt_mul hm).2
    simpa [Nat.mul_comm] using hsum
  omega

/-- The carry is one exactly when the two remainders cross the modulus. -/
theorem squareWaveCarry_eq_one_iff
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m = 1 ↔
      m ≤ (n ^ 2 % m) + ((2 * n) % m) := by
  unfold squareWaveCarry
  have hsum : n ^ 2 % m + (2 * n) % m < 2 * m := by
    have h₁ := Nat.mod_lt (n ^ 2) hm
    have h₂ := Nat.mod_lt (2 * n) hm
    omega
  constructor
  · intro hcarry
    by_contra hnot
    have hlt : n ^ 2 % m + (2 * n) % m < m := lt_of_not_ge hnot
    have hzero := Nat.div_eq_of_lt hlt
    omega
  · intro hcross
    exact Nat.div_eq_of_lt_le (by simpa using hcross) (by omega)

/-- The carry vanishes exactly when the remainder sum stays below the modulus. -/
theorem squareWaveCarry_eq_zero_iff
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m = 0 ↔
      (n ^ 2 % m) + ((2 * n) % m) < m := by
  unfold squareWaveCarry
  constructor
  · intro hzero
    by_contra hnot
    have hcross : m ≤ n ^ 2 % m + (2 * n) % m := le_of_not_gt hnot
    have hone : (n ^ 2 % m + (2 * n) % m) / m = 1 := by
      have hsum : n ^ 2 % m + (2 * n) % m < 2 * m := by
        have h₁ := Nat.mod_lt (n ^ 2) hm
        have h₂ := Nat.mod_lt (2 * n) hm
        omega
      exact Nat.div_eq_of_lt_le (by simpa using hcross) (by omega)
    omega
  · intro hlt
    exact Nat.div_eq_of_lt hlt

/-- Exact local occupancy as complete periods plus the square-anchor carry. -/
theorem card_squareWaveOffsets_eq_div_add_carry
    {n m : ℕ} (hm : 0 < m) :
    (squareWaveOffsets n m).card =
      (2 * n) / m + squareWaveCarry n m := by
  rw [card_squareWaveOffsets_eq_div_sub_div hm]
  unfold squareWaveCarry
  by_cases hcross : m ≤ (n ^ 2 % m) + ((2 * n) % m)
  · rw [Nat.add_div_eq_of_le_mod_add_mod hcross hm]
    have hsum : n ^ 2 % m + (2 * n) % m < 2 * m := by
      have h₁ := Nat.mod_lt (n ^ 2) hm
      have h₂ := Nat.mod_lt (2 * n) hm
      omega
    have hcarry :
        (n ^ 2 % m + (2 * n) % m) / m = 1 :=
      Nat.div_eq_of_lt_le (by simpa [Nat.one_mul] using hcross) (by omega)
    rw [hcarry]
    have hle : n ^ 2 / m ≤ n ^ 2 / m + 2 * n / m :=
      Nat.le_add_right _ _
    omega
  · have hlt : n ^ 2 % m + (2 * n) % m < m := lt_of_not_ge hcross
    rw [Nat.add_div_eq_of_add_mod_lt hlt, Nat.div_eq_of_lt hlt]
    simp [Nat.add_comm]

/-- A modulus dividing the anchor has no boundary carry. -/
theorem squareWaveCarry_eq_zero_of_dvd_anchor
    {n m : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    squareWaveCarry n m = 0 := by
  have hsq : m ∣ n ^ 2 := dvd_pow hmn (by decide)
  have hlen : m ∣ 2 * n := dvd_mul_of_dvd_right hmn 2
  rw [squareWaveCarry_eq_zero_iff hm]
  rw [Nat.mod_eq_zero_of_dvd hsq, Nat.mod_eq_zero_of_dvd hlen]
  exact hm

/-- A divisor of the anchor contributes exactly the complete-period count. -/
theorem card_squareWaveOffsets_eq_div_of_dvd_anchor
    {n m : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    (squareWaveOffsets n m).card = (2 * n) / m := by
  rw [card_squareWaveOffsets_eq_div_add_carry hm,
    squareWaveCarry_eq_zero_of_dvd_anchor hm hmn, Nat.add_zero]

/-! The preceding carry identities specialize directly to the prime waves
used by the finite square-cover ledger. -/

/-- Exact prime-wave occupancy as complete periods plus the anchor carry. -/
theorem card_squarePrimeWaveOffsets_eq_div_add_carry
    {n q : ℕ} (hq : Nat.Prime q) :
    (squarePrimeWaveOffsets n q).card =
      (2 * n) / q + squareWaveCarry n q := by
  simpa [squarePrimeWaveOffsets] using
    (card_squareWaveOffsets_eq_div_add_carry (n := n) (m := q) hq.pos)

/-- A prime divisor of the anchor contributes no carry. -/
theorem card_squarePrimeWaveOffsets_eq_div_of_dvd_anchor
    {n q : ℕ} (hq : Nat.Prime q) (hqn : q ∣ n) :
    (squarePrimeWaveOffsets n q).card = (2 * n) / q := by
  simpa [squarePrimeWaveOffsets] using
    (card_squareWaveOffsets_eq_div_of_dvd_anchor (n := n) (m := q)
      hq.pos hqn)

/-- Exact occupancy for an old prime wave, specialized from the generic formula. -/
theorem card_squarePrimeWaveOffsets_eq_div_sub_div
    {n q : ℕ}
    (hq : Nat.Prime q) :
    (squarePrimeWaveOffsets n q).card =
      (n ^ 2 + 2 * n) / q - (n ^ 2) / q := by
  simpa [squarePrimeWaveOffsets] using
    (card_squareWaveOffsets_eq_div_sub_div (n := n) (m := q) hq.pos)

/-- The local occupancy is bounded below by the number of complete wave periods. -/
theorem div_le_card_squareWaveOffsets
    {n m : ℕ}
    (hm : 0 < m) :
    (2 * n) / m ≤ (squareWaveOffsets n m).card := by
  rw [card_squareWaveOffsets_eq_div_sub_div hm]
  have hdiv := Nat.add_div_le_add_div (n ^ 2) (2 * n) m
  omega

/-- The local occupancy is at most one more than the number of complete periods. -/
theorem card_squareWaveOffsets_le_div_add_one
    {n m : ℕ}
    (hm : 0 < m) :
    (squareWaveOffsets n m).card ≤ (2 * n) / m + 1 := by
  rw [card_squareWaveOffsets_eq_div_sub_div hm]
  rw [Nat.add_div hm]
  split <;> simp [Nat.add_assoc, Nat.add_comm]

/-- Every old prime wave has at least two hits in the anchored square window. -/
theorem two_le_card_squarePrimeWaveOffsets_of_mem
    {n q : ℕ}
    (hq : q ∈ primeScalesUpTo n) :
    2 ≤ (squarePrimeWaveOffsets n q).card := by
  have hq' := mem_primeScalesUpTo.mp hq
  have htwo_div : 2 ≤ (2 * n) / q := by
    apply (Nat.le_div_iff_mul_le hq'.1.pos).2
    omega
  exact htwo_div.trans
    (div_le_card_squareWaveOffsets hq'.1.pos)

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

/-- Exact quotient occupancy of a distinct-prime pair overlap. -/
theorem card_squarePrimePairOverlapOffsets_eq_div_sub_div
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    (squarePrimePairOverlapOffsets n p q).card =
      (n ^ 2 + 2 * n) / (p * q) - (n ^ 2) / (p * q) := by
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq]
  exact card_squareWaveOffsets_eq_div_sub_div (Nat.mul_pos hp.pos hq.pos)

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

/-- The complete-period part of the finite prime-wave incidence ledger. -/
noncomputable def squareCoverBaselineIncidence (n : ℕ) : ℕ :=
  ∑ q ∈ primeScalesUpTo n, (2 * n) / q

/-- The total one-bit anchor-carry contribution of the old prime waves. -/
noncomputable def squareAnchorCarryCount (n : ℕ) : ℕ :=
  ∑ q ∈ primeScalesUpTo n, squareWaveCarry n q

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

/-- The incidence ledger splits exactly into baseline periods and carries. -/
theorem squareCoverIncidenceCount_eq_baseline_add_carry
    (n : ℕ) :
    squareCoverIncidenceCount n =
      squareCoverBaselineIncidence n + squareAnchorCarryCount n := by
  rw [squareCoverIncidenceCount_eq_sum_primeWave_cards]
  unfold squareCoverBaselineIncidence squareAnchorCarryCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact card_squarePrimeWaveOffsets_eq_div_add_carry
    (mem_primeScalesUpTo.mp hq).1

/-- The carry ledger is bounded by the number of old prime scales. -/
theorem squareAnchorCarryCount_le_card_primeScalesUpTo (n : ℕ) :
    squareAnchorCarryCount n ≤ (primeScalesUpTo n).card := by
  unfold squareAnchorCarryCount
  calc
    (∑ q ∈ primeScalesUpTo n, squareWaveCarry n q) ≤
        ∑ q ∈ primeScalesUpTo n, 1 := by
      apply Finset.sum_le_sum
      intro q hq
      exact squareWaveCarry_le_one (mem_primeScalesUpTo.mp hq).1.pos
    _ = (primeScalesUpTo n).card := by simp

/-- The total incidence count written entirely as endpoint quotient differences. -/
theorem squareCoverIncidenceCount_eq_sum_div_sub_div
    (n : ℕ) :
    squareCoverIncidenceCount n =
      ∑ q ∈ primeScalesUpTo n,
        ((n ^ 2 + 2 * n) / q - (n ^ 2) / q) := by
  rw [squareCoverIncidenceCount_eq_sum_primeWave_cards]
  apply Finset.sum_congr rfl
  intro q hq
  exact card_squarePrimeWaveOffsets_eq_div_sub_div
    (mem_primeScalesUpTo.mp hq).1

/-- Full cover yields the quotient-arithmetic incidence necessary condition. -/
theorem two_mul_le_sum_div_sub_div_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    2 * n ≤
      ∑ q ∈ primeScalesUpTo n,
        ((n ^ 2 + 2 * n) / q - (n ^ 2) / q) := by
  rw [← squareCoverIncidenceCount_eq_sum_div_sub_div]
  exact two_mul_le_squareCoverIncidenceCount_of_fullyCovered hfull

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

/-- Under full cover, baseline plus carries equals the exact incidence budget. -/
theorem squareCoverBaselineIncidence_add_squareAnchorCarryCount_eq_two_mul_add_overlapExcess_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n =
      2 * n + squareCoverOverlapExcess n := by
  calc
    squareCoverBaselineIncidence n + squareAnchorCarryCount n =
        squareCoverIncidenceCount n :=
      (squareCoverIncidenceCount_eq_baseline_add_carry n).symm
    _ = 2 * n + squareCoverOverlapExcess n :=
      squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered hfull

/-!
### PRIM-L009: pair-overlap budget

The second-order ledger records unordered pairs of distinct old prime
directions.  It is a finite double count of support intersections: an offset
with support size `k` contributes `k - 1` to the overlap excess and
`Nat.choose k 2` to the pair ledger.  No higher-order inclusion-exclusion or
analytic estimate is used here.
-/

/-- Canonical ordered representatives of the unordered pairs in a finite set. -/
private def upperPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.1 < pair.2)

/-- The reverse orientation of the canonical representatives. -/
private def lowerPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter (fun pair => pair.2 < pair.1)

/-- Canonical pair representatives have the expected binomial cardinality. -/
private theorem card_upperPairs_eq_choose (s : Finset ℕ) :
    (upperPairs s).card = Nat.choose s.card 2 := by
  classical
  have hswap : (lowerPairs s).card = (upperPairs s).card := by
    apply Finset.card_bij (fun pair _ => (pair.2, pair.1))
    · intro pair hpair
      have hpair' := Finset.mem_filter.mp hpair
      have hdiag := Finset.mem_offDiag.mp hpair'.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_offDiag.mpr
          ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩,
        hpair'.2⟩
    · intro pair₁ hpair₁ pair₂ hpair₂ heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro pair hpair
      refine ⟨(pair.2, pair.1), ?_, ?_⟩
      · have hpair' := Finset.mem_filter.mp hpair
        have hdiag := Finset.mem_offDiag.mp hpair'.1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_offDiag.mpr
            ⟨hdiag.2.1, hdiag.1, Ne.symm hdiag.2.2⟩,
          hpair'.2⟩
      · rfl
  have hneg : s.offDiag.filter (fun pair => ¬ pair.1 < pair.2) =
      lowerPairs s := by
    ext pair
    simp [lowerPairs]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s.offDiag) (p := fun pair : ℕ × ℕ => pair.1 < pair.2)
  rw [hneg] at hsplit
  have hsum : (upperPairs s).card + (lowerPairs s).card = s.offDiag.card := by
    simpa [upperPairs] using hsplit
  have htwice : 2 * (upperPairs s).card = s.offDiag.card := by
    omega
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one,
    ← Finset.offDiag_card]
  exact (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two htwice.symm).symm

/-- One offset's unordered support-pair multiplicity. -/
noncomputable def squareOffsetPrimePairMultiplicity (n r : ℕ) : ℕ :=
  Nat.choose (squareOffsetPrimeSupport n r).card 2

/-- A support of size `k` has at least `k - 1` unordered distinct pairs. -/
theorem primeSupport_sub_one_le_pairMultiplicity
    {n r : ℕ} :
    (squareOffsetPrimeSupport n r).card - 1 ≤
      squareOffsetPrimePairMultiplicity n r := by
  unfold squareOffsetPrimePairMultiplicity
  rw [Nat.choose_two_right]
  by_cases hsmall : (squareOffsetPrimeSupport n r).card ≤ 1
  · omega
  · have hlarge : 2 ≤ (squareOffsetPrimeSupport n r).card := by omega
    apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right ((squareOffsetPrimeSupport n r).card - 1) hlarge)

/-- One copy of every unordered pair of old prime directions. -/
noncomputable def squarePrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeScalesUpTo n).product (primeScalesUpTo n)).filter
    (fun pair => pair.1 < pair.2)

/-- Membership in the canonical old-prime pair set. -/
@[simp] theorem mem_squarePrimePairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ Nat.Prime q ∧ q ≤ n ∧ p < q := by
  simp [squarePrimePairs, and_assoc, and_left_comm, and_comm]

/-- Pair-overlap incidence count over canonical old-prime pairs. -/
noncomputable def squarePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimePairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The pair ledger is exactly the sum of local unordered support-pair counts. -/
theorem squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ r ∈ squareOffsets n,
        squareOffsetPrimePairMultiplicity n r := by
  classical
  have hpairset (r : ℕ) :
      (squarePrimePairs n).filter
          (fun pair => pair.1 ∈ squareOffsetPrimeSupport n r ∧
            pair.2 ∈ squareOffsetPrimeSupport n r) =
        upperPairs (squareOffsetPrimeSupport n r) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [squarePrimePairs, upperPairs, mem_squareOffsetPrimeSupport,
      and_assoc, and_left_comm, and_comm]
    omega
  unfold squarePrimePairOverlapCount
  calc
    (∑ pair ∈ squarePrimePairs n,
        (squarePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squarePrimePairs n, ∑ r ∈ squareOffsets n,
          if SquareOffsetForbiddenBy n pair.1 r ∧
              SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      simp [squarePrimePairOverlapOffsets, squareOffsets]
    _ = ∑ r ∈ squareOffsets n, ∑ pair ∈ squarePrimePairs n,
          if SquareOffsetForbiddenBy n pair.1 r ∧
              SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareOffsets n,
          ((squarePrimePairs n).filter
            (fun pair => pair.1 ∈ squareOffsetPrimeSupport n r ∧
              pair.2 ∈ squareOffsetPrimeSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext pair
      rcases pair with ⟨p, q⟩
      simp [mem_squareOffsetPrimeSupport, SquareOffsetForbiddenBy]
      aesop
    _ = ∑ r ∈ squareOffsets n,
          (upperPairs (squareOffsetPrimeSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hpairset]
    _ = ∑ r ∈ squareOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold squareOffsetPrimePairMultiplicity
      exact card_upperPairs_eq_choose _

/-- Pair multiplicity dominates the repeated-support excess at every offset. -/
theorem squareCoverOverlapExcess_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareCoverOverlapExcess n ≤ squarePrimePairOverlapCount n := by
  rw [squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity]
  unfold squareCoverOverlapExcess
  apply Finset.sum_le_sum
  intro r hr
  exact primeSupport_sub_one_le_pairMultiplicity

/-- Full cover obeys the second-order pair-overlap budget constraint. -/
theorem baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n + squarePrimePairOverlapCount n := by
  calc
    squareCoverBaselineIncidence n + squareAnchorCarryCount n =
        2 * n + squareCoverOverlapExcess n :=
      squareCoverBaselineIncidence_add_squareAnchorCarryCount_eq_two_mul_add_overlapExcess_of_fullyCovered
        hfull
    _ ≤ 2 * n + squarePrimePairOverlapCount n := by
      exact Nat.add_le_add_left
        (squareCoverOverlapExcess_le_squarePrimePairOverlapCount n) (2 * n)

/-- Pair overlap reduces to exact occupancy of the product-modulus wave. -/
theorem squarePrimePairOverlapCount_eq_sum_product_div_add_carry
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ pair ∈ squarePrimePairs n,
        ((2 * n) / (pair.1 * pair.2) +
          squareWaveCarry n (pair.1 * pair.2)) := by
  unfold squarePrimePairOverlapCount
  apply Finset.sum_congr rfl
  intro pair hpair
  rcases pair with ⟨p, q⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq⟩
  simpa using
    (show (squarePrimePairOverlapOffsets n p q).card =
        (2 * n) / (p * q) + squareWaveCarry n (p * q) by
      rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq
        hpq.ne]
      exact card_squareWaveOffsets_eq_div_add_carry
        (Nat.mul_pos hp.pos hq.pos))

/-- The full-cover pair budget in its expanded product-wave arithmetic form. -/
theorem baseline_add_carry_le_two_mul_add_sum_product_div_add_carry_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n +
        ∑ pair ∈ squarePrimePairs n,
          ((2 * n) / (pair.1 * pair.2) +
            squareWaveCarry n (pair.1 * pair.2)) := by
  rw [← squarePrimePairOverlapCount_eq_sum_product_div_add_carry]
  exact baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered hfull

/-!
### PRIM-L010: near/far pair localization

The second-order pair ledger is now localized by the product modulus relative
to the actual square-window length `2 * n`.  Near products retain a complete
period baseline, while far products have no complete period and can contribute
only their one-bit square-anchor carry.  This is finite localization, not an
analytic estimate or a claim of independence between prime directions.
-/

/-- Canonical old-prime pairs whose product period fits in the square window. -/
noncomputable def squarePrimeNearPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => pair.1 * pair.2 ≤ 2 * n)

/-- Canonical old-prime pairs whose product period exceeds the square window. -/
noncomputable def squarePrimeFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => 2 * n < pair.1 * pair.2)

/-- Membership in the near canonical pair set. -/
@[simp] theorem mem_squarePrimeNearPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeNearPairs n ↔
      (p, q) ∈ squarePrimePairs n ∧ p * q ≤ 2 * n := by
  simp [squarePrimeNearPairs]

/-- Membership in the far canonical pair set. -/
@[simp] theorem mem_squarePrimeFarPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeFarPairs n ↔
      (p, q) ∈ squarePrimePairs n ∧ 2 * n < p * q := by
  simp [squarePrimeFarPairs]

/-- The near and far pair sets form an exact disjoint partition. -/
theorem squarePrimeNearPairs_union_farPairs (n : ℕ) :
    squarePrimeNearPairs n ∪ squarePrimeFarPairs n = squarePrimePairs n := by
  ext pair
  rcases pair with ⟨p, q⟩
  by_cases hnear : p * q ≤ 2 * n
  · simp [squarePrimeNearPairs, squarePrimeFarPairs, hnear]
  · have hfar : 2 * n < p * q := lt_of_not_ge hnear
    simp [squarePrimeNearPairs, squarePrimeFarPairs, hnear, hfar]

/-- Near and far canonical pairs are disjoint. -/
theorem disjoint_squarePrimeNearPairs_squarePrimeFarPairs (n : ℕ) :
    Disjoint (squarePrimeNearPairs n) (squarePrimeFarPairs n) := by
  rw [Finset.disjoint_left]
  intro pair hnear hfar
  have hnear' := mem_squarePrimeNearPairs.mp hnear
  have hfar' := mem_squarePrimeFarPairs.mp hfar
  omega

/-- The near-pair contribution to the second-order overlap ledger. -/
noncomputable def squarePrimeNearPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The far-pair contribution to the second-order overlap ledger. -/
noncomputable def squarePrimeFarPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeFarPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

/-- The total pair ledger splits exactly into near and far contributions. -/
theorem squarePrimePairOverlapCount_eq_near_add_far
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairOverlapCount n +
        squarePrimeFarPairOverlapCount n := by
  unfold squarePrimePairOverlapCount squarePrimeNearPairOverlapCount
    squarePrimeFarPairOverlapCount
  rw [show squarePrimePairs n =
      squarePrimeNearPairs n ∪ squarePrimeFarPairs n by
        symm
        exact squarePrimeNearPairs_union_farPairs n]
  rw [Finset.sum_union (disjoint_squarePrimeNearPairs_squarePrimeFarPairs n)]

/-- A wave longer than the window has occupancy equal to its anchor carry. -/
theorem card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus
    {n m : ℕ}
    (hm : 0 < m)
    (hfar : 2 * n < m) :
    (squareWaveOffsets n m).card = squareWaveCarry n m := by
  rw [card_squareWaveOffsets_eq_div_add_carry hm,
    Nat.div_eq_of_lt hfar, Nat.zero_add]

/-- A far canonical prime pair has overlap occupancy equal to its product carry. -/
theorem card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far
    {n p q : ℕ}
    (hpq : (p, q) ∈ squarePrimeFarPairs n) :
    (squarePrimePairOverlapOffsets n p q).card =
      squareWaveCarry n (p * q) := by
  rcases mem_squarePrimeFarPairs.mp hpq with ⟨hpair, hfar⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq'⟩
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq'.ne]
  exact card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus
    (Nat.mul_pos hp.pos hq.pos) hfar

/-- Far pairs whose product wave actually hits the square window. -/
noncomputable def squarePrimeActiveFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimeFarPairs n).filter
    (fun pair => squareWaveCarry n (pair.1 * pair.2) = 1)

/-- Membership in the active far-pair set. -/
@[simp] theorem mem_squarePrimeActiveFarPairs
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeActiveFarPairs n ↔
      (p, q) ∈ squarePrimeFarPairs n ∧
        squareWaveCarry n (p * q) = 1 := by
  simp [squarePrimeActiveFarPairs]

/-- The far overlap ledger is exactly the number of active far pairs. -/
theorem squarePrimeFarPairOverlapCount_eq_card_activeFarPairs
    (n : ℕ) :
    squarePrimeFarPairOverlapCount n =
      (squarePrimeActiveFarPairs n).card := by
  unfold squarePrimeFarPairOverlapCount
  calc
    (∑ pair ∈ squarePrimeFarPairs n,
        (squarePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squarePrimeFarPairs n,
          squareWaveCarry n (pair.1 * pair.2) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far hpair
    _ = ∑ pair ∈ squarePrimeFarPairs n,
          if squareWaveCarry n (pair.1 * pair.2) = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hmem := mem_squarePrimeFarPairs.mp hpair
      rcases mem_squarePrimePairs.mp hmem.1 with ⟨hp, hpn, hq, hqn, hpq⟩
      have hle := squareWaveCarry_le_one (n := n)
        (m := pair.1 * pair.2) (Nat.mul_pos hp.pos hq.pos)
      split_ifs with hcarry
      · simp [hcarry]
      · have hzero : squareWaveCarry n (pair.1 * pair.2) = 0 := by
          omega
        simp [hzero]
    _ = (squarePrimeActiveFarPairs n).card := by
      rw [Finset.sum_boole]
      rfl

/-- A far pair is active exactly when its product wave is nonempty. -/
theorem mem_squarePrimeActiveFarPairs_iff_overlap_nonempty
    {n p q : ℕ} :
    (p, q) ∈ squarePrimeActiveFarPairs n ↔
      (p, q) ∈ squarePrimeFarPairs n ∧
        (squarePrimePairOverlapOffsets n p q).Nonempty := by
  constructor
  · intro hactive
    refine ⟨(mem_squarePrimeActiveFarPairs.mp hactive).1, ?_⟩
    apply Finset.card_pos.mp
    rw [card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far
      (mem_squarePrimeActiveFarPairs.mp hactive).1]
    exact (mem_squarePrimeActiveFarPairs.mp hactive).2 ▸ Nat.zero_lt_one
  · rintro ⟨hfar, hnonempty⟩
    rw [mem_squarePrimeActiveFarPairs]
    refine ⟨hfar, ?_⟩
    have hpos := Finset.card_pos.mpr hnonempty
    have hcard := card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far hfar
    have hpair := mem_squarePrimeFarPairs.mp hfar
    rcases mem_squarePrimePairs.mp hpair.1 with ⟨hp, hpn, hq, hqn, hpq⟩
    have hle := squareWaveCarry_le_one (n := n)
      (m := p * q) (Nat.mul_pos hp.pos hq.pos)
    omega

/-- The complete product-period baseline contributed by near pairs. -/
noncomputable def squarePrimeNearPairBaseline (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (2 * n) / (pair.1 * pair.2)

/-- The product-wave carry count contributed by near pairs. -/
noncomputable def squarePrimeNearPairCarryCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    squareWaveCarry n (pair.1 * pair.2)

/-- Near-pair overlap is exactly baseline periods plus product carries. -/
theorem squarePrimeNearPairOverlapCount_eq_baseline_add_carry
    (n : ℕ) :
    squarePrimeNearPairOverlapCount n =
      squarePrimeNearPairBaseline n + squarePrimeNearPairCarryCount n := by
  unfold squarePrimeNearPairOverlapCount squarePrimeNearPairBaseline
    squarePrimeNearPairCarryCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair hpair
  rcases pair with ⟨p, q⟩
  rcases mem_squarePrimeNearPairs.mp hpair with ⟨hprimepair, hnear⟩
  rcases mem_squarePrimePairs.mp hprimepair with ⟨hp, hpn, hq, hqn, hpq⟩
  simpa using
    (show (squarePrimePairOverlapOffsets n p q).card =
        (2 * n) / (p * q) + squareWaveCarry n (p * q) by
      rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq
        hpq.ne]
      exact card_squareWaveOffsets_eq_div_add_carry
        (Nat.mul_pos hp.pos hq.pos))

/-- Every near pair contributes at least one product-wave overlap seat. -/
theorem one_le_card_squarePrimePairOverlapOffsets_of_mem_near
    {n p q : ℕ}
    (hpq : (p, q) ∈ squarePrimeNearPairs n) :
    1 ≤ (squarePrimePairOverlapOffsets n p q).card := by
  rcases mem_squarePrimeNearPairs.mp hpq with ⟨hpair, hnear⟩
  rcases mem_squarePrimePairs.mp hpair with ⟨hp, hpn, hq, hqn, hpq'⟩
  rw [squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product hp hq hpq'.ne,
    card_squareWaveOffsets_eq_div_add_carry (Nat.mul_pos hp.pos hq.pos)]
  have hdiv : 1 ≤ (2 * n) / (p * q) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hq.pos)).2
    simpa using hnear
  omega

/-- The complete pair ledger has near baseline, near carry, and active far parts. -/
theorem squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairBaseline n +
        squarePrimeNearPairCarryCount n +
          (squarePrimeActiveFarPairs n).card := by
  rw [squarePrimePairOverlapCount_eq_near_add_far,
    squarePrimeNearPairOverlapCount_eq_baseline_add_carry,
    squarePrimeFarPairOverlapCount_eq_card_activeFarPairs]

/-- Full cover in the localized near/far second-order normal form. -/
theorem baseline_add_carry_le_two_mul_add_near_far_pair_budget_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n +
        (squarePrimeNearPairBaseline n +
          squarePrimeNearPairCarryCount n +
            (squarePrimeActiveFarPairs n).card) := by
  calc
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
        2 * n + squarePrimePairOverlapCount n :=
      baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered hfull
    _ = 2 * n +
        (squarePrimeNearPairBaseline n +
          squarePrimeNearPairCarryCount n +
            (squarePrimeActiveFarPairs n).card) := by
      rw [squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar]

/-!
### PRIM-L011: anchor-divisor and coprime-offset localization

This checkpoint partitions old prime directions according to whether they
divide the square anchor `n`.  A divisor direction has zero forbidden phase
and therefore sees exactly the offsets divisible by that prime.  Consequently
the coprime part of the square window can only be covered by nondivisor
directions.  This is an exact finite partition, not a density estimate or a
statement about p-adic depth.
-/

/-- Old prime directions that divide the square anchor. -/
noncomputable def squareAnchorDivisorPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (primeScalesUpTo n).filter (fun q => q ∣ n)

/-- Old prime directions that do not divide the square anchor. -/
noncomputable def squareAnchorNondivisorPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (primeScalesUpTo n).filter (fun q => ¬ q ∣ n)

/-- Membership in the anchor-divisor prime world. -/
@[simp] theorem mem_squareAnchorDivisorPrimes
    {n q : ℕ} :
    q ∈ squareAnchorDivisorPrimes n ↔
      Nat.Prime q ∧ q ≤ n ∧ q ∣ n := by
  simp [squareAnchorDivisorPrimes, and_assoc]

/-- Membership in the anchor-nondivisor prime world. -/
@[simp] theorem mem_squareAnchorNondivisorPrimes
    {n q : ℕ} :
    q ∈ squareAnchorNondivisorPrimes n ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n := by
  simp [squareAnchorNondivisorPrimes, and_assoc]

/-- The divisor and nondivisor prime worlds partition the old prime scales. -/
theorem squareAnchorDivisorPrimes_union_nondivisorPrimes (n : ℕ) :
    squareAnchorDivisorPrimes n ∪ squareAnchorNondivisorPrimes n =
      primeScalesUpTo n := by
  ext q
  by_cases hqn : q ∣ n
  · simp [squareAnchorDivisorPrimes, squareAnchorNondivisorPrimes, hqn]
  · simp [squareAnchorDivisorPrimes, squareAnchorNondivisorPrimes, hqn]

/-- The two anchor prime classes are disjoint. -/
theorem disjoint_squareAnchorDivisorPrimes_squareAnchorNondivisorPrimes
    (n : ℕ) :
    Disjoint (squareAnchorDivisorPrimes n) (squareAnchorNondivisorPrimes n) := by
  rw [Finset.disjoint_left]
  intro q hdiv hnondiv
  exact (mem_squareAnchorNondivisorPrimes.mp hnondiv).2.2
    (mem_squareAnchorDivisorPrimes.mp hdiv).2.2

/-- A divisor prime wave is equivalent to divisibility of the offset itself. -/
theorem squareOffsetForbiddenBy_iff_dvd_offset_of_dvd_anchor
    {n q r : ℕ}
    (hqn : q ∣ n) :
    SquareOffsetForbiddenBy n q r ↔ q ∣ r := by
  have hsq : q ∣ n ^ 2 := dvd_pow hqn (by decide)
  rw [SquareOffsetForbiddenBy]
  rw [← Nat.dvd_add_iff_right hsq]

/-- A prime dividing the anchor has zero forbidden square-anchor phase. -/
theorem squareAnchorForbiddenResidue_eq_zero_of_dvd_anchor
    {n q : ℕ}
    (_hq : 0 < q)
    (hqn : q ∣ n) :
    squareAnchorForbiddenResidue n q = 0 := by
  unfold squareAnchorForbiddenResidue
  rw [Nat.mod_eq_zero_of_dvd (dvd_pow hqn (by decide))]
  simp

/-- A prime not dividing the anchor has nonzero forbidden square-anchor phase. -/
theorem squareAnchorForbiddenResidue_ne_zero_of_prime_not_dvd_anchor
    {n q : ℕ}
    (hq : Nat.Prime q)
    (hqn : ¬ q ∣ n) :
    squareAnchorForbiddenResidue n q ≠ 0 := by
  intro hres
  have hforbid : SquareOffsetForbiddenBy n q 0 := by
    rw [squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue hq.pos]
    simp [hres]
  have hsq : q ∣ n ^ 2 := by
    simpa [SquareOffsetForbiddenBy] using hforbid
  exact hqn (hq.dvd_of_dvd_pow hsq)

/-- Coverage by an old prime direction dividing the anchor. -/
def SquareOffsetCoveredByAnchorDivisorPrime (n r : ℕ) : Prop :=
  ∃ q, q ∈ squareAnchorDivisorPrimes n ∧
    SquareOffsetForbiddenBy n q r

/-- Coverage by an old prime direction not dividing the anchor. -/
def SquareOffsetCoveredByAnchorNondivisorPrime (n r : ℕ) : Prop :=
  ∃ q, q ∈ squareAnchorNondivisorPrimes n ∧
    SquareOffsetForbiddenBy n q r

/-- Ordinary coverage splits exactly into divisor and nondivisor coverage. -/
theorem squareOffsetCovered_iff_anchorDivisor_or_nondivisor
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      SquareOffsetCoveredByAnchorDivisorPrime n r ∨
        SquareOffsetCoveredByAnchorNondivisorPrime n r := by
  constructor
  · rintro ⟨q, hq, hforbid⟩
    by_cases hqn : q ∣ n
    · left
      exact ⟨q, mem_squareAnchorDivisorPrimes.mpr
        ⟨(mem_primeScalesUpTo.mp hq).1,
          (mem_primeScalesUpTo.mp hq).2, hqn⟩, hforbid⟩
    · right
      exact ⟨q, mem_squareAnchorNondivisorPrimes.mpr
        ⟨(mem_primeScalesUpTo.mp hq).1,
          (mem_primeScalesUpTo.mp hq).2, hqn⟩, hforbid⟩
  · rintro (hdiv | hnondiv)
    · rcases hdiv with ⟨q, hq, hforbid⟩
      have hq' := mem_squareAnchorDivisorPrimes.mp hq
      exact ⟨q, mem_primeScalesUpTo.mpr ⟨hq'.1, hq'.2.1⟩, hforbid⟩
    · rcases hnondiv with ⟨q, hq, hforbid⟩
      have hq' := mem_squareAnchorNondivisorPrimes.mp hq
      exact ⟨q, mem_primeScalesUpTo.mpr ⟨hq'.1, hq'.2.1⟩, hforbid⟩

/-- Divisor-prime coverage is exactly failure of coprimality with the anchor. -/
theorem squareOffsetCoveredByAnchorDivisorPrime_iff_not_coprime
    {n r : ℕ}
    (hn : 0 < n) :
    SquareOffsetCoveredByAnchorDivisorPrime n r ↔
      ¬ Nat.Coprime n r := by
  constructor
  · rintro ⟨q, hq, hforbid⟩
    have hq' := mem_squareAnchorDivisorPrimes.mp hq
    apply Nat.Prime.not_coprime_iff_dvd.mpr
    exact ⟨q, hq'.1, hq'.2.2,
      (squareOffsetForbiddenBy_iff_dvd_offset_of_dvd_anchor hq'.2.2).mp
        hforbid⟩
  · intro hnot
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨q, hq, hqn, hqr⟩
    have hqle : q ≤ n := Nat.le_of_dvd hn hqn
    refine ⟨q, mem_squareAnchorDivisorPrimes.mpr ⟨hq, hqle, hqn⟩, ?_⟩
    exact (squareOffsetForbiddenBy_iff_dvd_offset_of_dvd_anchor hqn).mpr hqr

/-- A coprime offset can only be covered by an anchor-nondivisor prime. -/
theorem squareOffsetCovered_iff_anchorNondivisor_of_coprime
    {n r : ℕ}
    (hn : 0 < n)
    (hcop : Nat.Coprime n r) :
    SquareOffsetCovered n r ↔
      SquareOffsetCoveredByAnchorNondivisorPrime n r := by
  rw [squareOffsetCovered_iff_anchorDivisor_or_nondivisor]
  constructor
  · rintro (hdiv | hnondiv)
    · exact False.elim
        ((squareOffsetCoveredByAnchorDivisorPrime_iff_not_coprime hn).mp hdiv hcop)
    · exact hnondiv
  · intro hnondiv
    exact Or.inr hnondiv

/-- Coprime offsets in the finite square window. -/
noncomputable def squareAnchorCoprimeOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => Nat.Coprime n r)

/-- Membership in the coprime part of the square-offset window. -/
@[simp] theorem mem_squareAnchorCoprimeOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeOffsets n ↔
      SquareOffset n r ∧ Nat.Coprime n r := by
  simp [squareAnchorCoprimeOffsets]

/-- The coprime square window consists of two complete totient periods. -/
theorem card_squareAnchorCoprimeOffsets
    {n : ℕ}
    (hn : 0 < n) :
    (squareAnchorCoprimeOffsets n).card = 2 * Nat.totient n := by
  classical
  have hinterval :
      Finset.Icc 1 (2 * n) =
        Finset.Ico 1 (n + 1) ∪ Finset.Ico (n + 1) (2 * n + 1) := by
    ext r
    simp
    omega
  have hdisjoint :
      Disjoint (Finset.Ico 1 (n + 1))
        (Finset.Ico (n + 1) (2 * n + 1)) := by
    rw [Finset.disjoint_left]
    intro r hr₁ hr₂
    simp only [Finset.mem_Ico] at hr₁ hr₂
    omega
  have hcard₁ :
      ((Finset.Ico 1 (n + 1)).filter (fun r => Nat.Coprime n r)).card =
        Nat.totient n := by
    simpa [Nat.add_comm] using
      (Nat.filter_coprime_Ico_eq_totient n 1)
  have hcard₂ :
      ((Finset.Ico (n + 1) (2 * n + 1)).filter
          (fun r => Nat.Coprime n r)).card = Nat.totient n := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using
      (Nat.filter_coprime_Ico_eq_totient n (n + 1))
  have hdisjoint' :
      Disjoint
        ((Finset.Ico 1 (n + 1)).filter (fun r => Nat.Coprime n r))
        ((Finset.Ico (n + 1) (2 * n + 1)).filter
          (fun r => Nat.Coprime n r)) := by
    rw [Finset.disjoint_left]
    intro r hr₁ hr₂
    exact (Finset.disjoint_left.mp hdisjoint)
      (Finset.mem_of_mem_filter _ hr₁) (Finset.mem_of_mem_filter _ hr₂)
  unfold squareAnchorCoprimeOffsets squareOffsets
  rw [hinterval, Finset.filter_union, Finset.card_union_of_disjoint hdisjoint',
    hcard₁, hcard₂]
  omega

/-- Incidence mass supplied by old primes not dividing the anchor. -/
noncomputable def squareAnchorNondivisorIncidence (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorNondivisorPrimes n,
    (squarePrimeWaveOffsets n q).card

/-- Full cover forces a nondivisor incidence on every coprime offset. -/
theorem card_squareAnchorCoprimeOffsets_le_nondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (squareAnchorCoprimeOffsets n).card ≤
      squareAnchorNondivisorIncidence n := by
  classical
  unfold squareAnchorNondivisorIncidence
  calc
    (squareAnchorCoprimeOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hcop := mem_squareAnchorCoprimeOffsets.mp hr
      have hcovered := hfull r hcop.1
      have hnondiv :=
        (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hcop.2).mp
          hcovered
      rcases hnondiv with ⟨q, hq, hforbid⟩
      have hsingle := Finset.single_le_sum
        (f := fun q => if SquareOffsetForbiddenBy n q r then 1 else 0)
        (fun q _ => Nat.zero_le _) hq
      simpa [hforbid] using hsingle
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ q ∈ squareAnchorNondivisorPrimes n,
          (squarePrimeWaveOffsets n q).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hsubset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
        intro r hr
        exact (mem_squareOffsets).2 (mem_squareAnchorCoprimeOffsets.mp hr).1
      calc
        (∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0) ≤
            ∑ r ∈ squareOffsets n,
              if SquareOffsetForbiddenBy n q r then 1 else 0 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun r hr hnot => by simp)
        _ = (squarePrimeWaveOffsets n q).card := by
          simp [squarePrimeWaveOffsets, squareWaveOffsets]

/-- Nondivisor-prime incidence in exact baseline-plus-carry form. -/
theorem squareAnchorNondivisorIncidence_eq_sum_div_add_carry
    (n : ℕ) :
    squareAnchorNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        ((2 * n) / q + squareWaveCarry n q) := by
  unfold squareAnchorNondivisorIncidence
  apply Finset.sum_congr rfl
  intro q hq
  exact card_squarePrimeWaveOffsets_eq_div_add_carry
    (mem_squareAnchorNondivisorPrimes.mp hq).1

/-- Totient-form coprime full-cover frontier. -/
theorem two_mul_totient_le_nondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ squareAnchorNondivisorIncidence n := by
  rw [← card_squareAnchorCoprimeOffsets hn]
  exact card_squareAnchorCoprimeOffsets_le_nondivisorIncidence_of_fullyCovered
    hn hfull

/-!
### PRIM-L012: coprime doublets and `n`-shift separation

PRIM-L011 isolated the `2 * φ(n)` coprime seats because anchor-divisor
directions cannot cover them.  Those seats have more structure than an
undifferentiated cardinality: they are the `φ(n)` packets `(r, n + r)` with
`1 ≤ r ≤ n` and `Nat.Coprime n r`.  An anchor-nondivisor direction cannot hit
both seats of one packet, since the difference of the corresponding anchored
points is exactly `n`.

The support sets below count distinct old prime directions only.  They do not
count p-adic depth, use probabilistic independence, or invoke a prime-density
estimate.  The checkpoint stops at the localized finite incidence frontier;
it does not claim a contradiction or prove Legendre's conjecture.
-/

/-! ### PRIM-L012.1: canonical packet representatives -/

/-- The first-half representatives of the coprime square packets. -/
noncomputable def squareAnchorCoprimeBaseOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter (fun r => Nat.Coprime n r)

/-- Membership in the canonical coprime packet representatives. -/
@[simp] theorem mem_squareAnchorCoprimeBaseOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeBaseOffsets n ↔
      1 ≤ r ∧ r ≤ n ∧ Nat.Coprime n r := by
  simp [squareAnchorCoprimeBaseOffsets, and_assoc]

/-- The canonical first-half representatives have totient cardinality. -/
theorem card_squareAnchorCoprimeBaseOffsets
    {n : ℕ} (_hn : 0 < n) :
    (squareAnchorCoprimeBaseOffsets n).card = Nat.totient n := by
  have hinterval : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext r
    simp
  unfold squareAnchorCoprimeBaseOffsets
  rw [hinterval]
  simpa [Nat.add_comm] using Nat.filter_coprime_Ico_eq_totient n 1

/-- Coprimality is unchanged by adding one copy of the anchor. -/
theorem coprime_anchor_add_iff
    {n r : ℕ} :
    Nat.Coprime n (n + r) ↔ Nat.Coprime n r := by
  exact Nat.coprime_self_add_right

/-- The base seat of a packet lies in the coprime square window. -/
theorem mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    r ∈ squareAnchorCoprimeOffsets n := by
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hr
  exact mem_squareAnchorCoprimeOffsets.mpr
    ⟨⟨hr'.1, by omega⟩, hr'.2.2⟩

/-- The shifted seat of a packet lies in the coprime square window. -/
theorem mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    n + r ∈ squareAnchorCoprimeOffsets n := by
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hr
  exact mem_squareAnchorCoprimeOffsets.mpr
    ⟨⟨by omega, by omega⟩, coprime_anchor_add_iff.mpr hr'.2.2⟩

/-- The second seats of coprime packets, obtained by the `n`-shift. -/
noncomputable def squareAnchorCoprimeShiftOffsets (n : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeBaseOffsets n).image (fun r => n + r)

/-- Membership in the shifted packet seats is image membership. -/
@[simp] theorem mem_squareAnchorCoprimeShiftOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeShiftOffsets n ↔
      ∃ s, s ∈ squareAnchorCoprimeBaseOffsets n ∧ n + s = r := by
  simp [squareAnchorCoprimeShiftOffsets]

/-- The coprime square window is the disjoint union of its packet halves. -/
theorem squareAnchorCoprimeOffsets_eq_base_union_shift
    (n : ℕ) :
    squareAnchorCoprimeOffsets n =
      squareAnchorCoprimeBaseOffsets n ∪
        squareAnchorCoprimeShiftOffsets n := by
  ext r
  constructor
  · intro hr
    have hr' := mem_squareAnchorCoprimeOffsets.mp hr
    by_cases hle : r ≤ n
    · exact Finset.mem_union_left _
        (mem_squareAnchorCoprimeBaseOffsets.mpr ⟨hr'.1.1, hle, hr'.2⟩)
    · have hnr : n ≤ r := by omega
      have hlt : n < r := by omega
      have hsubcop : Nat.Coprime n (r - n) := by
        apply (coprime_anchor_add_iff (n := n) (r := r - n)).mp
        rw [Nat.add_sub_of_le hnr]
        exact hr'.2
      apply Finset.mem_union_right _
      apply mem_squareAnchorCoprimeShiftOffsets.mpr
      refine ⟨r - n, ?_, ?_⟩
      · have hsubpos : 0 < r - n := Nat.sub_pos_of_lt hlt
        have hsuble : r - n ≤ n := by
          apply Nat.sub_le_iff_le_add.mpr
          calc
            r ≤ 2 * n := hr'.1.2
            _ = n + n := by omega
        exact mem_squareAnchorCoprimeBaseOffsets.mpr
          ⟨by omega, hsuble, hsubcop⟩
      · omega
  · intro hr
    rcases Finset.mem_union.mp hr with hbase | hshift
    · exact mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets hbase
    · rcases mem_squareAnchorCoprimeShiftOffsets.mp hshift with ⟨s, hs, rfl⟩
      exact mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hs

/-- The two seats in every canonical packet occupy disjoint halves. -/
theorem disjoint_squareAnchorCoprimeBaseOffsets_coprimeShiftOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeBaseOffsets n)
      (squareAnchorCoprimeShiftOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hrbase hrshift
  rcases mem_squareAnchorCoprimeShiftOffsets.mp hrshift with ⟨s, hs, hsr⟩
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hrbase
  have hs' := mem_squareAnchorCoprimeBaseOffsets.mp hs
  omega

/-! ### PRIM-L012.2: nondivisor support and packet separation -/

/-- Old nondivisor prime directions supporting one square offset. -/
noncomputable def squareOffsetAnchorNondivisorSupport
    (n r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorNondivisorPrimes n).filter
    (fun q => SquareOffsetForbiddenBy n q r)

/-- Exact finite semantics of nondivisor support at one offset. -/
@[simp] theorem mem_squareOffsetAnchorNondivisorSupport
    {n r q : ℕ} :
    q ∈ squareOffsetAnchorNondivisorSupport n r ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ∣ n ^ 2 + r := by
  simp [squareOffsetAnchorNondivisorSupport, and_assoc,
    SquareOffsetForbiddenBy]

/-- On a coprime offset, old support is exactly nondivisor support. -/
theorem squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
    {n r : ℕ}
    (_hn : 0 < n)
    (hcop : Nat.Coprime n r) :
    squareOffsetPrimeSupport n r =
      squareOffsetAnchorNondivisorSupport n r := by
  ext q
  constructor
  · intro hq
    have hq' := mem_squareOffsetPrimeSupport.mp hq
    have hqnot : ¬ q ∣ n := by
      intro hqn
      have hnotcop : ¬ Nat.Coprime n r :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨q, hq'.1, hqn,
            (squareOffsetForbiddenBy_iff_dvd_offset_of_dvd_anchor hqn).mp
              hq'.2.2⟩
      exact hnotcop hcop
    exact mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hq'.1, hq'.2.1, hqnot, hq'.2.2⟩
  · intro hq
    have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
    exact mem_squareOffsetPrimeSupport.mpr
      ⟨hq'.1, hq'.2.1, hq'.2.2.2⟩

/-- A nondivisor modulus cannot support both seats of one `n`-shift packet. -/
theorem not_both_squareOffsetForbiddenBy_of_not_dvd_anchor
    {n q r : ℕ}
    (hqn : ¬ q ∣ n) :
    ¬ (SquareOffsetForbiddenBy n q r ∧
       SquareOffsetForbiddenBy n q (n + r)) := by
  rintro ⟨hleft, hright⟩
  apply hqn
  have hrewrite : n ^ 2 + (n + r) = (n ^ 2 + r) + n := by omega
  change q ∣ n ^ 2 + r at hleft
  change q ∣ n ^ 2 + (n + r) at hright
  rw [hrewrite] at hright
  exact (Nat.dvd_add_iff_right hleft).mpr hright

/-- Nondivisor supports of the two seats in one packet are disjoint. -/
theorem disjoint_anchorNondivisorSupport_shift
    (n r : ℕ) :
    Disjoint
      (squareOffsetAnchorNondivisorSupport n r)
      (squareOffsetAnchorNondivisorSupport n (n + r)) := by
  rw [Finset.disjoint_left]
  intro q hleft hright
  have hqn := (mem_squareOffsetAnchorNondivisorSupport.mp hleft).2.2.1
  exact not_both_squareOffsetForbiddenBy_of_not_dvd_anchor hqn
    ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hleft).2.2.2,
      (mem_squareOffsetAnchorNondivisorSupport.mp hright).2.2.2⟩

/-- Full cover gives distinct nondivisor witnesses for both packet seats. -/
theorem exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q,
      p ≠ q ∧
      p ∈ squareOffsetAnchorNondivisorSupport n r ∧
      q ∈ squareOffsetAnchorNondivisorSupport n (n + r) := by
  have hleftmem : r ∈ squareAnchorCoprimeOffsets n :=
    mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets hr
  have hrightmem : n + r ∈ squareAnchorCoprimeOffsets n :=
    mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hr
  have hleftmem' := mem_squareAnchorCoprimeOffsets.mp hleftmem
  have hrightmem' := mem_squareAnchorCoprimeOffsets.mp hrightmem
  have hleft' :=
    (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hleftmem'.2).mp
      (hfull r hleftmem'.1)
  have hright' :=
    (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hrightmem'.2).mp
      (hfull (n + r) hrightmem'.1)
  rcases hleft' with ⟨p, hp, hpforbid⟩
  rcases hright' with ⟨q, hq, hqforbid⟩
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mpr
    ⟨(mem_squareAnchorNondivisorPrimes.mp hp).1,
      (mem_squareAnchorNondivisorPrimes.mp hp).2.1,
      (mem_squareAnchorNondivisorPrimes.mp hp).2.2,
      hpforbid⟩
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mpr
    ⟨(mem_squareAnchorNondivisorPrimes.mp hq).1,
      (mem_squareAnchorNondivisorPrimes.mp hq).2.1,
      (mem_squareAnchorNondivisorPrimes.mp hq).2.2,
      hqforbid⟩
  refine ⟨p, q, ?_, hp', hq'⟩
  intro hpq
  subst q
  exact (Finset.disjoint_left.mp (disjoint_anchorNondivisorSupport_shift n r)
    hp' hq')

/-! ### PRIM-L012.3: coprime-restricted incidence -/

/-- Nondivisor incidence occurring only on coprime square seats. -/
noncomputable def squareAnchorCoprimeNondivisorIncidence (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorCoprimeOffsets n,
    (squareOffsetAnchorNondivisorSupport n r).card

/-- The restricted incidence is bounded by the unrestricted nondivisor ledger. -/
theorem squareAnchorCoprimeNondivisorIncidence_le_nondivisorIncidence
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n ≤
      squareAnchorNondivisorIncidence n := by
  classical
  unfold squareAnchorCoprimeNondivisorIncidence
    squareAnchorNondivisorIncidence
  calc
    (∑ r ∈ squareAnchorCoprimeOffsets n,
        (squareOffsetAnchorNondivisorSupport n r).card) =
        ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetAnchorNondivisorSupport]
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ q ∈ squareAnchorNondivisorPrimes n,
          (squarePrimeWaveOffsets n q).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hsubset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
        intro r hr
        exact (mem_squareOffsets).2
          (mem_squareAnchorCoprimeOffsets.mp hr).1
      calc
        (∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0) ≤
            ∑ r ∈ squareOffsets n,
              if SquareOffsetForbiddenBy n q r then 1 else 0 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun r hr hnot => by simp)
        _ = (squarePrimeWaveOffsets n q).card := by
          simp [squarePrimeWaveOffsets, squareWaveOffsets]

/-- The restricted ledger is the sum of the two support counts per packet. -/
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_base_pairs
    {n : ℕ} (_hn : 0 < n) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
        ((squareOffsetAnchorNondivisorSupport n r).card +
          (squareOffsetAnchorNondivisorSupport n (n + r)).card) := by
  classical
  have hdisjoint :=
    disjoint_squareAnchorCoprimeBaseOffsets_coprimeShiftOffsets n
  have hsum :
      ∑ r ∈ squareAnchorCoprimeShiftOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card =
        ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          (squareOffsetAnchorNondivisorSupport n (n + r)).card := by
    unfold squareAnchorCoprimeShiftOffsets
    apply Finset.sum_image
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  unfold squareAnchorCoprimeNondivisorIncidence
  rw [squareAnchorCoprimeOffsets_eq_base_union_shift,
    Finset.sum_union hdisjoint, hsum, ← Finset.sum_add_distrib]

/-- Full cover gives the localized paired totient frontier. -/
theorem two_mul_totient_le_coprimeNondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      squareAnchorCoprimeNondivisorIncidence n := by
  rw [← card_squareAnchorCoprimeOffsets hn]
  unfold squareAnchorCoprimeNondivisorIncidence
  calc
    (squareAnchorCoprimeOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_squareAnchorCoprimeOffsets.mp hr
      have hcover :=
        (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hr'.2).mp
          (hfull r hr'.1)
      rcases hcover with ⟨q, hq, hqforbid⟩
      have hqmem := mem_squareOffsetAnchorNondivisorSupport.mpr
        ⟨(mem_squareAnchorNondivisorPrimes.mp hq).1,
          (mem_squareAnchorNondivisorPrimes.mp hq).2.1,
          (mem_squareAnchorNondivisorPrimes.mp hq).2.2,
          hqforbid⟩
      have hpos := Finset.card_pos.mpr ⟨q, hqmem⟩
      omega

/-!
### PRIM-L013: coprime quotient lift and packet factorization

PRIM-L012 separated the coprime square window into packets `(r, n + r)` and
showed that full cover supplies distinct nondivisor prime directions on the
two seats.  This checkpoint attaches the complementary factor
`k = (n ^ 2 + r) / q` to each such finite incidence.  The factor equation is
exact, and the square-window bounds force `k > n` when `q ≤ n`.

For an anchor-nondivisor prime, coprimality with `n` transfers from the offset
to its complementary factor.  The quotient image is only a coordinate change
for existing finite support incidences: no primality, primitivity, uniqueness
of factorization, or contradiction is asserted for the quotient.  In
particular, the packet equation exposed below is a structural frontier rather
than a proof of Legendre's conjecture.
-/

/-! ### PRIM-L013.1: complementary factors -/

/-- The complementary factor attached to a known support divisor. -/
def squareOffsetSupportQuotient (n q r : ℕ) : ℕ :=
  (n ^ 2 + r) / q

/-- Exact reconstruction of an anchored point from its support quotient. -/
theorem mul_squareOffsetSupportQuotient_eq
    {n q r : ℕ}
    (hdiv : q ∣ n ^ 2 + r) :
    q * squareOffsetSupportQuotient n q r = n ^ 2 + r := by
  exact Nat.mul_div_cancel' hdiv

/-- A square-window support factor has a complementary factor larger than `n`. -/
theorem anchor_lt_squareOffsetSupportQuotient
    {n q r : ℕ}
    (hr : SquareOffset n r)
    (hqle : q ≤ n)
    (hdiv : q ∣ n ^ 2 + r) :
    n < squareOffsetSupportQuotient n q r := by
  have hpoint : n ^ 2 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    omega
  have hfactor := mul_squareOffsetSupportQuotient_eq hdiv
  by_contra hnot
  have hkle : squareOffsetSupportQuotient n q r ≤ n := by omega
  have hbound : q * squareOffsetSupportQuotient n q r ≤ n ^ 2 := by
    calc
      q * squareOffsetSupportQuotient n q r ≤ q * n :=
        Nat.mul_le_mul_left q hkle
      _ ≤ n * n := Nat.mul_le_mul_right n hqle
      _ = n ^ 2 := by simp [pow_two]
  omega

/-- A nondivisor support incidence has a complementary factor above the anchor. -/
theorem anchor_lt_squareOffsetSupportQuotient_of_mem_nondivisorSupport
    {n q r : ℕ}
    (hr : SquareOffset n r)
    (hq : q ∈ squareOffsetAnchorNondivisorSupport n r) :
    n < squareOffsetSupportQuotient n q r := by
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
  exact anchor_lt_squareOffsetSupportQuotient hr hq'.2.1 hq'.2.2.2

/-- Coprimality transfers between a coprime offset and its support quotient. -/
theorem coprime_anchor_squareOffsetSupportQuotient_iff
    {n q r : ℕ}
    (hq : Nat.Prime q)
    (hqn : ¬ q ∣ n)
    (hdiv : q ∣ n ^ 2 + r) :
    Nat.Coprime n (squareOffsetSupportQuotient n q r) ↔
      Nat.Coprime n r := by
  have hqcop : Nat.Coprime n q :=
    (hq.coprime_iff_not_dvd.mpr hqn).symm
  have hmul :
      Nat.Coprime n (q * squareOffsetSupportQuotient n q r) ↔
        Nat.Coprime n (squareOffsetSupportQuotient n q r) := by
    constructor
    · intro h
      exact (Nat.coprime_mul_iff_right.mp h).2
    · intro h
      exact hqcop.mul_right h
  have hpoint : Nat.Coprime n (n ^ 2 + r) ↔ Nat.Coprime n r := by
    simpa only [pow_two] using Nat.coprime_mul_left_add_right n r n
  calc
    Nat.Coprime n (squareOffsetSupportQuotient n q r) ↔
        Nat.Coprime n (q * squareOffsetSupportQuotient n q r) := hmul.symm
    _ ↔ Nat.Coprime n (n ^ 2 + r) := by
      rw [mul_squareOffsetSupportQuotient_eq hdiv]
    _ ↔ Nat.Coprime n r := hpoint

/-! ### PRIM-L013.2: finite coprime wave quotient images -/

/-- Coprime square seats hit by one old nondivisor prime wave. -/
noncomputable def squareAnchorCoprimeWaveOffsets (n q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)

/-- Exact membership in a coprime nondivisor wave. -/
@[simp] theorem mem_squareAnchorCoprimeWaveOffsets
    {n q r : ℕ} :
    r ∈ squareAnchorCoprimeWaveOffsets n q ↔
      SquareOffset n r ∧ Nat.Coprime n r ∧
        SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimeWaveOffsets, and_assoc]

/-- A nondivisor coprime-wave seat carries a large coprime quotient factor. -/
theorem squareAnchorCoprimeWaveOffsets_quotient_properties
    {n q r : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n)
    (hr : r ∈ squareAnchorCoprimeWaveOffsets n q) :
    n < squareOffsetSupportQuotient n q r ∧
      Nat.Coprime n (squareOffsetSupportQuotient n q r) ∧
      q * squareOffsetSupportQuotient n q r = n ^ 2 + r := by
  have hq' := mem_squareAnchorNondivisorPrimes.mp hq
  have hr' := mem_squareAnchorCoprimeWaveOffsets.mp hr
  refine ⟨anchor_lt_squareOffsetSupportQuotient hr'.1 hq'.2.1 hr'.2.2,
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2
      hr'.2.2).mpr hr'.2.1, ?_⟩
  exact mul_squareOffsetSupportQuotient_eq hr'.2.2

/-- Complementary factors carried by a coprime wave are represented finitely. -/
noncomputable def squareAnchorCoprimeSupportQuotients (n q : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeWaveOffsets n q).image
    (fun r => squareOffsetSupportQuotient n q r)

/-- Membership in the finite complementary-factor image. -/
@[simp] theorem mem_squareAnchorCoprimeSupportQuotients
    {n q k : ℕ} :
    k ∈ squareAnchorCoprimeSupportQuotients n q ↔
      ∃ r, r ∈ squareAnchorCoprimeWaveOffsets n q ∧
        squareOffsetSupportQuotient n q r = k := by
  simp [squareAnchorCoprimeSupportQuotients]

/-- A quotient-image member recovers its large, coprime factorization data. -/
theorem squareAnchorCoprimeSupportQuotients_mem_properties
    {n q k : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n)
    (hk : k ∈ squareAnchorCoprimeSupportQuotients n q) :
    ∃ r, r ∈ squareAnchorCoprimeWaveOffsets n q ∧
      n < k ∧ Nat.Coprime n k ∧ q * k = n ^ 2 + r := by
  rcases mem_squareAnchorCoprimeSupportQuotients.mp hk with ⟨r, hr, hrk⟩
  have hprops := squareAnchorCoprimeWaveOffsets_quotient_properties hq hr
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · simpa [hrk] using hprops.1
  · simpa [hrk] using hprops.2.1
  · rw [← hrk]
    exact hprops.2.2

/-- The quotient map is injective on the seats of a positive prime wave. -/
theorem card_squareAnchorCoprimeSupportQuotients
    {n q : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n) :
    (squareAnchorCoprimeSupportQuotients n q).card =
      (squareAnchorCoprimeWaveOffsets n q).card := by
  classical
  apply (Finset.card_image_iff).2
  intro r₁ hr₁ r₂ hr₂ heq
  have hq' := mem_squareAnchorNondivisorPrimes.mp hq
  have h₁ := mem_squareAnchorCoprimeWaveOffsets.mp hr₁
  have h₂ := mem_squareAnchorCoprimeWaveOffsets.mp hr₂
  have hf₁ := mul_squareOffsetSupportQuotient_eq h₁.2.2
  have hf₂ := mul_squareOffsetSupportQuotient_eq h₂.2.2
  have heq' : squareOffsetSupportQuotient n q r₁ =
      squareOffsetSupportQuotient n q r₂ := heq
  have hpoint : n ^ 2 + r₁ = n ^ 2 + r₂ := by
    calc
      n ^ 2 + r₁ = q * squareOffsetSupportQuotient n q r₁ := hf₁.symm
      _ = q * squareOffsetSupportQuotient n q r₂ := by rw [heq']
      _ = n ^ 2 + r₂ := hf₂
  omega

/-! ### PRIM-L013.3: quotient-coordinate incidence -/

/-- Restricted coprime incidence transposed to one-prime coprime waves. -/
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_coprimeWave_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeWaveOffsets n q).card := by
  classical
  unfold squareAnchorCoprimeNondivisorIncidence
  calc
    (∑ r ∈ squareAnchorCoprimeOffsets n,
        (squareOffsetAnchorNondivisorSupport n r).card) =
        ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetAnchorNondivisorSupport]
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          (squareAnchorCoprimeWaveOffsets n q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [squareAnchorCoprimeWaveOffsets]

/-- Restricted coprime incidence transposed to quotient-image cardinalities. -/
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_quotient_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeSupportQuotients n q).card := by
  rw [squareAnchorCoprimeNondivisorIncidence_eq_sum_coprimeWave_cards]
  apply Finset.sum_congr rfl
  intro q hq
  exact (card_squareAnchorCoprimeSupportQuotients hq).symm

/-! ### PRIM-L013.4: full-cover packet factorization -/

/-- A fully covered coprime packet yields two distinct small primes and two
large anchor-coprime complementary factors. -/
theorem exists_distinct_prime_large_cofactor_packet_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q a b,
      p ≠ q ∧
      p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b := by
  rcases exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
      hn hr hfull with ⟨p, q, hpq, hp, hq⟩
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
  have hpmem : p ∈ squareAnchorNondivisorPrimes n :=
    mem_squareAnchorNondivisorPrimes.mpr
      ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
  have hqmem : q ∈ squareAnchorNondivisorPrimes n :=
    mem_squareAnchorNondivisorPrimes.mpr
      ⟨hq'.1, hq'.2.1, hq'.2.2.1⟩
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hr
  have hrbaseSquare : SquareOffset n r := ⟨hr'.1, by omega⟩
  have hrshiftmem : n + r ∈ squareAnchorCoprimeOffsets n :=
    mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hr
  have hrshift' := mem_squareAnchorCoprimeOffsets.mp hrshiftmem
  have hrshift : Nat.Coprime n (n + r) := coprime_anchor_add_iff.mpr hr'.2.2
  have hpa : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hrbaseSquare hp'.2.1 hp'.2.2.2
  have hqb : n < squareOffsetSupportQuotient n q (n + r) :=
    anchor_lt_squareOffsetSupportQuotient hrshift'.1 hq'.2.1 hq'.2.2.2
  have hpa' : Nat.Coprime n (squareOffsetSupportQuotient n p r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2.2
  have hqb' : Nat.Coprime n (squareOffsetSupportQuotient n q (n + r)) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2.1
      hq'.2.2.2).mpr hrshift
  have hpaeq := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  have hqbeq := mul_squareOffsetSupportQuotient_eq hq'.2.2.2
  refine ⟨p, q, squareOffsetSupportQuotient n p r,
    squareOffsetSupportQuotient n q (n + r), hpq, hpmem, hqmem,
    hpa, hqb, hpa', hqb', hpaeq, hqbeq, ?_⟩
  omega

/-!
### PRIM-L014: quotient collision rigidity and global injectivity

PRIM-L013 attached a complementary factor to each coprime nondivisor support
incidence.  This checkpoint exposes all such incidences as one finite set of
pairs `(q, r)` and studies the quotient projection on that set.  A collision
within one prime wave was already excluded by the exact factor equation.  The
new point is that a collision across distinct prime waves would force the
prime pair `2, 3` and then `n < 4`; hence for `4 ≤ n` the quotient projection
is globally injective.

The resulting quotient values are large and coprime to the anchor, but they
are not asserted to be prime, primitive, or fresh.  This is a finite
collision-rigidity statement, not a density estimate, matching argument, or
proof of Legendre's conjecture.
-/

/-! ### PRIM-L014.1: the global incidence domain -/

/-- Coprime nondivisor support incidences `(q, r)`. -/
noncomputable def squareAnchorCoprimeSupportIncidences
    (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorCoprimeOffsets n)).filter
      (fun qr => SquareOffsetForbiddenBy n qr.1 qr.2)

/-- Exact membership in the global coprime-support incidence domain. -/
@[simp] theorem mem_squareAnchorCoprimeSupportIncidences
    {n q r : ℕ} :
    (q, r) ∈ squareAnchorCoprimeSupportIncidences n ↔
      q ∈ squareAnchorNondivisorPrimes n ∧
      r ∈ squareAnchorCoprimeOffsets n ∧
      SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimeSupportIncidences, and_assoc]

/-- The global incidence set has exactly the restricted-ledger cardinality. -/
theorem card_squareAnchorCoprimeSupportIncidences
    (n : ℕ) :
    (squareAnchorCoprimeSupportIncidences n).card =
      squareAnchorCoprimeNondivisorIncidence n := by
  classical
  unfold squareAnchorCoprimeSupportIncidences
    squareAnchorCoprimeNondivisorIncidence
  calc
    (((squareAnchorNondivisorPrimes n).product
        (squareAnchorCoprimeOffsets n)).filter
        (fun qr => SquareOffsetForbiddenBy n qr.1 qr.2)).card =
        ∑ qr ∈ (squareAnchorNondivisorPrimes n).product
          (squareAnchorCoprimeOffsets n),
          if SquareOffsetForbiddenBy n qr.1 qr.2 then 1 else 0 := by
      simp
    _ = ∑ q ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      change
        (∑ qr ∈ (squareAnchorNondivisorPrimes n ×ˢ
          squareAnchorCoprimeOffsets n),
          if SquareOffsetForbiddenBy n qr.1 qr.2 then 1 else 0) = _
      rw [Finset.sum_product]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ q ∈ squareAnchorNondivisorPrimes n,
            if SquareOffsetForbiddenBy n q r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [squareOffsetAnchorNondivisorSupport]

/-! ### PRIM-L014.2: global quotient projection -/

/-- The quotient attached to one global support incidence pair. -/
def squareAnchorIncidenceQuotient
    (n : ℕ) (qr : ℕ × ℕ) : ℕ :=
  squareOffsetSupportQuotient n qr.1 qr.2

/-- All complementary quotients arising from coprime support incidences. -/
noncomputable def squareAnchorCoprimeGlobalQuotients (n : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeSupportIncidences n).image
    (squareAnchorIncidenceQuotient n)

/-- Membership in the global quotient image remembers an incidence source. -/
@[simp] theorem mem_squareAnchorCoprimeGlobalQuotients
    {n k : ℕ} :
    k ∈ squareAnchorCoprimeGlobalQuotients n ↔
      ∃ q r, (q, r) ∈ squareAnchorCoprimeSupportIncidences n ∧
        squareOffsetSupportQuotient n q r = k := by
  simp [squareAnchorCoprimeGlobalQuotients, squareAnchorIncidenceQuotient]

/-! ### PRIM-L014.3: collision rigidity -/

private theorem eq_of_same_prime_same_support_quotient
    {n q r s : ℕ}
    (hr : q ∣ n ^ 2 + r)
    (hs : q ∣ n ^ 2 + s)
    (hquot : squareOffsetSupportQuotient n q r =
      squareOffsetSupportQuotient n q s) :
    r = s := by
  have hfr := mul_squareOffsetSupportQuotient_eq hr
  have hfs := mul_squareOffsetSupportQuotient_eq hs
  have hsum : n ^ 2 + r = n ^ 2 + s := by
    calc
      n ^ 2 + r = q * squareOffsetSupportQuotient n q r := hfr.symm
      _ = q * squareOffsetSupportQuotient n q s := by rw [hquot]
      _ = n ^ 2 + s := hfs
  omega

private theorem eq_two_eq_three_of_primes_of_sub_lt_two
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p < q)
    (hgap : q - p < 2) :
    p = 2 ∧ q = 3 := by
  have hsucc : q = p + 1 := by omega
  rcases hp.eq_two_or_odd' with hp_two | hp_odd
  · subst p
    constructor
    · rfl
    · omega
  · have hq_even : Even q := by
      rw [hsucc]
      exact hp_odd.add_one
    have hq_two : q = 2 := hq.even_iff.mp hq_even
    have hp_two_le : 2 ≤ p := hp.two_le
    omega

private theorem anchor_lt_four_of_ordered_distinct_prime_quotient_collision
    {n p q r s : ℕ}
    (hp : (p, r) ∈ squareAnchorCoprimeSupportIncidences n)
    (hq : (q, s) ∈ squareAnchorCoprimeSupportIncidences n)
    (hpq : p < q)
    (hquot : squareOffsetSupportQuotient n p r =
      squareOffsetSupportQuotient n q s) :
    n < 4 := by
  have hp' := mem_squareAnchorCoprimeSupportIncidences.mp hp
  have hq' := mem_squareAnchorCoprimeSupportIncidences.mp hq
  have hpp := mem_squareAnchorNondivisorPrimes.mp hp'.1
  have hqq := mem_squareAnchorNondivisorPrimes.mp hq'.1
  have hr' := mem_squareAnchorCoprimeOffsets.mp hp'.2.1
  have hs' := mem_squareAnchorCoprimeOffsets.mp hq'.2.1
  have hkp : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hpp.2.1 hp'.2.2
  have hkp' : n < squareOffsetSupportQuotient n q s := by
    simpa [hquot] using hkp
  let k := squareOffsetSupportQuotient n p r
  have hpfactor : p * k = n ^ 2 + r := by
    simpa [k] using mul_squareOffsetSupportQuotient_eq hp'.2.2
  have hqfactor : q * k = n ^ 2 + s := by
    simpa [k, hquot] using mul_squareOffsetSupportQuotient_eq hq'.2.2
  have hdiff : (q - p) * k = s - r := by
    rw [Nat.sub_mul]
    rw [hpfactor, hqfactor]
    omega
  have hr_one : 1 ≤ r := hr'.1.1
  have hs_two_n : s ≤ 2 * n := hs'.1.2
  have hk_pos : 0 < k := by
    dsimp [k]
    omega
  have hqp_pos : 0 < q - p := by omega
  have hprod_pos : 0 < (q - p) * k := Nat.mul_pos hqp_pos hk_pos
  have hsr : r ≤ s := by
    omega
  have hdiff_lt : s - r < 2 * n := by
    omega
  by_cases hgap : q - p < 2
  · have hpq23 := eq_two_eq_three_of_primes_of_sub_lt_two hpp.1 hqq.1
      hpq hgap
    rcases hpq23 with ⟨rfl, rfl⟩
    have hk_eq : k = s - r := by
      simpa using hdiff
    have hk_lt : k < 2 * n := by
      rw [hk_eq]
      exact hdiff_lt
    have hn_sq_lt : n ^ 2 < 2 * k := by
      omega
    have hn_sq_lt_four : n ^ 2 < 4 * n := by
      omega
    by_contra hn
    have hn_four : 4 ≤ n := by omega
    have hfour_mul : 4 * n ≤ n ^ 2 := by
      calc
        4 * n ≤ n * n := Nat.mul_le_mul_right n hn_four
        _ = n ^ 2 := by simp [pow_two]
    omega
  · have hgap_two : 2 ≤ q - p := by omega
    have htwo_mul : 2 * k ≤ (q - p) * k := by
      exact Nat.mul_le_mul_right k hgap_two
    omega

/-- A collision between distinct prime waves forces the anchor below `4`. -/
theorem anchor_lt_four_of_distinct_prime_quotient_collision
    {n p q r s : ℕ}
    (hp : (p, r) ∈ squareAnchorCoprimeSupportIncidences n)
    (hq : (q, s) ∈ squareAnchorCoprimeSupportIncidences n)
    (hpq : p ≠ q)
    (hquot : squareOffsetSupportQuotient n p r =
      squareOffsetSupportQuotient n q s) :
    n < 4 := by
  rcases lt_or_gt_of_ne hpq with hpq_lt | hqp_lt
  · exact anchor_lt_four_of_ordered_distinct_prime_quotient_collision
      hp hq hpq_lt hquot
  · exact anchor_lt_four_of_ordered_distinct_prime_quotient_collision
      hq hp hqp_lt hquot.symm

/-! ### PRIM-L014.4: global injectivity and image cardinality -/

/-- A quotient collision at an anchor `n ≥ 4` has the same prime and offset. -/
theorem squareAnchorIncidenceQuotient_eq_imp_eq_of_four_le
    {n : ℕ} (hn : 4 ≤ n) {x y : ℕ × ℕ}
    (hx : x ∈ squareAnchorCoprimeSupportIncidences n)
    (hy : y ∈ squareAnchorCoprimeSupportIncidences n)
    (hxy : squareAnchorIncidenceQuotient n x =
      squareAnchorIncidenceQuotient n y) :
    x = y := by
  rcases x with ⟨p, r⟩
  rcases y with ⟨q, s⟩
  change squareOffsetSupportQuotient n p r =
    squareOffsetSupportQuotient n q s at hxy
  by_cases hpq : p = q
  · subst q
    have hxs := mem_squareAnchorCoprimeSupportIncidences.mp hx
    have hys := mem_squareAnchorCoprimeSupportIncidences.mp hy
    have hrs := eq_of_same_prime_same_support_quotient hxs.2.2 hys.2.2 hxy
    cases hrs
    rfl
  · have hnlt := anchor_lt_four_of_distinct_prime_quotient_collision
      hx hy hpq hxy
    omega

theorem squareAnchorIncidenceQuotient_injective_of_four_le
    {n : ℕ} (hn : 4 ≤ n) :
    Set.InjOn (squareAnchorIncidenceQuotient n)
      (squareAnchorCoprimeSupportIncidences n : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  exact squareAnchorIncidenceQuotient_eq_imp_eq_of_four_le hn hx hy hxy

/-- At `4 ≤ n`, the global quotient image preserves the incidence cardinality. -/
theorem card_squareAnchorCoprimeGlobalQuotients_of_four_le
    {n : ℕ} (hn : 4 ≤ n) :
    (squareAnchorCoprimeGlobalQuotients n).card =
      squareAnchorCoprimeNondivisorIncidence n := by
  calc
    (squareAnchorCoprimeGlobalQuotients n).card =
        (squareAnchorCoprimeSupportIncidences n).card := by
      unfold squareAnchorCoprimeGlobalQuotients
      exact (Finset.card_image_iff).2
        (squareAnchorIncidenceQuotient_injective_of_four_le hn)
    _ = squareAnchorCoprimeNondivisorIncidence n :=
      card_squareAnchorCoprimeSupportIncidences n

/-! ### PRIM-L014.5: quotient properties and the full-cover frontier -/

/-- Every global quotient lies above the anchor and is coprime to it. -/
theorem squareAnchorCoprimeGlobalQuotients_properties
    {n k : ℕ}
    (hk : k ∈ squareAnchorCoprimeGlobalQuotients n) :
    n < k ∧ Nat.Coprime n k := by
  rcases mem_squareAnchorCoprimeGlobalQuotients.mp hk with
    ⟨q, r, hqr, hqk⟩
  have hqr' := mem_squareAnchorCoprimeSupportIncidences.mp hqr
  have hq' := mem_squareAnchorNondivisorPrimes.mp hqr'.1
  have hr' := mem_squareAnchorCoprimeOffsets.mp hqr'.2.1
  have hlarge : n < squareOffsetSupportQuotient n q r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hq'.2.1 hqr'.2.2
  have hcop : Nat.Coprime n (squareOffsetSupportQuotient n q r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hq'.1 hq'.2.2
      hqr'.2.2).mpr hr'.2
  constructor
  · rw [← hqk]
    exact hlarge
  · rw [← hqk]
    exact hcop

/-- Preferred singular spelling for the global quotient property theorem. -/
theorem squareAnchorCoprimeGlobalQuotient_properties
    {n k : ℕ}
    (hk : k ∈ squareAnchorCoprimeGlobalQuotients n) :
    n < k ∧ Nat.Coprime n k :=
  squareAnchorCoprimeGlobalQuotients_properties hk

/-- Full cover gives the totient lower bound on the global quotient image. -/
theorem two_mul_totient_le_squareAnchorCoprimeGlobalQuotients_of_four_le_of_fullyCovered
    {n : ℕ}
    (hn : 4 ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ (squareAnchorCoprimeGlobalQuotients n).card := by
  have hnpos : 0 < n := by omega
  calc
    2 * Nat.totient n ≤ squareAnchorCoprimeNondivisorIncidence n :=
      two_mul_totient_le_coprimeNondivisorIncidence_of_fullyCovered hnpos hfull
    _ = (squareAnchorCoprimeGlobalQuotients n).card :=
      (card_squareAnchorCoprimeGlobalQuotients_of_four_le hn).symm

/-- Preferred short name for the full-cover distinct-quotient frontier. -/
theorem two_mul_totient_le_card_globalQuotients_of_fullyCovered
    {n : ℕ}
    (hn : 4 ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ (squareAnchorCoprimeGlobalQuotients n).card :=
  two_mul_totient_le_squareAnchorCoprimeGlobalQuotients_of_four_le_of_fullyCovered
    hn hfull

/-!
### PRIM-L015: quotient co-support and direction/depth dichotomy

Dividing an anchored point `n^2 + r` by one selected old support prime `p`
preserves every other old prime direction.  The selected direction is the only
exception: it remains in the quotient exactly when one further `p`-factor was
present.  The finite support sets below record distinct prime directions, not
prime-power exponents.  The resulting direction/depth decomposition is
elementary and does not assert quotient primality, primitive origin, descent,
or Legendre's conjecture.
-/

/-! ### PRIM-L015.1: old directions in one quotient -/

/--
The old nondivisor prime directions dividing a selected complementary quotient.

This is a direction set: membership records one prime divisor, without
recording its multiplicity.
-/
noncomputable def squareQuotientAnchorNondivisorSupport
    (n p r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorNondivisorPrimes n).filter
    (fun q => q ∣ squareOffsetSupportQuotient n p r)

/-- Exact finite semantics of old directions in a complementary quotient. -/
@[simp] theorem mem_squareQuotientAnchorNondivisorSupport
    {n p r q : ℕ} :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧
        q ∣ squareOffsetSupportQuotient n p r := by
  simp [squareQuotientAnchorNondivisorSupport, and_assoc]

/-! ### PRIM-L015.2: support transfer -/

/-- Every old direction in the quotient already divides the anchored point. -/
theorem squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareQuotientAnchorNondivisorSupport n p r ⊆
      squareOffsetAnchorNondivisorSupport n r := by
  intro q hq
  have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hqpoint : q ∣ n ^ 2 + r := by
    rw [← mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
    exact dvd_mul_of_dvd_right hq'.2.2.2 p
  exact mem_squareOffsetAnchorNondivisorSupport.mpr
    ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqpoint⟩

/-- Every off-diagonal old direction survives division by the selected prime. -/
theorem mem_quotientSupport_iff_mem_offsetSupport_of_ne
    {n p q r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hqp : q ≠ p) :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      q ∈ squareOffsetAnchorNondivisorSupport n r := by
  constructor
  · apply squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp
  · intro hq
    have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
    have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
    have hqprod : q ∣ p * squareOffsetSupportQuotient n p r := by
      rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
      exact hq'.2.2.2
    rcases (Nat.Prime.dvd_mul hq'.1).mp hqprod with hqpdiv | hqdiv
    · have hqeqp : q = p :=
        ((Nat.dvd_prime hp'.1).mp hqpdiv).resolve_left hq'.1.ne_one
      exact False.elim (hqp hqeqp)
    · exact mem_squareQuotientAnchorNondivisorSupport.mpr
        ⟨hq'.1, hq'.2.1, hq'.2.2.1, hqdiv⟩

/-- Erasing the selected direction gives exact off-diagonal support equality. -/
theorem erase_squareQuotientSupport_eq_erase_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).erase p =
      (squareOffsetAnchorNondivisorSupport n r).erase p := by
  ext q
  by_cases hqp : q = p
  · simp [hqp]
  · simp only [Finset.mem_erase]
    rw [mem_quotientSupport_iff_mem_offsetSupport_of_ne hp hqp]

/-! ### PRIM-L015.3: cardinality and selected-direction depth -/

/-- Quotient support loses at most the selected prime direction. -/
theorem offsetSupport_card_sub_one_le_quotientSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareOffsetAnchorNondivisorSupport n r).card - 1 ≤
      (squareQuotientAnchorNondivisorSupport n p r).card := by
  have hsub :
      (squareOffsetAnchorNondivisorSupport n r).erase p ⊆
        squareQuotientAnchorNondivisorSupport n p r := by
    rw [← erase_squareQuotientSupport_eq_erase_offsetSupport hp]
    exact Finset.erase_subset _ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hp] at hcard
  exact hcard

/-- Quotient support is contained in the original support. -/
theorem quotientSupport_card_le_offsetSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).card ≤
      (squareOffsetAnchorNondivisorSupport n r).card := by
  exact Finset.card_le_card
    (squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp)

/-- The selected direction persists exactly when a second `p`-factor remains. -/
theorem selectedPrime_mem_quotientSupport_iff_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    p ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      p ^ 2 ∣ n ^ 2 + r := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  constructor
  · intro hq
    have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
    have hmuldiv : p * p ∣ p * squareOffsetSupportQuotient n p r :=
      Nat.mul_dvd_mul_left p hq'.2.2.2
    rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2] at hmuldiv
    simpa [pow_two] using hmuldiv
  · intro hsq
    have hsq' : p * p ∣ p * squareOffsetSupportQuotient n p r := by
      rw [mul_squareOffsetSupportQuotient_eq hp'.2.2.2]
      simpa [pow_two] using hsq
    have hpquot : p ∣ squareOffsetSupportQuotient n p r :=
      (Nat.mul_dvd_mul_iff_left hp'.1.pos).mp hsq'
    exact mem_squareQuotientAnchorNondivisorSupport.mpr
      ⟨hp'.1, hp'.2.1, hp'.2.2.1, hpquot⟩

/-! ### PRIM-L015.4: square-Body closure and direction/depth dichotomy -/

/-- A complementary quotient remains inside the certified square Body. -/
theorem squareOffsetSupportQuotient_le_squareBody
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ≤ squareBody n := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hfactor := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  have hpoint : n ^ 2 + r ≤ squareBody n := by
    dsimp [SquareOffset] at hr
    dsimp [squareBody]
    omega
  have hfactor_le : p * squareOffsetSupportQuotient n p r ≤
      squareBody n := by
    rw [hfactor]
    exact hpoint
  have hpone : 1 ≤ p := hp'.1.one_le
  have hquot_le : squareOffsetSupportQuotient n p r ≤
      p * squareOffsetSupportQuotient n p r := by
    simpa using Nat.mul_le_mul_right (squareOffsetSupportQuotient n p r)
      hpone
  exact hquot_le.trans hfactor_le

/-- A non-prime quotient in the square Body exposes an old nondivisor prime. -/
theorem exists_old_prime_dvd_quotient_of_not_prime
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hnotprime : ¬ Nat.Prime (squareOffsetSupportQuotient n p r)) :
    ∃ q, q ∈ squareQuotientAnchorNondivisorSupport n p r := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr'.1 hp'.2.1 hp'.2.2.2
  have hupper : squareOffsetSupportQuotient n p r ≤ squareBody n :=
    squareOffsetSupportQuotient_le_squareBody hr'.1 hp
  have hquot_one : 1 < squareOffsetSupportQuotient n p r := by
    omega
  obtain ⟨q, hqprime, hqdiv, hqle⟩ :=
    exists_prime_dvd_le_of_not_prime_of_le_squareBody hquot_one hupper
      hnotprime
  have hcop : Nat.Coprime n (squareOffsetSupportQuotient n p r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2
  have hqnotn : ¬ q ∣ n := by
    intro hqn
    have hqgcd : q ∣ Nat.gcd n (squareOffsetSupportQuotient n p r) :=
      Nat.dvd_gcd hqn hqdiv
    rw [hcop.gcd_eq_one] at hqgcd
    exact hqprime.ne_one (Nat.dvd_one.mp hqgcd)
  exact ⟨q, mem_squareQuotientAnchorNondivisorSupport.mpr
    ⟨hqprime, hqle, hqnotn, hqdiv⟩⟩

/-- Quotient non-primality splits into selected depth or another old direction. -/
theorem not_prime_quotient_iff_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      p ∣ squareOffsetSupportQuotient n p r ∨
      ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient
      (mem_squareAnchorCoprimeOffsets.mp hr).1 hp'.2.1 hp'.2.2.2
  constructor
  · intro hnotprime
    obtain ⟨q, hq⟩ := exists_old_prime_dvd_quotient_of_not_prime
      hn hr hp hnotprime
    have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hq
    by_cases hqp : q = p
    · left
      simpa [hqp] using hq'.2.2.2
    · right
      exact ⟨q, hqp,
        squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp hq⟩
  · rintro (hself | ⟨q, hqp, hqoff⟩)
    · intro hprime
      rcases (Nat.dvd_prime hprime).mp hself with hone | heq
      · exact hp'.1.ne_one hone
      · have hplt : p < squareOffsetSupportQuotient n p r :=
          lt_of_le_of_lt hp'.2.1 hlarge
        omega
    · have hqquot : q ∈ squareQuotientAnchorNondivisorSupport n p r :=
        (mem_quotientSupport_iff_mem_offsetSupport_of_ne hp hqp).mpr hqoff
      have hq' := mem_squareQuotientAnchorNondivisorSupport.mp hqquot
      have hqoff' := mem_squareOffsetAnchorNondivisorSupport.mp hqoff
      intro hprime
      rcases (Nat.dvd_prime hprime).mp hq'.2.2.2 with hone | heq
      · exact hqoff'.1.ne_one hone
      · have hqlt : q < squareOffsetSupportQuotient n p r :=
          lt_of_le_of_lt hqoff'.2.1 hlarge
        omega

/-!
### PRIM-L016: simple support and a fresh quotient direction

PRIM-L015 classified quotient non-primality by two finite old-world
obstructions: persistence of the selected direction, or another old support
direction.  This checkpoint formalizes the complementary case.  Singleton
support means one distinct old direction, while depth one is the elementary
condition `p^2 ∤ n^2 + r`; no general valuation API is introduced.

Under these hypotheses the quotient is prime, lies above the anchor, and is
fresh relative to `primeScalesUpTo n`.  This is finite-world freshness only:
it is not a Zsigmondy, PrimitiveBeam, or Legendre theorem.
-/

/-! ### PRIM-L016.1: singleton support and depth one -/

/-- No old support direction other than `p` is equivalent to singleton support. -/
theorem no_distinct_anchorNondivisorSupport_iff_eq_singleton
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (¬ ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p} := by
  constructor
  · intro hnodist
    ext q
    constructor
    · intro hq
      by_cases hqp : q = p
      · simp [hqp]
      · exact False.elim (hnodist ⟨q, hqp, hq⟩)
    · intro hq
      simp only [Finset.mem_singleton] at hq
      simpa [hq] using hp
  · intro hsingle hex
    rcases hex with ⟨q, hqp, hq⟩
    have hq' : q ∈ ({p} : Finset ℕ) := by
      rw [← hsingle]
      exact hq
    exact hqp (by simpa using hq')

/-- Depth one is the negated selected-direction persistence condition. -/
theorem selectedPrime_not_dvd_quotient_iff_not_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ p ∣ squareOffsetSupportQuotient n p r ↔
      ¬ p ^ 2 ∣ n ^ 2 + r := by
  constructor
  · intro hnot hsq
    have hqmem : p ∈ squareQuotientAnchorNondivisorSupport n p r :=
      (selectedPrime_mem_quotientSupport_iff_square_dvd hp).mpr hsq
    exact hnot (mem_squareQuotientAnchorNondivisorSupport.mp hqmem).2.2.2
  · intro hnot hpdvd
    apply hnot
    exact (selectedPrime_mem_quotientSupport_iff_square_dvd hp).mp
      (mem_squareQuotientAnchorNondivisorSupport.mpr
        ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hp).1,
          (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1,
          (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.1,
          hpdvd⟩)

/-- Exact criterion for a simple-support, depth-one quotient to be prime. -/
theorem prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p} ∧
      ¬ p ^ 2 ∣ n ^ 2 + r := by
  have hdich := not_prime_quotient_iff_self_depth_or_distinct_support
    hn hr hp
  constructor
  · intro hprime
    have hnodist : ¬ ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
      intro hother
      exact (hdich.mpr (Or.inr hother)) hprime
    have hsingle :=
      (no_distinct_anchorNondivisorSupport_iff_eq_singleton hp).mp hnodist
    have hdepth : ¬ p ^ 2 ∣ n ^ 2 + r := by
      apply (selectedPrime_not_dvd_quotient_iff_not_square_dvd hp).mp
      intro hpdvd
      exact (hdich.mpr (Or.inl hpdvd)) hprime
    exact ⟨hsingle, hdepth⟩
  · rintro ⟨hsingle, hdepth⟩
    by_contra hnotprime
    rcases hdich.mp hnotprime with hself | hother
    · exact (selectedPrime_not_dvd_quotient_iff_not_square_dvd hp).mpr
        hdepth hself
    · exact (no_distinct_anchorNondivisorSupport_iff_eq_singleton hp).mpr
        hsingle hother

/-- Convenient constructor for a prime quotient from the simple hypotheses. -/
theorem prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) :=
  (prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    hn hr hp).mpr ⟨hsingle, hdepth⟩

/-! ### PRIM-L016.2: finite-world freshness -/

/-- A complementary quotient lies outside the old bounded prime world. -/
theorem squareOffsetSupportQuotient_not_mem_primeScalesUpTo
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ∉ primeScalesUpTo n := by
  intro hk
  have hk' := mem_primeScalesUpTo.mp hk
  have hlarge : n < squareOffsetSupportQuotient n p r :=
    anchor_lt_squareOffsetSupportQuotient hr
      (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.2
  omega

/-- The simple quotient is fresh relative to the finite old prime world. -/
theorem freshPrimeDirection_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    FreshPrimeDirection
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r)
      (squareOffsetSupportQuotient n p r) := by
  let k := squareOffsetSupportQuotient n p r
  have hkprime : Nat.Prime k := by
    dsimp [k]
    exact prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
      hn hr hp hsingle hdepth
  have hknotmem : k ∉ primeScalesUpTo n := by
    dsimp [k]
    exact squareOffsetSupportQuotient_not_mem_primeScalesUpTo
      (mem_squareAnchorCoprimeOffsets.mp hr).1 hp
  exact ⟨hkprime, dvd_refl k, hknotmem⟩

/-- The simple quotient has no prime divisor from the old finite world. -/
theorem supportDisjointFrom_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    SupportDisjointFrom
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r) := by
  have hprime := prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    hn hr hp hsingle hdepth
  have hnotmem := squareOffsetSupportQuotient_not_mem_primeScalesUpTo
    (mem_squareAnchorCoprimeOffsets.mp hr).1 hp
  intro q hqprime hqdiv hqmem
  rcases (Nat.dvd_prime hprime).mp hqdiv with hqone | hqeq
  · exact hqprime.ne_one hqone
  · exact hnotmem (by simpa [hqeq] using hqmem)

/-! ### PRIM-L016.3: the simple old-prime times fresh-prime factorization -/

/-- The simple incidence factors as one old prime and one large fresh prime. -/
theorem simple_support_depth_one_factorization
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    let k := squareOffsetSupportQuotient n p r
    Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
    Nat.Prime k ∧ n < k ∧ Nat.Coprime n k ∧
    p * k = n ^ 2 + r := by
  dsimp
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hkprime := prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    hn hr hp hsingle hdepth
  have hklarge := anchor_lt_squareOffsetSupportQuotient hr'.1 hp'.2.1 hp'.2.2.2
  have hkcop :=
    (coprime_anchor_squareOffsetSupportQuotient_iff hp'.1 hp'.2.2.1
      hp'.2.2.2).mpr hr'.2
  have hkfactor := mul_squareOffsetSupportQuotient_eq hp'.2.2.2
  exact ⟨hp'.1, hp'.2.1, hp'.2.2.1, hkprime, hklarge, hkcop, hkfactor⟩

/-! ### PRIM-L016.4: fresh-or-obstructed trichotomy -/

/-- Every selected coprime incidence is simple or has an old-world obstruction. -/
theorem quotient_prime_or_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ∨
      p ^ 2 ∣ n ^ 2 + r ∨
      ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r := by
  by_cases hprime : Nat.Prime (squareOffsetSupportQuotient n p r)
  · exact Or.inl hprime
  · rcases (not_prime_quotient_iff_self_depth_or_distinct_support hn hr hp).mp
      hprime with hself | hother
    · exact Or.inr (Or.inl ((selectedPrime_mem_quotientSupport_iff_square_dvd hp).mp
        (mem_squareQuotientAnchorNondivisorSupport.mpr
          ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hp).1,
            (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.1,
            (mem_squareOffsetAnchorNondivisorSupport.mp hp).2.2.1,
            hself⟩)))
    · exact Or.inr (Or.inr hother)

/-!
### PRIM-L017: coprime obstruction seats and the Direction/Depth budget

PRIM-L016 classifies one selected support incidence.  This checkpoint lifts
that result to whole coprime seats: a covered seat is either simple and fresh,
singleton-support with selected-prime depth, or multi-directional.  The last
two classes are charged to finite obstruction ledgers below.  These are exact
finite bookkeeping statements and upper bounds, not a contradiction or a
proof of Legendre's conjecture.
-/

/-! ### PRIM-L017.1: seat predicates and finite classes -/

/-- A coprime seat with one old direction and depth one. -/
def SquareAnchorCoprimeSimpleFreshSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    ¬ p ^ 2 ∣ n ^ 2 + r

/-- A coprime seat with one old direction and persistent selected depth. -/
def SquareAnchorCoprimeSingletonDepthSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    p ^ 2 ∣ n ^ 2 + r

/-- A coprime seat carrying at least two distinct old directions. -/
def SquareAnchorCoprimeMultiSupportSeat (n r : ℕ) : Prop :=
  2 ≤ (squareOffsetAnchorNondivisorSupport n r).card

/-- Coprime simple/fresh seats in the square window. -/
noncomputable def squareAnchorCoprimeSimpleFreshOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeSimpleFreshSeat n)

/-- Coprime singleton-depth seats in the square window. -/
noncomputable def squareAnchorCoprimeSingletonDepthOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeSingletonDepthSeat n)

/-- Coprime multi-direction seats in the square window. -/
noncomputable def squareAnchorCoprimeMultiSupportOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (SquareAnchorCoprimeMultiSupportSeat n)

@[simp] theorem mem_squareAnchorCoprimeSimpleFreshOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeSimpleFreshOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeSimpleFreshSeat n r := by
  simp [squareAnchorCoprimeSimpleFreshOffsets]

@[simp] theorem mem_squareAnchorCoprimeSingletonDepthOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeSingletonDepthOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeSingletonDepthSeat n r := by
  simp [squareAnchorCoprimeSingletonDepthOffsets]

@[simp] theorem mem_squareAnchorCoprimeMultiSupportOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeMultiSupportOffsets n ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareAnchorCoprimeMultiSupportSeat n r := by
  simp [squareAnchorCoprimeMultiSupportOffsets]

/-! ### PRIM-L017.2: seat trichotomy and partition -/

/-- A covered coprime seat is simple, depth-obstructed, or multi-directional. -/
theorem coprime_covered_seat_trichotomy
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r) :
    SquareAnchorCoprimeSimpleFreshSeat n r ∨
      SquareAnchorCoprimeSingletonDepthSeat n r ∨
      SquareAnchorCoprimeMultiSupportSeat n r := by
  have hr' := mem_squareAnchorCoprimeOffsets.mp hr
  have hnondiv :=
    (squareOffsetCovered_iff_anchorNondivisor_of_coprime hn hr'.2).mp hcovered
  rcases hnondiv with ⟨p, hpWorld, hpforbid⟩
  have hpWorld' := mem_squareAnchorNondivisorPrimes.mp hpWorld
  have hp : p ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpWorld'.1, hpWorld'.2.1, hpWorld'.2.2, hpforbid⟩
  by_cases hcard :
      (squareOffsetAnchorNondivisorSupport n r).card = 1
  · have hsingle : squareOffsetAnchorNondivisorSupport n r = {p} := by
      rcases Finset.card_eq_one.mp hcard with ⟨q, hq⟩
      have hpq : p = q := by
        have hpq' : p ∈ ({q} : Finset ℕ) := by
          rw [← hq]
          exact hp
        simpa using hpq'
      calc
        squareOffsetAnchorNondivisorSupport n r = {q} := hq
        _ = {p} := by rw [hpq]
    by_cases hdepth : p ^ 2 ∣ n ^ 2 + r
    · exact Or.inr (Or.inl ⟨p, hp, hsingle, hdepth⟩)
    · exact Or.inl ⟨p, hp, hsingle, hdepth⟩
  · have hmulti :
        2 ≤ (squareOffsetAnchorNondivisorSupport n r).card := by
      have hpos : 0 < (squareOffsetAnchorNondivisorSupport n r).card :=
        Finset.card_pos.mpr ⟨p, hp⟩
      omega
    exact Or.inr (Or.inr hmulti)

private theorem not_simple_and_singletonDepth_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSimpleFreshSeat n r ∧
      SquareAnchorCoprimeSingletonDepthSeat n r) := by
  rintro ⟨hsimple, hdepth⟩
  rcases hsimple with ⟨p, hp, hpsingle, hpnot⟩
  rcases hdepth with ⟨q, hq, hqsingle, hqdepth⟩
  have hpq : p = q := by
    have hpq' : p ∈ ({q} : Finset ℕ) := by
      rw [← hqsingle]
      exact hp
    simpa using hpq'
  subst q
  exact hpnot hqdepth

private theorem not_simple_and_multiSupport_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSimpleFreshSeat n r ∧
      SquareAnchorCoprimeMultiSupportSeat n r) := by
  rintro ⟨hsimple, hmulti⟩
  rcases hsimple with ⟨p, hp, hsingle, _⟩
  dsimp [SquareAnchorCoprimeMultiSupportSeat] at hmulti
  rw [hsingle] at hmulti
  simp at hmulti

private theorem not_singletonDepth_and_multiSupport_seat
    {n r : ℕ} :
    ¬ (SquareAnchorCoprimeSingletonDepthSeat n r ∧
      SquareAnchorCoprimeMultiSupportSeat n r) := by
  rintro ⟨hdepth, hmulti⟩
  rcases hdepth with ⟨p, hp, hsingle, _⟩
  dsimp [SquareAnchorCoprimeMultiSupportSeat] at hmulti
  rw [hsingle] at hmulti
  simp at hmulti

theorem disjoint_squareAnchorCoprimeSimpleFreshOffsets_singletonDepthOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSimpleFreshOffsets n)
      (squareAnchorCoprimeSingletonDepthOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hs hd
  exact not_simple_and_singletonDepth_seat
    ⟨(mem_squareAnchorCoprimeSimpleFreshOffsets.mp hs).2,
      (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hd).2⟩

theorem disjoint_squareAnchorCoprimeSimpleFreshOffsets_multiSupportOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSimpleFreshOffsets n)
      (squareAnchorCoprimeMultiSupportOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hs hm
  exact not_simple_and_multiSupport_seat
    ⟨(mem_squareAnchorCoprimeSimpleFreshOffsets.mp hs).2,
      (mem_squareAnchorCoprimeMultiSupportOffsets.mp hm).2⟩

theorem disjoint_squareAnchorCoprimeSingletonDepthOffsets_multiSupportOffsets
    (n : ℕ) :
    Disjoint (squareAnchorCoprimeSingletonDepthOffsets n)
      (squareAnchorCoprimeMultiSupportOffsets n) := by
  rw [Finset.disjoint_left]
  intro r hd hm
  exact not_singletonDepth_and_multiSupport_seat
    ⟨(mem_squareAnchorCoprimeSingletonDepthOffsets.mp hd).2,
      (mem_squareAnchorCoprimeMultiSupportOffsets.mp hm).2⟩

/-- Under full cover, the coprime window is the disjoint three-class union. -/
theorem squareAnchorCoprimeOffsets_eq_simpleFresh_union_singletonDepth_union_multi
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    squareAnchorCoprimeOffsets n =
      (squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n) ∪
        squareAnchorCoprimeMultiSupportOffsets n := by
  ext r
  constructor
  · intro hr
    have hcop := mem_squareAnchorCoprimeOffsets.mp hr
    rcases coprime_covered_seat_trichotomy hn hr (hfull r hcop.1) with
      hsimple | hdepth | hmulti
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (mem_squareAnchorCoprimeSimpleFreshOffsets.mpr ⟨hr, hsimple⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (mem_squareAnchorCoprimeSingletonDepthOffsets.mpr ⟨hr, hdepth⟩))
    · exact Finset.mem_union_right _
        (mem_squareAnchorCoprimeMultiSupportOffsets.mpr ⟨hr, hmulti⟩)
  · intro hr
    rcases Finset.mem_union.mp hr with hrleft | hrmulti
    · rcases Finset.mem_union.mp hrleft with hrsimple | hrdepth
      · exact (mem_squareAnchorCoprimeSimpleFreshOffsets.mp hrsimple).1
      · exact (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hrdepth).1
    · exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hrmulti).1

theorem two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n =
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      (squareAnchorCoprimeSingletonDepthOffsets n).card +
      (squareAnchorCoprimeMultiSupportOffsets n).card := by
  have hdisjLeft :=
    disjoint_squareAnchorCoprimeSimpleFreshOffsets_singletonDepthOffsets n
  have hdisjRight :
      Disjoint
        (squareAnchorCoprimeSimpleFreshOffsets n ∪
          squareAnchorCoprimeSingletonDepthOffsets n)
        (squareAnchorCoprimeMultiSupportOffsets n) := by
    rw [Finset.disjoint_left]
    intro r hleft hmulti
    rcases Finset.mem_union.mp hleft with hs | hd
    · exact (Finset.disjoint_left.mp
        (disjoint_squareAnchorCoprimeSimpleFreshOffsets_multiSupportOffsets n))
        hs hmulti
    · exact (Finset.disjoint_left.mp
        (disjoint_squareAnchorCoprimeSingletonDepthOffsets_multiSupportOffsets n))
        hd hmulti
  calc
    2 * Nat.totient n = (squareAnchorCoprimeOffsets n).card :=
      (card_squareAnchorCoprimeOffsets hn).symm
    _ = ((squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n) ∪
        squareAnchorCoprimeMultiSupportOffsets n).card :=
      congrArg Finset.card
        (squareAnchorCoprimeOffsets_eq_simpleFresh_union_singletonDepth_union_multi
          hn hfull)
    _ = (squareAnchorCoprimeSimpleFreshOffsets n ∪
        squareAnchorCoprimeSingletonDepthOffsets n).card +
        (squareAnchorCoprimeMultiSupportOffsets n).card :=
      Finset.card_union_of_disjoint hdisjRight
    _ = (squareAnchorCoprimeSimpleFreshOffsets n).card +
        (squareAnchorCoprimeSingletonDepthOffsets n).card +
        (squareAnchorCoprimeMultiSupportOffsets n).card := by
      rw [Finset.card_union_of_disjoint hdisjLeft]

/-! ### PRIM-L017.3: simple seats and the depth budget -/

/-- A simple seat supplies a finite-world fresh quotient direction. -/
theorem exists_fresh_quotient_of_mem_simpleFreshOffsets
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeSimpleFreshOffsets n) :
    ∃ p,
      p ∈ squareOffsetAnchorNondivisorSupport n r ∧
      FreshPrimeDirection
        (primeScalesUpTo n)
        (squareOffsetSupportQuotient n p r)
        (squareOffsetSupportQuotient n p r) := by
  have hr' := mem_squareAnchorCoprimeSimpleFreshOffsets.mp hr
  rcases hr'.2 with ⟨p, hp, hsingle, hdepth⟩
  exact ⟨p, hp,
    freshPrimeDirection_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
      hn hr'.1 hp hsingle hdepth⟩

/-- The upper ledger of singleton-depth seats, counting all `p^2` wave hits. -/
noncomputable def squareAnchorPrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareWaveOffsets n (p ^ 2)).card

/-- Singleton-depth seats are paid for by the prime-square wave ledger. -/
theorem card_singletonDepthOffsets_le_primeSquareDepthBudget
    (n : ℕ) :
    (squareAnchorCoprimeSingletonDepthOffsets n).card ≤
      squareAnchorPrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorPrimeSquareDepthBudget
  have hsubset : squareAnchorCoprimeSingletonDepthOffsets n ⊆
      squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr).1).1
  calc
    (squareAnchorCoprimeSingletonDepthOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr
      rcases hr'.2 with ⟨p, hp, _, hdepth⟩
      have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
      have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
        mem_squareAnchorNondivisorPrimes.mpr
          ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
      have hwave : r ∈ squareWaveOffsets n (p ^ 2) :=
        mem_squareWaveOffsets.mpr ⟨
          (mem_squareAnchorCoprimeOffsets.mp hr'.1).1, hdepth⟩
      have hsingle := Finset.single_le_sum
        (f := fun q => if r ∈ squareWaveOffsets n (q ^ 2) then 1 else 0)
        (fun q _ => Nat.zero_le _) hpWorld
      simpa [hwave] using hsingle
    _ ≤ ∑ r ∈ squareOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareOffsets n,
            if r ∈ squareWaveOffsets n (p ^ 2) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          (squareWaveOffsets n (p ^ 2)).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareWaveOffsets, mem_squareOffsets]

/-- Exact baseline-plus-carry arithmetic form of the depth budget. -/
theorem squareAnchorPrimeSquareDepthBudget_eq_sum_div_add_carry
    (n : ℕ) :
    squareAnchorPrimeSquareDepthBudget n =
      ∑ p ∈ squareAnchorNondivisorPrimes n,
        ((2 * n) / (p ^ 2) + squareWaveCarry n (p ^ 2)) := by
  unfold squareAnchorPrimeSquareDepthBudget
  apply Finset.sum_congr rfl
  intro p hp
  simpa using card_squareWaveOffsets_eq_div_add_carry
    (Nat.pow_pos (mem_squareAnchorNondivisorPrimes.mp hp).1.pos)

/-! ### PRIM-L017.4: multi-direction and combined obstruction budgets -/

/-- Multi-direction seats are paid for by the existing pair-overlap ledger. -/
theorem card_multiSupportOffsets_le_squarePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squarePrimePairOverlapCount n := by
  classical
  have hmulti_subset : squareAnchorCoprimeMultiSupportOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hr).1
  have hcop_subset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp hr).1
  calc
    (squareAnchorCoprimeMultiSupportOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      apply Finset.sum_le_sum
      intro r hr
      have hmulti := mem_squareAnchorCoprimeMultiSupportOffsets.mp hr
      have hcop := mem_squareAnchorCoprimeOffsets.mp hmulti.1
      have hnpos : 0 < n := by
        dsimp [SquareOffset] at hcop
        omega
      have hsupport :=
        squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
          hnpos hcop.2
      have hcard : 2 ≤ (squareOffsetPrimeSupport n r).card := by
        rw [hsupport]
        simpa [SquareAnchorCoprimeMultiSupportSeat] using hmulti.2
      have hpair := primeSupport_sub_one_le_pairMultiplicity (n := n) (r := r)
      omega
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hmulti_subset
        (fun r _ _ => Nat.zero_le _)
    _ ≤ ∑ r ∈ squareOffsets n,
          squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hcop_subset
        (fun r _ _ => Nat.zero_le _)
    _ = squarePrimePairOverlapCount n :=
      (squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity n).symm

/-- Full cover separates coprime seats into fresh and obstruction budgets. -/
theorem two_mul_totient_le_simpleFresh_add_depthBudget_add_pairOverlap_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n := by
  have hpartition :=
    two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered hn hfull
  have hdepth := card_singletonDepthOffsets_le_primeSquareDepthBudget n
  have hmulti := card_multiSupportOffsets_le_squarePrimePairOverlapCount n
  calc
    2 * Nat.totient n =
        (squareAnchorCoprimeSimpleFreshOffsets n).card +
          (squareAnchorCoprimeSingletonDepthOffsets n).card +
          (squareAnchorCoprimeMultiSupportOffsets n).card := hpartition
    _ ≤ (squareAnchorCoprimeSimpleFreshOffsets n).card +
          squareAnchorPrimeSquareDepthBudget n +
          squarePrimePairOverlapCount n := by omega

/-- If no simple seat occurs, only the two finite obstruction budgets remain. -/
theorem two_mul_totient_le_depthBudget_add_pairOverlap_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n := by
  have hmain :=
    two_mul_totient_le_simpleFresh_add_depthBudget_add_pairOverlap_of_fullyCovered
      hn hfull
  simpa [hno] using hmain

/-!
### PRIM-L018: coprime-local obstruction ledgers

PRIM-L017 classifies coprime covered seats, but charges its depth and pair
obstructions to ledgers over the whole square window.  This checkpoint keeps
the same seat classification while restricting both ledgers to coprime seats
and to the anchor-nondivisor prime world.  The resulting identities are
finite incidence statements: local depth counts distinct prime-square
divisibility witnesses, not p-adic valuation mass, and the pair ledger counts
unordered distinct nondivisor-prime pairs.  The localized budgets are proved
to be no larger than their PRIM-L017 predecessors.  No contradiction, simple
seat existence, or Legendre theorem is asserted here.
-/

/-! ### PRIM-L018.1: local prime-square waves and depth -/

/-- Coprime seats hit by the square wave of one nondivisor prime. -/
noncomputable def squareAnchorCoprimePrimeSquareOffsets
    (n p : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => p ^ 2 ∣ n ^ 2 + r)

@[simp] theorem mem_squareAnchorCoprimePrimeSquareOffsets
    {n p r : ℕ} :
    r ∈ squareAnchorCoprimePrimeSquareOffsets n p ↔
      r ∈ squareAnchorCoprimeOffsets n ∧ p ^ 2 ∣ n ^ 2 + r := by
  simp [squareAnchorCoprimePrimeSquareOffsets]

/-- The coprime-local wave is contained in the existing square wave. -/
theorem squareAnchorCoprimePrimeSquareOffsets_subset_squareWaveOffsets
    (n p : ℕ) :
    squareAnchorCoprimePrimeSquareOffsets n p ⊆
      squareWaveOffsets n (p ^ 2) := by
  intro r hr
  have hr' := mem_squareAnchorCoprimePrimeSquareOffsets.mp hr
  exact mem_squareWaveOffsets.mpr
    ⟨(mem_squareAnchorCoprimeOffsets.mp hr'.1).1, hr'.2⟩

/-- The depth ledger restricted to coprime seats and nondivisor directions.

This is an upper ledger: a multi-support seat is counted whenever one of its
nondivisor directions has a prime-square hit. -/
noncomputable def squareAnchorCoprimePrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareAnchorCoprimePrimeSquareOffsets n p).card

/-- Singleton-depth seats are paid for by the coprime-local depth ledger. -/
theorem card_singletonDepthOffsets_le_coprimePrimeSquareDepthBudget
    (n : ℕ) :
    (squareAnchorCoprimeSingletonDepthOffsets n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
  have hsubset : squareAnchorCoprimeSingletonDepthOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr).1
  calc
    (squareAnchorCoprimeSingletonDepthOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeSingletonDepthOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := mem_squareAnchorCoprimeSingletonDepthOffsets.mp hr
      rcases hr'.2 with ⟨p, hp, _, hdepth⟩
      have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
      have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
        mem_squareAnchorNondivisorPrimes.mpr
          ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
      have hlocal : r ∈ squareAnchorCoprimePrimeSquareOffsets n p :=
        mem_squareAnchorCoprimePrimeSquareOffsets.mpr ⟨hr'.1, hdepth⟩
      have hsingle := Finset.single_le_sum
        (f := fun q =>
          if r ∈ squareAnchorCoprimePrimeSquareOffsets n q then 1 else 0)
        (fun q _ => Nat.zero_le _) hpWorld
      simpa [hlocal] using hsingle
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ squareAnchorNondivisorPrimes n,
          (squareAnchorCoprimePrimeSquareOffsets n p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareAnchorCoprimePrimeSquareOffsets]

/-- The localized depth ledger is bounded by the PRIM-L017 global ledger. -/
theorem squareAnchorCoprimePrimeSquareDepthBudget_le_primeSquareDepthBudget
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n ≤
      squareAnchorPrimeSquareDepthBudget n := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
    squareAnchorPrimeSquareDepthBudget
  apply Finset.sum_le_sum
  intro p hp
  exact Finset.card_le_card
    (squareAnchorCoprimePrimeSquareOffsets_subset_squareWaveOffsets n p)

/-- Number of distinct nondivisor prime-square witnesses at one coprime seat. -/
noncomputable def squareAnchorCoprimeDepthMultiplicity
    (n r : ℕ) : ℕ := by
  classical
  exact ((squareAnchorNondivisorPrimes n).filter
    (fun p => p ^ 2 ∣ n ^ 2 + r)).card

/-- Exact transpose of the localized prime-square incidence ledger. -/
theorem squareAnchorCoprimePrimeSquareDepthBudget_eq_sum_local_depthMultiplicity
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        squareAnchorCoprimeDepthMultiplicity n r := by
  classical
  unfold squareAnchorCoprimePrimeSquareDepthBudget
  calc
    (∑ p ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimePrimeSquareOffsets n p).card) =
        ∑ p ∈ squareAnchorNondivisorPrimes n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext r
      simp [squareAnchorCoprimePrimeSquareOffsets]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ p ∈ squareAnchorNondivisorPrimes n,
            if r ∈ squareAnchorCoprimePrimeSquareOffsets n p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareAnchorCoprimeDepthMultiplicity n r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [show (squareAnchorCoprimeDepthMultiplicity n r) =
        ((squareAnchorNondivisorPrimes n).filter
          (fun p => p ^ 2 ∣ n ^ 2 + r)).card by
            rfl]
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext p
      simp [squareAnchorCoprimePrimeSquareOffsets, hr]

/-! ### PRIM-L018.2: local nondivisor-prime pairs -/

/-- One canonical copy of every unordered pair of anchor-nondivisor primes. -/
noncomputable def squareAnchorNondivisorPrimePairs (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorNondivisorPrimes n)).filter
      (fun pair => pair.1 < pair.2)

/-- Membership in the canonical local nondivisor-prime pair set. -/
@[simp] theorem mem_squareAnchorNondivisorPrimePairs
    {n p q : ℕ} :
    (p, q) ∈ squareAnchorNondivisorPrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
        Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ p < q := by
  simp [squareAnchorNondivisorPrimePairs, and_assoc, and_left_comm,
    and_comm]

/-- The local canonical pair set is contained in the global old-prime pairs. -/
theorem squareAnchorNondivisorPrimePairs_subset_squarePrimePairs
    (n : ℕ) :
    squareAnchorNondivisorPrimePairs n ⊆ squarePrimePairs n := by
  intro pair hp
  rcases pair with ⟨p, q⟩
  have hpq : p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧ p < q := by
    have hp' : (p, q) ∈
        ((squareAnchorNondivisorPrimes n).product
          (squareAnchorNondivisorPrimes n)).filter
            (fun pair => pair.1 < pair.2) := by
      simpa [squareAnchorNondivisorPrimePairs] using hp
    have hfilter := Finset.mem_filter.mp hp'
    have hprod := Finset.mem_product.mp hfilter.1
    exact ⟨hprod.1, hprod.2, hfilter.2⟩
  have hp' := mem_squareAnchorNondivisorPrimes.mp hpq.1
  have hq' := mem_squareAnchorNondivisorPrimes.mp hpq.2.1
  exact mem_squarePrimePairs.mpr
    ⟨hp'.1, hp'.2.1, hq'.1, hq'.2.1, hpq.2.2⟩

/-- Coprime seats carrying one specified nondivisor-prime pair. -/
noncomputable def squareAnchorCoprimePrimePairOverlapOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r =>
      SquareOffsetForbiddenBy n p r ∧
        SquareOffsetForbiddenBy n q r)

@[simp] theorem mem_squareAnchorCoprimePrimePairOverlapOffsets
    {n p q r : ℕ} :
    r ∈ squareAnchorCoprimePrimePairOverlapOffsets n p q ↔
      r ∈ squareAnchorCoprimeOffsets n ∧
        SquareOffsetForbiddenBy n p r ∧
          SquareOffsetForbiddenBy n q r := by
  simp [squareAnchorCoprimePrimePairOverlapOffsets, and_assoc]

/-- The localized unordered-pair incidence ledger. -/
noncomputable def squareAnchorCoprimePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
    (squareAnchorCoprimePrimePairOverlapOffsets n pair.1 pair.2).card

/-- Exact local pair double count using the same support as the seat trichotomy. -/
theorem squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
  classical
  have hpairset (r : ℕ) :
      (squareAnchorNondivisorPrimePairs n).filter
          (fun pair =>
            pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
              pair.2 ∈ squareOffsetAnchorNondivisorSupport n r) =
        upperPairs (squareOffsetAnchorNondivisorSupport n r) := by
    ext pair
    rcases pair with ⟨p, q⟩
    simp [squareAnchorNondivisorPrimePairs, upperPairs,
      mem_squareOffsetAnchorNondivisorSupport, and_assoc,
      and_left_comm, and_comm]
    omega
  unfold squareAnchorCoprimePrimePairOverlapCount
  calc
    (∑ pair ∈ squareAnchorNondivisorPrimePairs n,
        (squareAnchorCoprimePrimePairOverlapOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
          ∑ r ∈ squareAnchorCoprimeOffsets n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      simp [squareAnchorCoprimePrimePairOverlapOffsets]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 r then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          ((squareAnchorNondivisorPrimePairs n).filter
            (fun pair =>
              pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
                pair.2 ∈ squareOffsetAnchorNondivisorSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext pair
      rcases pair with ⟨p, q⟩
      simp [mem_squareOffsetAnchorNondivisorSupport,
        SquareOffsetForbiddenBy]
      aesop
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          (upperPairs (squareOffsetAnchorNondivisorSupport n r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hpairset]
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact card_upperPairs_eq_choose _

/-! ### PRIM-L018.3: localized budgets and seat certificate -/

/- A support of size at least two contributes at least one unordered pair. -/
private theorem one_le_choose_two_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ Nat.choose k 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
  have hk' : 1 ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul hk hk'
  simpa [Nat.mul_comm] using hmul

/-- Multi-support seats are paid for by the localized pair ledger. -/
theorem card_multiSupportOffsets_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squareAnchorCoprimePrimePairOverlapCount n := by
  classical
  have hmulti_subset : squareAnchorCoprimeMultiSupportOffsets n ⊆
      squareAnchorCoprimeOffsets n := by
    intro r hr
    exact (mem_squareAnchorCoprimeMultiSupportOffsets.mp hr).1
  calc
    (squareAnchorCoprimeMultiSupportOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeMultiSupportOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hmulti := mem_squareAnchorCoprimeMultiSupportOffsets.mp hr
      exact one_le_choose_two_of_two_le hmulti.2
    _ ≤ ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hmulti_subset
        (fun r _ _ => Nat.zero_le _)
    _ = squareAnchorCoprimePrimePairOverlapCount n :=
      (squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support n).symm

/-- The localized pair ledger is bounded by the PRIM-L009 global pair ledger. -/
theorem squareAnchorCoprimePrimePairOverlapCount_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n ≤
      squarePrimePairOverlapCount n := by
  classical
  have hsubset : squareAnchorCoprimeOffsets n ⊆ squareOffsets n := by
    intro r hr
    exact mem_squareOffsets.mpr
      (mem_squareAnchorCoprimeOffsets.mp hr).1
  have hpointwise :
      (∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2) =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        squareOffsetPrimePairMultiplicity n r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hcop := mem_squareAnchorCoprimeOffsets.mp hr
    have hnpos : 0 < n := by
      dsimp [SquareOffset] at hcop
      omega
    unfold squareOffsetPrimePairMultiplicity
    rw [← squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
      hnpos hcop.2]
  calc
    squareAnchorCoprimePrimePairOverlapCount n =
        ∑ r ∈ squareAnchorCoprimeOffsets n,
          Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 :=
      squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support n
    _ = ∑ r ∈ squareAnchorCoprimeOffsets n,
          squareOffsetPrimePairMultiplicity n r := hpointwise
    _ ≤ ∑ r ∈ squareOffsets n, squareOffsetPrimePairMultiplicity n r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => Nat.zero_le _)
    _ = squarePrimePairOverlapCount n :=
      (squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity n).symm

/-- A covered coprime non-simple seat pays one unit to a local obstruction. -/
theorem one_le_depthMultiplicity_add_pairMultiplicity_of_coprime_covered_not_simple
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r)
    (hnotSimple : ¬ SquareAnchorCoprimeSimpleFreshSeat n r) :
    1 ≤ squareAnchorCoprimeDepthMultiplicity n r +
      Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2 := by
  rcases coprime_covered_seat_trichotomy hn hr hcovered with
    hsimple | hdepth | hmulti
  · exact False.elim (hnotSimple hsimple)
  · rcases hdepth with ⟨p, hp, _, hdepth⟩
    have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
    have hpWorld : p ∈ squareAnchorNondivisorPrimes n :=
      mem_squareAnchorNondivisorPrimes.mpr
        ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩
    have hpDepth : p ∈ (squareAnchorNondivisorPrimes n).filter
        (fun q => q ^ 2 ∣ n ^ 2 + r) :=
      Finset.mem_filter.mpr ⟨hpWorld, hdepth⟩
    have hpos : 0 < squareAnchorCoprimeDepthMultiplicity n r := by
      dsimp [squareAnchorCoprimeDepthMultiplicity]
      exact Finset.card_pos.mpr ⟨p, hpDepth⟩
    omega
  · have hchoose := one_le_choose_two_of_two_le hmulti
    omega

/-! ### PRIM-L018.4: the localized full-cover frontier -/

/-- Full cover is charged to simple seats and the two coprime-local ledgers. -/
theorem two_mul_totient_le_simpleFresh_add_localDepth_add_localPair_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n := by
  have hpartition :=
    two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered hn hfull
  have hdepth :=
    card_singletonDepthOffsets_le_coprimePrimeSquareDepthBudget n
  have hmulti := card_multiSupportOffsets_le_coprimePrimePairOverlapCount n
  calc
    2 * Nat.totient n =
        (squareAnchorCoprimeSimpleFreshOffsets n).card +
          (squareAnchorCoprimeSingletonDepthOffsets n).card +
          (squareAnchorCoprimeMultiSupportOffsets n).card := hpartition
    _ ≤ (squareAnchorCoprimeSimpleFreshOffsets n).card +
          squareAnchorCoprimePrimeSquareDepthBudget n +
          squareAnchorCoprimePrimePairOverlapCount n := by omega

/-- If no simple seat exists, only the localized obstruction ledgers remain. -/
theorem two_mul_totient_le_localDepth_add_localPair_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n := by
  have hmain :=
    two_mul_totient_le_simpleFresh_add_localDepth_add_localPair_of_fullyCovered
      hn hfull
  simpa [hno] using hmain

/-- The localized obstruction capacity is no larger than PRIM-L017's capacity.

This explicit domination records that PRIM-L018 removes bookkeeping waste
rather than merely renaming the earlier frontier. -/
theorem squareAnchorCoprimeLocalDepth_add_pairOverlap_le_globalDepth_add_pairOverlap
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n +
        squareAnchorCoprimePrimePairOverlapCount n ≤
      squareAnchorPrimeSquareDepthBudget n +
        squarePrimePairOverlapCount n := by
  have hdepth :=
    squareAnchorCoprimePrimeSquareDepthBudget_le_primeSquareDepthBudget n
  have hpair :=
    squareAnchorCoprimePrimePairOverlapCount_le_squarePrimePairOverlapCount n
  omega

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
