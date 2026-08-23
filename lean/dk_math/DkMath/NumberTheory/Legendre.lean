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
