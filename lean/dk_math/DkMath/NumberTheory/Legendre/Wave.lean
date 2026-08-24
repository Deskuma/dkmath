/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Basic

#print "file: DkMath.NumberTheory.Legendre.Wave"

/-!
## Wave

One-wave occupancy, square-anchor carries, and first-order finite incidence ledgers built on Basic.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

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
  classical
  rw [squareWaveOffsets, Finset.mem_filter, mem_squareOffsets]
  rfl

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
  have hdiv := Nat.div_add_div_le_add_div (x := n ^ 2) (y := 2 * n) (z := m)
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


end DkMath.NumberTheory.Legendre
