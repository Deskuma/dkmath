/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PairOverlap

#print "file: DkMath.NumberTheory.Legendre.CoprimePacket"

/-!
## CoprimePacket

Anchor-divisor localization and canonical coprime packet geometry `(r, n+r)` built on PairOverlap.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

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


end DkMath.NumberTheory.Legendre

