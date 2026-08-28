/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.OldSupportCapacity
import DkMath.NumberTheory.Primitive.PeriodicPrimeWorld

#print "file: DkMath.NumberTheory.Legendre.OldSupportGcd"

/-!
## OldSupportGcd

For two ordered square-shell offsets, the gcd of the corresponding complete
points divides the offset gap.  The actual old-support condition therefore
sees only the prime divisors of this gcd that are at most the anchor.

Inside a positive square shell, the gap is smaller than `2 * n`.  Consequently
old-support disjointness permits exactly two gcd shapes: `1`, or one fresh
prime strictly larger than `n`.  The fresh branch is inhabited by the L029
example `gcd 10 15 = 5` and must not be collapsed into complete coprimality.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L030.1: gcd divides the ordered seat gap -/

/-- The gcd of two shared-anchor points divides their ordered offset gap. -/
theorem gcd_squarePoints_dvd_orderedOffsetGap
    {n r s : ℕ} (hrs : r < s) :
    Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ∣ s - r := by
  have hleft : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ∣ n ^ 2 + r :=
    Nat.gcd_dvd_left _ _
  have hright : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ∣ n ^ 2 + s :=
    Nat.gcd_dvd_right _ _
  have hid : n ^ 2 + s = (n ^ 2 + r) + (s - r) := by omega
  have hright' :
      Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ∣
        (n ^ 2 + r) + (s - r) := by
    convert hright using 1; omega
  exact (Nat.dvd_add_iff_right hleft).mpr hright'

/-! ### PRIM-L030.2: old-support disjointness and gcd support escape -/

/--
Two actual old-prime supports are disjoint exactly when their complete-point
gcd has no prime divisor from the bounded old-prime world.
-/
theorem disjoint_squareOffsetPrimeSupport_iff_gcd_supportDisjointFrom
    {n r s : ℕ} :
    Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) ↔
      SupportDisjointFrom (primeScalesUpTo n)
        (Nat.gcd (n ^ 2 + r) (n ^ 2 + s)) := by
  constructor
  · intro hdisj q hq hqg hqS
    have hqS' := mem_primeScalesUpTo.mp hqS
    have hqA : q ∣ n ^ 2 + r :=
      dvd_trans hqg (Nat.gcd_dvd_left _ _)
    have hqB : q ∣ n ^ 2 + s :=
      dvd_trans hqg (Nat.gcd_dvd_right _ _)
    exact (Finset.disjoint_left.mp hdisj)
      (mem_squareOffsetPrimeSupport.mpr ⟨hqS'.1, hqS'.2, hqA⟩)
      (mem_squareOffsetPrimeSupport.mpr ⟨hqS'.1, hqS'.2, hqB⟩)
  · intro hdisj
    rw [Finset.disjoint_left]
    intro q hqA hqB
    have hqA' := mem_squareOffsetPrimeSupport.mp hqA
    have hqB' := mem_squareOffsetPrimeSupport.mp hqB
    have hqg : q ∣ Nat.gcd (n ^ 2 + r) (n ^ 2 + s) :=
      Nat.dvd_gcd hqA'.2.2 hqB'.2.2
    exact hdisj hqA'.1 hqg
      (mem_primeScalesUpTo.mpr ⟨hqA'.1, hqA'.2.1⟩)

/-! ### PRIM-L030.3: optional finite-world modulus form -/

/-- The gcd support escape is equivalently coprimality with the prime-world modulus. -/
theorem disjoint_squareOffsetPrimeSupport_iff_gcd_coprime_primeWorldModulus
    {n r s : ℕ} :
    Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) ↔
      Nat.Coprime (Nat.gcd (n ^ 2 + r) (n ^ 2 + s))
        (primeWorldModulus (primeScalesUpTo n)) := by
  rw [disjoint_squareOffsetPrimeSupport_iff_gcd_supportDisjointFrom]
  exact supportDisjointFrom_iff_coprime_primeWorldModulus
    (knownPrimeScales_primeScalesUpTo n)

/-! ### PRIM-L030.4: positive-shell gcd classification -/

/-- The ordered shell gap is strictly smaller than twice the positive anchor. -/
theorem gcd_squarePoints_lt_twice_anchor
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s) :
    Nat.gcd (n ^ 2 + r) (n ^ 2 + s) < 2 * n := by
  have hgap : s - r < 2 * n := by
    dsimp [SquareOffset] at hr hs
    omega
  have hgap_pos : 0 < s - r := by omega
  exact lt_of_le_of_lt
    (Nat.le_of_dvd hgap_pos (gcd_squarePoints_dvd_orderedOffsetGap hrs))
    hgap

/--
For distinct ordered positive-shell seats, old-support disjointness is
equivalent to the gcd being `1` or one fresh prime above the old-prime bound.
-/
theorem disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s) :
    Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) ↔
      Nat.gcd (n ^ 2 + r) (n ^ 2 + s) = 1 ∨
        (Nat.Prime (Nat.gcd (n ^ 2 + r) (n ^ 2 + s)) ∧
          n < Nat.gcd (n ^ 2 + r) (n ^ 2 + s)) := by
  let g := Nat.gcd (n ^ 2 + r) (n ^ 2 + s)
  change Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s) ↔
    g = 1 ∨ (Nat.Prime g ∧ n < g)
  have hApos : 0 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    omega
  have hgap_lt : g < 2 * n := by
    dsimp [g]
    exact gcd_squarePoints_lt_twice_anchor hr hs hrs
  have hdisj_gcd :
      SupportDisjointFrom (primeScalesUpTo n) g ↔
      Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) := by
    exact disjoint_squareOffsetPrimeSupport_iff_gcd_supportDisjointFrom.symm
  constructor
  · intro hdisj
    have hsd : SupportDisjointFrom (primeScalesUpTo n) g :=
      hdisj_gcd.mpr hdisj
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · have hgpos : 0 < g := by
        dsimp [g]
        exact Nat.gcd_pos_of_pos_left _ hApos
      obtain ⟨p, hp, hpg⟩ :=
        Nat.exists_prime_and_dvd (by omega : g ≠ 1)
      have hpA : p ∣ n ^ 2 + r :=
        dvd_trans hpg (Nat.gcd_dvd_left _ _)
      have hpB : p ∣ n ^ 2 + s :=
        dvd_trans hpg (Nat.gcd_dvd_right _ _)
      have hnp : n < p := by
        by_contra hnp
        have hpS : p ∈ primeScalesUpTo n :=
          mem_primeScalesUpTo.mpr ⟨hp, Nat.le_of_not_gt hnp⟩
        exact hsd hp hpg hpS
      have hgp_lt : g < 2 * p := by omega
      obtain ⟨c, hgc⟩ := hpg
      have hc_pos : 0 < c := by
        by_contra hc
        have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
        rw [hc0, mul_zero] at hgc
        omega
      have hmul_lt : p * c < p * 2 := by
        calc
          p * c = g := hgc.symm
          _ < 2 * p := hgp_lt
          _ = p * 2 := by omega
      have hc_lt : c < 2 := (Nat.mul_lt_mul_left hp.pos).mp hmul_lt
      have hc_one : c = 1 := by omega
      have hgeq : g = p := by
        rw [hgc, hc_one, mul_one]
      exact Or.inr ⟨by simpa [hgeq] using hp, by rw [hgeq]; exact hnp⟩
  · intro hshape
    apply hdisj_gcd.mp
    intro q hq hqg hqS
    rcases hshape with hgeq | ⟨hgprime, hng⟩
    · rw [hgeq] at hqg
      exact hq.not_dvd_one hqg
    · have hqS' := mem_primeScalesUpTo.mp hqS
      have hqeq : q = g :=
        ((Nat.dvd_prime hgprime).mp hqg).resolve_left hq.ne_one
      omega

/-! ### PRIM-L030.5: explicit fresh branch -/

/-- A nontrivial old-support-disjoint gcd is a single fresh prime. -/
theorem prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s)
    (hdisj : Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s))
    (hg : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1) :
    Nat.Prime (Nat.gcd (n ^ 2 + r) (n ^ 2 + s)) ∧
      n < Nat.gcd (n ^ 2 + r) (n ^ 2 + s) := by
  exact (disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
    hr hs hrs).mp hdisj |>.resolve_left hg

/-! ### PRIM-L030.6: recover the L029 strictness witness -/

/-- The L029 fresh collision is exactly `gcd 10 15 = 5 > 3`. -/
theorem oldSupportCapacity_strictness_gcd_three_one_six :
    Nat.gcd (3 ^ 2 + 1) (3 ^ 2 + 6) = 5 ∧
      Nat.Prime 5 ∧ 3 < 5 := by
  norm_num

/-! ### PRIM-L030.7: finite-family gcd interface -/

/--
A finite family whose ordered pairs have only the two allowed gcd shapes.
The ordered condition avoids duplicating the symmetric pair statement.
-/
def PairwiseGcdFreshSeparatedSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, SquareOffset n r) ∧
    ∀ r ∈ R, ∀ s ∈ R, r < s →
      Nat.gcd (n ^ 2 + r) (n ^ 2 + s) = 1 ∨
        (Nat.Prime (Nat.gcd (n ^ 2 + r) (n ^ 2 + s)) ∧
          n < Nat.gcd (n ^ 2 + r) (n ^ 2 + s))

/-- Under `0<n`, the gcd/fresh family is equivalent to old-support separation. -/
theorem pairwiseGcdFreshSeparatedSquareSeatFamily_iff_oldSupportDisjoint
    {n : ℕ} {R : Finset ℕ} :
    PairwiseGcdFreshSeparatedSquareSeatFamily n R ↔
      PairwiseOldSupportDisjointSquareSeatFamily n R := by
  constructor
  · intro hfamily
    constructor
    · exact hfamily.1
    · intro r hr s hs hrs
      rcases lt_or_gt_of_ne hrs with hrs' | hrs'
      · exact (disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
          (hfamily.1 r hr) (hfamily.1 s hs) hrs').mpr
          (hfamily.2 r hr s hs hrs')
      · have hsr : Disjoint (squareOffsetPrimeSupport n s)
            (squareOffsetPrimeSupport n r) :=
          (disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
            (hfamily.1 s hs) (hfamily.1 r hr) hrs').mpr
            (by
              simpa [Nat.gcd_comm] using
                (hfamily.2 s hs r hr hrs'))
        exact hsr.symm
  · intro hfamily
    constructor
    · exact hfamily.1
    · intro r hr s hs hrs
      exact (disjoint_squareOffsetPrimeSupport_iff_gcd_eq_one_or_fresh_prime
        (hfamily.1 r hr) (hfamily.1 s hs) hrs).mp
        (hfamily.2 hr hs (ne_of_lt hrs))

/-! ### PRIM-L030.8: gcd-form capacity / Frontier consumer -/

/-- The gcd/fresh family reuses the L029 capacity/frontier bridge. -/
theorem exists_prime_squareCell_of_pairwiseGcdFreshSeparatedSquareSeatFamily_card_excess
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hfamily : PairwiseGcdFreshSeparatedSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  exact exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
    hn ((pairwiseGcdFreshSeparatedSquareSeatFamily_iff_oldSupportDisjoint).mp hfamily)
    hcard

end DkMath.NumberTheory.Legendre
