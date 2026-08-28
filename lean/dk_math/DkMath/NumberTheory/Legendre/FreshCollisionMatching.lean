/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.OldSupportGcd
import DkMath.NumberTheory.Legendre.SmallCofactor

#print "file: DkMath.NumberTheory.Legendre.FreshCollisionMatching"

/-!
## FreshCollisionMatching

This module normalizes the nontrivial fresh branch left by `OldSupportGcd`.
For two ordered seats with disjoint old support and non-unit complete-point
gcd, the fresh prime is exactly the seat gap.  The two points are consequently
`q * k` and `q * (k + 1)` with `0 < k` and `k + 1 ≤ n`.

The same square-body bound makes the fresh prime unique at one shell point,
which gives endpoint uniqueness for the fresh-collision relation.  Bounded old
support transfers to the consecutive cofactors.  These are finite structural
facts only: the final full-cover theorem records the cofactor consequences but
does not construct a smaller Legendre state or prove Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L031.1: the fresh gcd is the ordered seat gap -/

/-- A nontrivial fresh collision has gap equal to its fresh gcd. -/
theorem freshCollision_gcd_eq_orderedOffsetGap
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s)
    (hdisj : Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s))
    (hg1 : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1) :
    s - r = Nat.gcd (n ^ 2 + r) (n ^ 2 + s) := by
  let q := Nat.gcd (n ^ 2 + r) (n ^ 2 + s)
  have hq : Nat.Prime q ∧ n < q := by
    exact prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
      hr hs hrs hdisj hg1
  have hqgap : q ∣ s - r := by
    dsimp [q]
    exact gcd_squarePoints_dvd_orderedOffsetGap hrs
  have hgap_lt : s - r < 2 * n := by
    dsimp [SquareOffset] at hr hs
    omega
  have hgap_lt_two_q : s - r < 2 * q := by omega
  obtain ⟨c, hc⟩ := hqgap
  have hcpos : 0 < c := by
    by_contra hc0
    have hc0' : c = 0 := Nat.eq_zero_of_not_pos hc0
    rw [hc0', mul_zero] at hc
    omega
  have hc_one : c = 1 := by
    by_contra hc_one
    have hc_two : 2 ≤ c := by omega
    nlinarith [hq.1.pos]
  have hgapq : s - r = q := by
    rw [hc_one, mul_one] at hc
    exact hc
  dsimp [q] at hgapq
  exact hgapq

/-- A fresh collision crosses the midpoint of the square-offset window. -/
theorem freshCollision_crosses_anchor
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s)
    (hdisj : Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s))
    (hg1 : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1) :
    r < n ∧ n < s := by
  have hq := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    hr hs hrs hdisj hg1
  have hgap := freshCollision_gcd_eq_orderedOffsetGap hr hs hrs hdisj hg1
  dsimp [SquareOffset] at hr hs
  constructor <;> omega

/-! ### PRIM-L031.2: consecutive bounded cofactors -/

/-- The two complete points of a fresh collision have consecutive cofactors. -/
theorem freshCollision_consecutive_smallCofactor
    {n r s : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s) (hrs : r < s)
    (hdisj : Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s))
    (hg1 : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1) :
    ∃ q k,
      Nat.Prime q ∧ n < q ∧ 0 < k ∧ k + 1 ≤ n ∧
        q * k = n ^ 2 + r ∧ q * (k + 1) = n ^ 2 + s := by
  let q := Nat.gcd (n ^ 2 + r) (n ^ 2 + s)
  have hq := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    hr hs hrs hdisj hg1
  have hqA : q ∣ n ^ 2 + r := by
    dsimp [q]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨k, hk⟩ := hqA
  have hkfac : q * k = n ^ 2 + r := hk.symm
  have hgap : s - r = q := by
    dsimp [q]
    exact freshCollision_gcd_eq_orderedOffsetGap hr hs hrs hdisj hg1
  have hfacB : q * (k + 1) = n ^ 2 + s := by
    have hsum : n ^ 2 + s = (n ^ 2 + r) + q := by omega
    calc
      q * (k + 1) = q * k + q := by ring
      _ = (n ^ 2 + r) + q := by rw [hkfac]
      _ = n ^ 2 + s := hsum.symm
  have hApos : 0 < n ^ 2 + r := squarePoint_pos_of_squareOffset hr
  have hkpos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk0', mul_zero] at hkfac
    exact (Nat.ne_of_gt hApos) hkfac.symm
  have hBlt : n ^ 2 + s < (n + 1) ^ 2 := by
    dsimp [SquareOffset] at hs
    nlinarith
  have hkLe : k + 1 ≤ n := by
    have hqanchor : n + 1 ≤ q := by omega
    by_contra hkLe
    have hkanchor : n + 1 ≤ k + 1 := by omega
    have hprod : (n + 1) * (n + 1) ≤ q * (k + 1) :=
      Nat.mul_le_mul hqanchor hkanchor
    rw [hfacB] at hprod
    have hprod' : (n + 1) ^ 2 ≤ n ^ 2 + s := by
      simpa [pow_two] using hprod
    exact (not_lt_of_ge hprod') hBlt
  refine ⟨q, k, hq.1, hq.2, hkpos, hkLe, hkfac, hfacB⟩

/-! ### PRIM-L031.3: one fresh prime per shell point -/

/-- Two prime divisors above the anchor of one shell point coincide. -/
theorem unique_fresh_prime_divisor_of_squareOffset
    {n r q₁ q₂ : ℕ}
    (hr : SquareOffset n r)
    (hq₁ : Nat.Prime q₁) (hq₂ : Nat.Prime q₂)
    (hq₁large : n < q₁) (hq₂large : n < q₂)
    (hq₁dvd : q₁ ∣ n ^ 2 + r) (hq₂dvd : q₂ ∣ n ^ 2 + r) :
    q₁ = q₂ := by
  exact eq_of_large_primes_dvd_le_squareBody
    (squarePoint_pos_of_squareOffset hr)
    (squarePoint_le_squareBody_of_squareOffset hr)
    hq₁ hq₂ hq₁large hq₂large hq₁dvd hq₂dvd

/-! ### PRIM-L031.4: endpoint matching -/

/-- The minimal arithmetic relation represented by a fresh collision pair. -/
def FreshCollisionPair (n r s : ℕ) : Prop :=
  SquareOffset n r ∧ SquareOffset n s ∧ r < s ∧
    Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s) ∧
    Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1

private theorem freshCollisionPair_data
    {n r s : ℕ} (h : FreshCollisionPair n r s) :
    SquareOffset n r ∧ SquareOffset n s ∧ r < s ∧
      Disjoint (squareOffsetPrimeSupport n r)
        (squareOffsetPrimeSupport n s) ∧
      Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1 := h

/-- A lower seat has at most one nontrivial fresh collision partner. -/
theorem freshCollision_lower_endpoint_unique
    {n r s t : ℕ}
    (hrs : FreshCollisionPair n r s)
    (hrt : FreshCollisionPair n r t) :
    s = t := by
  rcases freshCollisionPair_data hrs with ⟨hr, hs, hrs, hdisjs, hg1s⟩
  rcases freshCollisionPair_data hrt with ⟨hr', ht, hrt, hdisjt, hg1t⟩
  have hqS := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    hr hs hrs hdisjs hg1s
  have hqT := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    hr' ht hrt hdisjt hg1t
  have hqeq : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) =
      Nat.gcd (n ^ 2 + r) (n ^ 2 + t) := by
    apply unique_fresh_prime_divisor_of_squareOffset hr
      hqS.1 hqT.1 hqS.2 hqT.2
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_refl _)
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_refl _)
  have hgapS := freshCollision_gcd_eq_orderedOffsetGap hr hs hrs hdisjs hg1s
  have hgapT := freshCollision_gcd_eq_orderedOffsetGap hr' ht hrt hdisjt hg1t
  omega

/-- An upper seat has at most one nontrivial fresh collision partner. -/
theorem freshCollision_upper_endpoint_unique
    {n r s t : ℕ}
    (hrs : FreshCollisionPair n r s)
    (hts : FreshCollisionPair n t s) :
    r = t := by
  rcases freshCollisionPair_data hrs with ⟨hr, hs, hrs, hdisjs, hg1s⟩
  rcases freshCollisionPair_data hts with ⟨ht, hs', hts, hdisjt, hg1t⟩
  have hqS := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    hr hs hrs hdisjs hg1s
  have hqT := prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one
    ht hs' hts hdisjt hg1t
  have hqeq : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) =
      Nat.gcd (n ^ 2 + t) (n ^ 2 + s) := by
    apply unique_fresh_prime_divisor_of_squareOffset hs
      hqS.1 hqT.1 hqS.2 hqT.2
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.dvd_refl _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.dvd_refl _)
  have hgapS := freshCollision_gcd_eq_orderedOffsetGap hr hs hrs hdisjs hg1s
  have hgapT := freshCollision_gcd_eq_orderedOffsetGap ht hs' hts hdisjt hg1t
  omega

/-- A seat cannot be the lower endpoint and upper endpoint of fresh collisions. -/
theorem not_freshCollision_lower_and_upper
    {n r s t : ℕ}
    (hrs : FreshCollisionPair n r s)
    (htr : FreshCollisionPair n t r) :
    False := by
  have hleft := freshCollisionPair_data hrs
  have hright := freshCollisionPair_data htr
  have hcross₁ := freshCollision_crosses_anchor
    hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2.1 hleft.2.2.2.2
  have hcross₂ := freshCollision_crosses_anchor
    hright.1 hright.2.1 hright.2.2.1 hright.2.2.2.1 hright.2.2.2.2
  omega

/-! ### PRIM-L031.5: old support transfer to consecutive cofactors -/

/-- A bounded support prime of a fresh split is exactly a cofactor prime. -/
theorem mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
    {n r q k p : ℕ}
    (hq : Nat.Prime q) (hqLarge : n < q)
    (hfac : q * k = n ^ 2 + r) :
    p ∈ squareOffsetPrimeSupport n r ↔
      Nat.Prime p ∧ p ≤ n ∧ p ∣ k := by
  constructor
  · intro hp
    have hp' := mem_squareOffsetPrimeSupport.mp hp
    have hprod : p ∣ q * k := by rw [hfac]; exact hp'.2.2
    rcases (Nat.Prime.dvd_mul hp'.1).mp hprod with hpq | hpk
    · have hpq' : p = q :=
        ((Nat.dvd_prime hq).mp hpq).resolve_left hp'.1.ne_one
      omega
    · exact ⟨hp'.1, hp'.2.1, hpk⟩
  · rintro ⟨hp, hpLe, hpk⟩
    apply mem_squareOffsetPrimeSupport.mpr
    refine ⟨hp, hpLe, ?_⟩
    rw [← hfac]
    exact dvd_mul_of_dvd_right hpk q

/-- The consecutive fresh cofactors are old-generated. -/
theorem primeScaleGeneratedBy_freshCollision_cofactors
    {n r s q k : ℕ}
    (hr : SquareOffset n r) (hs : SquareOffset n s)
    (hq : Nat.Prime q) (hqLarge : n < q)
    (hfacr : q * k = n ^ 2 + r)
    (hfacs : q * (k + 1) = n ^ 2 + s) :
    PrimeScaleGeneratedBy (primeScalesUpTo n) k ∧
      PrimeScaleGeneratedBy (primeScalesUpTo n) (k + 1) := by
  have hkr := primeScaleGeneratedBy_div_of_large_prime_dvd_le_squareBody
    (squarePoint_pos_of_squareOffset hr)
    (squarePoint_le_squareBody_of_squareOffset hr) hq hqLarge
    (by rw [← hfacr]; exact dvd_mul_right q k)
  have hks := primeScaleGeneratedBy_div_of_large_prime_dvd_le_squareBody
    (squarePoint_pos_of_squareOffset hs)
    (squarePoint_le_squareBody_of_squareOffset hs) hq hqLarge
    (by rw [← hfacs]; exact dvd_mul_right q (k + 1))
  have hdivr : (n ^ 2 + r) / q = k := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    calc
      q * ((n ^ 2 + r) / q) = n ^ 2 + r := Nat.mul_div_cancel' (by
        rw [← hfacr]; exact dvd_mul_right q k)
      _ = q * k := hfacr.symm
  have hdivs : (n ^ 2 + s) / q = k + 1 := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    calc
      q * ((n ^ 2 + s) / q) = n ^ 2 + s := Nat.mul_div_cancel' (by
        rw [← hfacs]; exact dvd_mul_right q (k + 1))
      _ = q * (k + 1) := hfacs.symm
  rw [hdivr] at hkr
  rw [hdivs] at hks
  exact ⟨hkr, hks⟩

/-! ### PRIM-L031.6: full-cover cofactor consequence -/

/-- Full cover forces old prime content into both consecutive cofactors. -/
theorem freshCollision_cofactors_oldCovered_of_fullyCovered
    {n r s : ℕ}
    (hfull : SquareOffsetsFullyCovered n)
    (hpair : FreshCollisionPair n r s) :
    ∃ q k,
      Nat.Prime q ∧ n < q ∧ 2 ≤ k ∧ k + 1 ≤ n ∧
        q * k = n ^ 2 + r ∧ q * (k + 1) = n ^ 2 + s ∧
        (∃ p, Nat.Prime p ∧ p ≤ n ∧ p ∣ k) ∧
        (∃ p, Nat.Prime p ∧ p ≤ n ∧ p ∣ (k + 1)) := by
  rcases freshCollisionPair_data hpair with ⟨hr, hs, hrs, hdisj, hg1⟩
  rcases freshCollision_consecutive_smallCofactor hr hs hrs hdisj hg1 with
    ⟨q, k, hq, hqLarge, hkpos, hkLe, hfacr, hfacs⟩
  have hcoveredr : SquareOffsetCovered n r := hfull r hr
  have hcovereds : SquareOffsetCovered n s := hfull s hs
  have hk2 := two_le_smallCofactor_of_covered_fresh_split
    hr hcoveredr hq hqLarge hkpos hfacr
  have hmemr : (squareOffsetPrimeSupport n r).Nonempty :=
    squareOffsetCovered_iff_primeSupport_nonempty.mp hcoveredr
  have hmems : (squareOffsetPrimeSupport n s).Nonempty :=
    squareOffsetCovered_iff_primeSupport_nonempty.mp hcovereds
  obtain ⟨p, hp⟩ := hmemr
  obtain ⟨p', hp'⟩ := hmems
  have hpk := (mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
    hq hqLarge hfacr).mp hp
  have hpk' := (mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
    hq hqLarge hfacs).mp hp'
  refine ⟨q, k, hq, hqLarge, hk2, hkLe, hfacr, hfacs, ?_, ?_⟩
  · exact ⟨p, hpk.1, hpk.2.1, hpk.2.2⟩
  · exact ⟨p', hpk'.1, hpk'.2.1, hpk'.2.2⟩

/-! ### PRIM-L031.7: explicit boundary -/

/-- The accepted fresh-collision witness specializes to `5 * 2` and `5 * 3`. -/
theorem freshCollision_three_one_six_consecutive_cofactor :
    FreshCollisionPair 3 1 6 ∧
      (∃ q k, q = 5 ∧ k = 2 ∧
        q * k = 3 ^ 2 + 1 ∧ q * (k + 1) = 3 ^ 2 + 6) := by
  have hpair : FreshCollisionPair 3 1 6 := by
    refine ⟨squareOffset_oldSupportCapacity_strictness_left,
      squareOffset_oldSupportCapacity_strictness_right,
      by norm_num, disjoint_oldSupportCapacity_strictness_supports,
      by norm_num⟩
  refine ⟨hpair, ?_⟩
  rcases freshCollision_consecutive_smallCofactor
      hpair.1 hpair.2.1 hpair.2.2.1 hpair.2.2.2.1 hpair.2.2.2.2 with
    ⟨q, k, hq, hqLarge, hkpos, hkLe, hfacr, hfacs⟩
  refine ⟨q, k, ?_, ?_, hfacr, hfacs⟩
  · nlinarith [hfacr, hfacs]
  · have hqeq : q = 5 := by nlinarith [hfacr, hfacs]
    rw [hqeq] at hfacr
    norm_num at hfacr
    omega

end DkMath.NumberTheory.Legendre
