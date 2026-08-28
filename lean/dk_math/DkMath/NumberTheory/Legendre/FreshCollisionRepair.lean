/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreshCollisionMatching
import DkMath.NumberTheory.Legendre.CoprimeSeatCapacity

#print "file: DkMath.NumberTheory.Legendre.FreshCollisionRepair"

/-!
## FreshCollisionRepair

The consecutive-cofactor normal form from `FreshCollisionMatching` has one
additional finite consequence: exactly one of `k` and `k + 1` is even.  Since
the fresh branch forces `2 ≤ n`, the old prime `2` belongs to exactly one
endpoint of every fresh collision.

Thus an old-support-disjoint finite family contains at most one non-coprime
fresh-collision pair.  Removing one endpoint of that exceptional pair repairs
the family to a complete-point pairwise-coprime family.  This is a finite
`+1` comparison between the L028 and L029 interfaces; it is not a universal
provider, a descent, or a proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-! ### PRIM-L032.1: prime `2` ownership -/

/-- A fresh collision necessarily occurs at an anchor with `2 ≤ n`. -/
theorem two_le_anchor_of_freshCollisionPair
    {n r s : ℕ} (hpair : FreshCollisionPair n r s) :
    2 ≤ n := by
  rcases hpair with ⟨hr, hs, hrs, hdisj, hg1⟩
  rcases freshCollision_consecutive_smallCofactor hr hs hrs hdisj hg1 with
    ⟨q, k, hq, hqLarge, hkpos, hkLe, hfacr, hfacs⟩
  omega

/-- Exactly one endpoint of a fresh collision contains old prime `2`. -/
theorem freshCollision_primeTwo_owner
    {n r s : ℕ} (hpair : FreshCollisionPair n r s) :
    (2 ∈ squareOffsetPrimeSupport n r ∧
      2 ∉ squareOffsetPrimeSupport n s) ∨
    (2 ∉ squareOffsetPrimeSupport n r ∧
      2 ∈ squareOffsetPrimeSupport n s) := by
  rcases hpair with ⟨hr, hs, hrs, hdisj, hg1⟩
  rcases freshCollision_consecutive_smallCofactor hr hs hrs hdisj hg1 with
    ⟨q, k, hq, hqLarge, hkpos, hkLe, hfacr, hfacs⟩
  have hn2 : 2 ≤ n := by omega
  have h2r : 2 ∈ squareOffsetPrimeSupport n r ↔ 2 ∣ k := by
    have h := mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
      (p := 2) hq hqLarge hfacr
    constructor
    · intro hmem
      exact (h.mp hmem).2.2
    · intro hdiv
      exact h.mpr ⟨Nat.prime_two, hn2, hdiv⟩
  have h2s : 2 ∈ squareOffsetPrimeSupport n s ↔ 2 ∣ (k + 1) := by
    have h := mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
      (p := 2) hq hqLarge hfacs
    constructor
    · intro hmem
      exact (h.mp hmem).2.2
    · intro hdiv
      exact h.mpr ⟨Nat.prime_two, hn2, hdiv⟩
  rcases Nat.mod_two_eq_zero_or_one k with hkmod | hkmod
  · have h2k : 2 ∣ k := Nat.dvd_iff_mod_eq_zero.mpr hkmod
    left
    refine ⟨h2r.mpr h2k, ?_⟩
    rw [h2s]
    intro h2next
    rcases h2k with ⟨a, ha⟩
    rcases h2next with ⟨b, hb⟩
    omega
  · right
    refine ⟨?_, ?_⟩
    · rw [h2r]
      intro h2k
      have hzero := Nat.dvd_iff_mod_eq_zero.mp h2k
      omega
    · rw [h2s]
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega

/-! ### PRIM-L032.2: one fresh collision in an old-support family -/

/-- A fresh collision's prime-`2` owner is unique inside an old-support family. -/
private theorem freshCollision_primeTwo_owner_eq
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    {a b : ℕ} (ha : a ∈ R) (hb : b ∈ R)
    (h2a : 2 ∈ squareOffsetPrimeSupport n a)
    (h2b : 2 ∈ squareOffsetPrimeSupport n b) :
    a = b := by
  by_contra hab
  have hdisj := hfamily.2 ha hb hab
  exact (Finset.disjoint_left.mp hdisj) h2a h2b

/-- Two fresh-collision pairs in one old-support family are the same pair. -/
theorem freshCollisionPair_unique_in_oldSupportFamily
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    {r s u v : ℕ}
    (hrs : FreshCollisionPair n r s)
    (huv : FreshCollisionPair n u v)
    (hr : r ∈ R) (hs : s ∈ R) (hu : u ∈ R) (hv : v ∈ R) :
    r = u ∧ s = v := by
  rcases freshCollision_primeTwo_owner hrs with hownerRS | hownerSR
  · rcases freshCollision_primeTwo_owner huv with hownerUV | hownerVU
    · have hru : r = u := freshCollision_primeTwo_owner_eq hfamily hr hu
        hownerRS.1 hownerUV.1
      subst u
      have hst := freshCollision_lower_endpoint_unique hrs huv
      exact ⟨rfl, hst⟩
    · have hrv : r = v := freshCollision_primeTwo_owner_eq hfamily hr hv
        hownerRS.1 hownerVU.2
      subst v
      exact (not_freshCollision_lower_and_upper hrs huv).elim
  · rcases freshCollision_primeTwo_owner huv with hownerUV | hownerVU
    · have hsu : s = u := freshCollision_primeTwo_owner_eq hfamily hs hu
        hownerSR.2 hownerUV.1
      subst u
      exact (not_freshCollision_lower_and_upper huv hrs).elim
    · have hsv : s = v := freshCollision_primeTwo_owner_eq hfamily hs hv
        hownerSR.2 hownerVU.2
      subst v
      exact ⟨freshCollision_upper_endpoint_unique hrs huv, rfl⟩

/-! ### PRIM-L032.3: the unique non-coprime exception -/

/-- A non-coprime ordered pair in an old-support family is a fresh collision. -/
theorem freshCollisionPair_of_not_coprime_of_oldSupportFamily
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    {r s : ℕ} (hr : r ∈ R) (hs : s ∈ R) (hrs : r < s)
    (hncop : ¬ Nat.Coprime (n ^ 2 + r) (n ^ 2 + s)) :
    FreshCollisionPair n r s := by
  have hdisj := hfamily.2 hr hs (ne_of_lt hrs)
  have hg1 : Nat.gcd (n ^ 2 + r) (n ^ 2 + s) ≠ 1 := by
    intro hg
    apply hncop
    exact Nat.coprime_iff_gcd_eq_one.mpr hg
  exact ⟨hfamily.1 r hr, hfamily.1 s hs, hrs, hdisj, hg1⟩

/-! ### PRIM-L032.4: one-seat complete-coprime repair -/

/-- The erased endpoint of a fresh exception is absent from the repaired family. -/
private theorem coprime_on_erase_of_oldSupportFamily
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    {r s : ℕ} (hrs : FreshCollisionPair n r s)
    (hr : r ∈ R) (hs : s ∈ R) :
    PairwiseCoprimeSquareSeatFamily n (R.erase s) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    exact hfamily.1 u (Finset.mem_of_mem_erase hu)
  · intro u hu v hv huv
    have huR := Finset.mem_of_mem_erase hu
    have hvR := Finset.mem_of_mem_erase hv
    by_contra hncop
    rcases lt_or_gt_of_ne huv with huvlt | hvult
    · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
        hfamily huR hvR huvlt hncop
      have hsame := freshCollisionPair_unique_in_oldSupportFamily
        hfamily hrs hcollision hr hs huR hvR
      exact (Finset.ne_of_mem_erase hv) hsame.2.symm
    · have hcollision := freshCollisionPair_of_not_coprime_of_oldSupportFamily
        hfamily hvR huR hvult (by
          intro hcop
          exact hncop hcop.symm)
      have hsame := freshCollisionPair_unique_in_oldSupportFamily
        hfamily hrs hcollision hr hs hvR huR
      exact (Finset.ne_of_mem_erase hu) hsame.2.symm

/-- An old-support-disjoint family becomes complete-coprime after deleting at most one seat. -/
theorem exists_pairwiseCoprimeSquareSeatFamily_subset_card_le_add_one
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R) :
    ∃ R' : Finset ℕ,
      R' ⊆ R ∧ PairwiseCoprimeSquareSeatFamily n R' ∧
        R.card ≤ R'.card + 1 := by
  classical
  by_cases hex : ∃ r s, r ∈ R ∧ s ∈ R ∧ FreshCollisionPair n r s
  · obtain ⟨r, s, hr, hs, hrs⟩ := hex
    refine ⟨R.erase s, Finset.erase_subset _ _,
      coprime_on_erase_of_oldSupportFamily hfamily hrs hr hs, ?_⟩
    rw [Finset.card_erase_of_mem hs]
    omega
  · refine ⟨R, subset_rfl, ?_, by omega⟩
    refine ⟨hfamily.1, ?_⟩
    intro r hr s hs hrs
    by_contra hncop
    rcases lt_or_gt_of_ne hrs with hrslt | hslt
    · exact hex ⟨r, s, hr, hs,
        freshCollisionPair_of_not_coprime_of_oldSupportFamily
          hfamily hr hs hrslt hncop⟩
    · exact hex ⟨s, r, hs, hr,
        freshCollisionPair_of_not_coprime_of_oldSupportFamily
          hfamily hs hr hslt (by
            intro hcop
            exact hncop hcop.symm)⟩

/-! ### PRIM-L032.5: interface comparison and frontier sanity consumer -/

/-- Complete-coprime families remain old-support-disjoint families. -/
theorem pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily_L032
    {n : ℕ} {R : Finset ℕ}
    (hfamily : PairwiseCoprimeSquareSeatFamily n R) :
    PairwiseOldSupportDisjointSquareSeatFamily n R :=
  pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily hfamily

/-- The one-seat repair leaves a strict L028 capacity excess when the margin is at least two. -/
theorem exists_prime_squareCell_of_oldSupportFamily_card_excess_two
    {n : ℕ} (hn : 0 < n) {R : Finset ℕ}
    (hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R)
    (hcard : (primeScalesUpTo n).card + 1 < R.card) :
    ∃ p, Nat.Prime p ∧ SquareCell n p := by
  obtain ⟨R', hsub, hcop, hcard'⟩ :=
    exists_pairwiseCoprimeSquareSeatFamily_subset_card_le_add_one hfamily
  have hcard'' : (primeScalesUpTo n).card < R'.card := by omega
  exact exists_prime_squareCell_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
    hn hcop hcard''

end DkMath.NumberTheory.Legendre
