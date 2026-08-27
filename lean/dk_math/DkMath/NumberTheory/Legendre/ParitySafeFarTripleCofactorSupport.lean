/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport"

/-!
## ParitySafeFarTripleCofactorSupport

PRIM-L045 replaces the noninjective single returned-prime view of an L044
cofactor by its complete finite prime support.  For a fixed far residual seat,
the active support is exactly the three selected directions together with the
prime support of the complementary cofactor.  Every cofactor prime remains in
the same half-scale active world and candidate support.

The support decomposition is seat-local.  It does not make the cofactor value,
one returned prime, or the cofactor support without its seat a global charge
key.  No smaller-anchor cover, infinite descent, or global cardinality
contradiction is asserted.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal

/-! ### PRIM-L045.1: finite cofactor prime support -/

/-- The complete finite prime support of the L044 complementary cofactor. -/
noncomputable def paritySafeFarTripleCofactorPrimeSupport
    (n r q s : ℕ) : Finset ℕ :=
  Nat.primeFactors (paritySafeFarTripleCofactor n r q s)

/-- Membership in the cofactor prime support under a far packet. -/
theorem mem_paritySafeFarTripleCofactorPrimeSupport
    {n r q s u : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    u ∈ paritySafeFarTripleCofactorPrimeSupport n r q s ↔
      Nat.Prime u ∧ u ∣ paritySafeFarTripleCofactor n r q s := by
  have htpos := (paritySafeFarTripleCofactor_packet hinc hfar).1
  rw [paritySafeFarTripleCofactorPrimeSupport,
    Nat.mem_primeFactors_of_ne_zero (Nat.ne_of_gt htpos)]

/-! ### PRIM-L045.2: full-support return -/

/-- Every prime in the cofactor support returns to the half-scale active world.
-/
theorem paritySafeFarTripleCofactorPrimeSupport_subset_halfScale
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactorPrimeSupport n r q s ⊆
      paritySafeHalfScaleActivePrimes n := by
  intro u hu
  have hu' := (mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mp hu
  exact (paritySafeFarTripleCofactor_prime_divisor_halfScale_return
    hinc hfar hu'.1 hu'.2).1

/-- Every prime in the cofactor support belongs to the candidate's active
support at the original anchor. -/
theorem paritySafeFarTripleCofactorPrimeSupport_subset_activeSupport
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactorPrimeSupport n r q s ⊆
      paritySafeActiveSupport n r := by
  intro u hu
  have hu' := (mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mp hu
  exact (paritySafeFarTripleCofactor_prime_divisor_halfScale_return
    hinc hfar hu'.1 hu'.2).2

private theorem paritySafeFarTripleCofactor_triple_support
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r := by
  have hinc' := Finset.mem_filter.mp hinc
  have hprod := Finset.mem_product.mp hinc'.1
  have hcovered : r ∈ paritySafeCoveredCandidates n := hprod.1
  have hcond := hinc'.2
  have hqerase := hcond.2.1
  have hserase := hcond.2.2
  have hpoff :=
    (paritySafeCanonicalSupportPrime_packet hcovered).2.2.1
  have hsupport :=
    squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
      (mem_paritySafeCoveredCandidates.mp hcovered).1
  have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    hpoff (Finset.erase_subset _ _ hqerase)
  have hsoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    hpoff (Finset.erase_subset _ _ hserase)
  rw [hsupport] at hqoff hsoff
  exact ⟨paritySafeCanonicalSupportPrime_mem_activeSupport hcovered, hqoff, hsoff⟩

/-! ### PRIM-L045.3: exact active-support decomposition -/

set_option maxHeartbeats 800000 in
-- Extensional decomposition splits prime divisibility through a four-factor
-- product and needs a larger local elaboration budget.
/-- The fixed far seat's active support is the selected triple plus the full
prime support of its complementary cofactor. -/
theorem paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeActiveSupport n r =
      insert (paritySafeCanonicalSupportPrime n r)
        (insert q
          (insert s
            (paritySafeFarTripleCofactorPrimeSupport n r q s))) := by
  classical
  let p := paritySafeCanonicalSupportPrime n r
  have htriple := paritySafeFarTripleCofactor_triple_support hinc
  have hfactor := (paritySafeFarTripleCofactor_packet hinc hfar).2.1
  have hactive : ∀ {u : ℕ}, u ∈ paritySafeActiveSupport n r →
      u = p ∨ u = q ∨ u = s ∨
        u ∈ paritySafeFarTripleCofactorPrimeSupport n r q s := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have huprime := (mem_squareAnchorOddActivePrimes.mp hu'.1).1
    have huN : u ∣ n ^ 2 + r := hu'.2
    have hudvd : u ∣ p * q * s * paritySafeFarTripleCofactor n r q s := by
      rw [hfactor]
      exact huN
    rcases (huprime.dvd_mul).mp hudvd with hpqs | hut
    · rcases (huprime.dvd_mul).mp hpqs with hpq | hus
      · rcases (huprime.dvd_mul).mp hpq with hup | huq
        · left
          exact ((Nat.dvd_prime
            (mem_squareAnchorOddActivePrimes.mp
              (Finset.mem_filter.mp htriple.1).1).1).mp hup).resolve_left
            huprime.ne_one
        · right; left
          exact ((Nat.dvd_prime
            (mem_squareAnchorOddActivePrimes.mp
              (Finset.mem_filter.mp htriple.2.1).1).1).mp huq).resolve_left
            huprime.ne_one
      · right; right; left
        exact ((Nat.dvd_prime
          (mem_squareAnchorOddActivePrimes.mp
            (Finset.mem_filter.mp htriple.2.2).1).1).mp hus).resolve_left
          huprime.ne_one
    · right; right; right
      exact (mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mpr
        ⟨huprime, hut⟩
  ext u
  constructor
  · intro hu
    rcases hactive hu with hpu | hqu | hsu | hut
    · exact Finset.mem_insert.mpr (Or.inl hpu)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hqu)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hsu)))))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hut)))))
  · intro hu
    simp only [Finset.mem_insert] at hu
    rcases hu with rfl | rfl | rfl | hu
    · exact htriple.1
    · exact htriple.2.1
    · exact htriple.2.2
    · exact (paritySafeFarTripleCofactorPrimeSupport_subset_activeSupport
        hinc hfar) hu

/-! ### PRIM-L045.4: no-depth cardinal recharge -/

private theorem paritySafeFarTripleCofactor_primeSquare_of_dvd
    {n r p q s a : ℕ}
    (hfactor : p * q * s * paritySafeFarTripleCofactor n r q s = n ^ 2 + r)
    (ha : a ∣ p * q * s)
    (hat : a ∣ paritySafeFarTripleCofactor n r q s) :
    a ^ 2 ∣ n ^ 2 + r := by
  have hsq : a * a ∣ p * q * s * paritySafeFarTripleCofactor n r q s :=
    Nat.mul_dvd_mul ha hat
  rw [hfactor] at hsq
  simpa [pow_two] using hsq

private theorem paritySafeFarTripleCofactor_primeSupport_excludes_three
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (hpdepth : ¬ p ^ 2 ∣ n ^ 2 + r)
    (hqdepth : ¬ q ^ 2 ∣ n ^ 2 + r)
    (hsdepth : ¬ s ^ 2 ∣ n ^ 2 + r) :
    p ∉ paritySafeFarTripleCofactorPrimeSupport n r q s ∧
      q ∉ paritySafeFarTripleCofactorPrimeSupport n r q s ∧
      s ∉ paritySafeFarTripleCofactorPrimeSupport n r q s := by
  subst p
  have hfactor := (paritySafeFarTripleCofactor_packet hinc hfar).2.1
  have hpbase : paritySafeCanonicalSupportPrime n r ∣
      paritySafeCanonicalSupportPrime n r * q * s := by
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hqbase : q ∣ paritySafeCanonicalSupportPrime n r * q * s := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl q) _) _
  have hsbase : s ∣ paritySafeCanonicalSupportPrime n r * q * s := by
    exact dvd_mul_of_dvd_right (dvd_refl s) _
  constructor
  · intro hp'
    apply hpdepth
    exact paritySafeFarTripleCofactor_primeSquare_of_dvd hfactor hpbase
      ((mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mp hp').2
  constructor
  · intro hq'
    apply hqdepth
    exact paritySafeFarTripleCofactor_primeSquare_of_dvd hfactor hqbase
      ((mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mp hq').2
  · intro hs'
    apply hsdepth
    exact paritySafeFarTripleCofactor_primeSquare_of_dvd hfactor hsbase
      ((mem_paritySafeFarTripleCofactorPrimeSupport hinc hfar).mp hs').2

/-- In the no-depth branch, the active-support cardinality is exactly three
plus the number of distinct prime divisors of the cofactor. -/
theorem paritySafeActiveSupport_card_eq_three_add_cofactorPrimeSupport_card
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (hpdepth : ¬ p ^ 2 ∣ n ^ 2 + r)
    (hqdepth : ¬ q ^ 2 ∣ n ^ 2 + r)
    (hsdepth : ¬ s ^ 2 ∣ n ^ 2 + r) :
    (paritySafeActiveSupport n r).card =
      3 + (paritySafeFarTripleCofactorPrimeSupport n r q s).card := by
  subst p
  have hne := paritySafeFarTripleCofactor_primeSupport_excludes_three
    hinc hfar rfl hpdepth hqdepth hsdepth
  have htriple := paritySafeFarTripleCofactor_triple_support hinc
  have hdecomp := paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport
    hinc hfar
  rw [hdecomp]
  rcases paritySafeCanonicalResidualTripleIncidence_packet hinc with
    ⟨_, _, _, _, hpq, hps, hqs, _, _⟩
  have hqnot : q ∉ insert s
      (paritySafeFarTripleCofactorPrimeSupport n r q s) := by
    simp [hqs, hne.2.1]
  have hpnot : paritySafeCanonicalSupportPrime n r ∉ insert q
      (insert s (paritySafeFarTripleCofactorPrimeSupport n r q s)) := by
    simp [hpq, hps, hne.1]
  simp [hpnot, hqnot, hne.2.2]; omega

/-! ### PRIM-L045.5: exact erase complement -/

/-- In the no-depth branch, the cofactor prime support is the active support
with the selected triple erased. -/
theorem paritySafeFarTripleCofactorPrimeSupport_eq_activeSupport_erase_three
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (hpdepth : ¬ p ^ 2 ∣ n ^ 2 + r)
    (hqdepth : ¬ q ^ 2 ∣ n ^ 2 + r)
    (hsdepth : ¬ s ^ 2 ∣ n ^ 2 + r) :
    paritySafeFarTripleCofactorPrimeSupport n r q s =
      (((paritySafeActiveSupport n r).erase p).erase q).erase s := by
  classical
  subst p
  have hne := paritySafeFarTripleCofactor_primeSupport_excludes_three
    hinc hfar rfl hpdepth hqdepth hsdepth
  have hdecomp := paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport
    hinc hfar
  ext u
  constructor
  · intro hu
    have hneqp : u ≠ paritySafeCanonicalSupportPrime n r := by
      intro heq
      subst u
      exact (hne.1 hu).elim
    have hneqq : u ≠ q := by
      intro heq
      subst u
      exact (hne.2.1 hu).elim
    have hneqs : u ≠ s := by
      intro heq
      subst u
      exact (hne.2.2 hu).elim
    refine Finset.mem_erase.mpr ⟨hneqs, Finset.mem_erase.mpr ⟨hneqq,
      Finset.mem_erase.mpr ⟨hneqp, ?_⟩⟩⟩
    exact (paritySafeFarTripleCofactorPrimeSupport_subset_activeSupport
      hinc hfar) hu
  · intro hu
    have hu' := Finset.mem_erase.mp hu
    have hu'' := Finset.mem_erase.mp hu'.2
    have hu''' := Finset.mem_erase.mp hu''.2
    have husupport : u ∈ paritySafeActiveSupport n r := hu'''.2
    have huinsert : u ∈ insert (paritySafeCanonicalSupportPrime n r)
        (insert q (insert s
          (paritySafeFarTripleCofactorPrimeSupport n r q s))) := by
      rw [← hdecomp]
      exact husupport
    simp only [Finset.mem_insert] at huinsert
    rcases huinsert with hpu | hqu | hsu | hut
    · exact (hu'''.1 hpu).elim
    · exact (hu''.1 hqu).elim
    · exact (hu'.1 hsu).elim
    · exact hut

/-! ### PRIM-L045.6: seat-local ownership -/

/-- With the seat `r` and canonical prime fixed, equal cofactor prime supports
determine the canonically ordered residual pair in the no-depth branch.

This is deliberately local: the seat coordinate is part of the hypotheses,
so the theorem does not turn cofactor support into a global key.
-/
theorem paritySafeFarTripleCofactorPrimeSupport_local_injective
    {n r q₁ s₁ q₂ s₂ : ℕ}
    (hinc₁ : (r, (q₁, s₁)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₁ : (paritySafeCanonicalSupportPrime n r, (q₁, s₁)) ∈
      paritySafeTripleGateFarTriples n)
    (hinc₂ : (r, (q₂, s₂)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar₂ : (paritySafeCanonicalSupportPrime n r, (q₂, s₂)) ∈
      paritySafeTripleGateFarTriples n)
    (hpdepth : ¬ (paritySafeCanonicalSupportPrime n r) ^ 2 ∣ n ^ 2 + r)
    (hqdepth₁ : ¬ q₁ ^ 2 ∣ n ^ 2 + r)
    (hsdepth₁ : ¬ s₁ ^ 2 ∣ n ^ 2 + r)
    (hsupp : paritySafeFarTripleCofactorPrimeSupport n r q₁ s₁ =
      paritySafeFarTripleCofactorPrimeSupport n r q₂ s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  classical
  have hne₁ := paritySafeFarTripleCofactor_primeSupport_excludes_three
    hinc₁ hfar₁ rfl hpdepth hqdepth₁ hsdepth₁
  have hdecomp₂ := paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport
    hinc₂ hfar₂
  rcases paritySafeCanonicalResidualTripleIncidence_packet hinc₁ with
    ⟨_, _, _, _, hpq₁, hps₁, hq₁s₁, _, _⟩
  have hq₁lt : q₁ < s₁ := (Finset.mem_filter.mp hinc₁).2.1
  have hq₂lt : q₂ < s₂ := (Finset.mem_filter.mp hinc₂).2.1
  have hq₁cases : q₁ = paritySafeCanonicalSupportPrime n r ∨
      q₁ = q₂ ∨ q₁ = s₂ ∨
      q₁ ∈ paritySafeFarTripleCofactorPrimeSupport n r q₂ s₂ := by
    have hq₁support := (paritySafeFarTripleCofactor_triple_support hinc₁).2.1
    rw [hdecomp₂] at hq₁support
    simpa only [Finset.mem_insert] using hq₁support
  have hqchoice : q₁ = q₂ ∨ q₁ = s₂ := by
    rcases hq₁cases with hp | hq | hs | hco
    · exact False.elim (hpq₁ hp.symm)
    · exact Or.inl hq
    · exact Or.inr hs
    · exfalso
      apply hne₁.2.1
      rw [hsupp]
      exact hco
  rcases hqchoice with hqeq | hqeq
  · have hs₁cases : s₁ = paritySafeCanonicalSupportPrime n r ∨
        s₁ = q₂ ∨ s₁ = s₂ ∨
        s₁ ∈ paritySafeFarTripleCofactorPrimeSupport n r q₂ s₂ := by
      have hs₁support := (paritySafeFarTripleCofactor_triple_support hinc₁).2.2
      rw [hdecomp₂] at hs₁support
      simpa only [Finset.mem_insert] using hs₁support
    rcases hs₁cases with hp | hq | hs | hco
    · exact ⟨hqeq, False.elim (hps₁ hp.symm)⟩
    · exfalso
      omega
    · exact ⟨hqeq, hs⟩
    · exfalso
      apply hne₁.2.2
      rw [hsupp]
      exact hco
  · have hs₁cases : s₁ = paritySafeCanonicalSupportPrime n r ∨
        s₁ = q₂ ∨ s₁ = s₂ ∨
        s₁ ∈ paritySafeFarTripleCofactorPrimeSupport n r q₂ s₂ := by
      have hs₁support := (paritySafeFarTripleCofactor_triple_support hinc₁).2.2
      rw [hdecomp₂] at hs₁support
      simpa only [Finset.mem_insert] using hs₁support
    rcases hs₁cases with hp | hq | hs | hco
    · exfalso
      exact hps₁ hp.symm
    · exfalso
      omega
    · exfalso
      exact hq₁s₁ (hqeq.trans hs.symm)
    · exfalso
      apply hne₁.2.2
      rw [hsupp]
      exact hco

end DkMath.NumberTheory.Legendre
