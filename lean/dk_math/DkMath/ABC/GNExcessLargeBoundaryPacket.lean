/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessEulerMajorant
import DkMath.ABC.GNPrimeSupportOrder

#print "file: DkMath.ABC.GNExcessLargeBoundaryPacket"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exact arithmetic form of the GN large-boundary modulus

This module packages the full prime powers occurring with multiplicity at
least two.  It reconnects the excess-active CRT modulus with the legacy
`piSqRad`/`sqTail`/`twoTail` coordinates.

No estimate for the sum of large-boundary profile weights is asserted here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The full prime-power part of `n` supported on valuations at least two. -/
noncomputable def repeatedPrimePowerPart (n : ℕ) : ℕ :=
  (n.factorization.support.filter
    (fun q => 2 ≤ n.factorization q)).prod
      (fun q => q ^ n.factorization q)

/-- The repeated part is positive. -/
theorem repeatedPrimePowerPart_pos (n : ℕ) :
    0 < repeatedPrimePowerPart n := by
  classical
  unfold repeatedPrimePowerPart
  exact Finset.prod_pos fun q hq =>
    pow_pos
      (mem_support_factorization_iff.mp
        (Finset.mem_filter.mp hq).1).2.1.pos _

/-- Exact factorization of the repeated prime-power part. -/
theorem repeatedPrimePowerPart_factorization
    (n r : ℕ) :
    (repeatedPrimePowerPart n).factorization r =
      if r ∈ n.factorization.support ∧
          2 ≤ n.factorization r then
        n.factorization r
      else 0 := by
  classical
  let S :=
    n.factorization.support.filter
      (fun q => 2 ≤ n.factorization q)
  let f := fun q => q ^ n.factorization q
  have hprime :
      ∀ q ∈ S, Nat.Prime q := by
    intro q hq
    exact (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  have hnonzero :
      ∀ q ∈ S, f q ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (hprime q hq).ne_zero
  have hfac :=
    congrArg (fun g : ℕ →₀ ℕ => g r)
      (Nat.factorization_prod hnonzero)
  have hfac' :
      (repeatedPrimePowerPart n).factorization r =
        ∑ q ∈ S, (f q).factorization r := by
    simpa only [repeatedPrimePowerPart, S, f,
      Finsupp.coe_finsetSum, Finset.sum_apply] using hfac
  rw [hfac']
  simp only [f, Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
  by_cases hr : r ∈ S
  · have hr' :
        r ∈ n.factorization.support ∧
          2 ≤ n.factorization r :=
      Finset.mem_filter.mp hr
    rw [if_pos hr']
    calc
      ∑ q ∈ S,
          n.factorization q * q.factorization r =
        n.factorization r * r.factorization r := by
          apply Finset.sum_eq_single r
          · intro q hq hqr
            rw [(hprime q hq).factorization,
              Finsupp.single_apply]
            simp [hqr]
          · intro hrnot
            exact False.elim (hrnot hr)
      _ = n.factorization r := by
          rw [(hprime r hr).factorization,
            Finsupp.single_eq_same]
          simp
  · have hr' :
        ¬(r ∈ n.factorization.support ∧
          2 ≤ n.factorization r) := by
      simpa [S] using hr
    rw [if_neg hr']
    apply Finset.sum_eq_zero
    intro q hq
    rw [(hprime q hq).factorization,
      Finsupp.single_apply]
    simp only [mul_eq_zero]
    right
    simp only [ite_eq_right_iff]
    intro hqr
    subst q
    exact False.elim (hr hq)

/-- The factorization support of the repeated part is exactly the set of
prime factors occurring to depth at least two. -/
theorem repeatedPrimePowerPart_factorization_support
    (n : ℕ) :
    (repeatedPrimePowerPart n).factorization.support =
      n.factorization.support.filter
        (fun q => 2 ≤ n.factorization q) := by
  classical
  ext r
  rw [Finsupp.mem_support_iff,
    repeatedPrimePowerPart_factorization]
  by_cases hr :
      r ∈ n.factorization.support ∧
        2 ≤ n.factorization r
  · rw [if_pos hr]
    exact iff_of_true (by omega) (Finset.mem_filter.mpr hr)
  · rw [if_neg hr]
    exact iff_of_false (by simp) fun h =>
      hr (Finset.mem_filter.mp h)

/-- The repeated part is the square support shell times the old square-free
tail quotient. -/
theorem repeatedPrimePowerPart_eq_piSqRad_mul_sqTail
    {n : ℕ}
    (hn : n ≠ 0) :
    repeatedPrimePowerPart n =
      piSqRad n * sqTail n := by
  classical
  let S :=
    n.factorization.support.filter
      (fun q => 2 ≤ n.factorization q)
  have htail :
      (∏ q ∈ S, q ^ (n.factorization q - 2)) =
        twoTail n := by
    unfold twoTail
    apply Finset.prod_subset
      (s₁ := S) (s₂ := n.factorization.support)
    · exact Finset.filter_subset _ _
    · intro q hqs hqnot
      have hlt :
          n.factorization q < 2 := by
        by_contra hnot
        exact hqnot
          (Finset.mem_filter.mpr
            ⟨hqs, Nat.le_of_not_gt hnot⟩)
      simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  have hsplit :
      repeatedPrimePowerPart n =
        (piSqRad n) ^ 2 * twoTail n := by
    unfold repeatedPrimePowerPart piSqRad
    change
      (∏ q ∈ S, q ^ n.factorization q) =
        (∏ q ∈ S, q) ^ 2 * twoTail n
    calc
      (∏ q ∈ S, q ^ n.factorization q) =
          ∏ q ∈ S,
            (q ^ 2 * q ^ (n.factorization q - 2)) := by
        apply Finset.prod_congr rfl
        intro q hq
        have hv : 2 ≤ n.factorization q :=
          (Finset.mem_filter.mp hq).2
        rw [← pow_add, Nat.add_sub_of_le hv]
      _ = (∏ q ∈ S, q ^ 2) *
          (∏ q ∈ S,
            q ^ (n.factorization q - 2)) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ q ∈ S, q) ^ 2 *
          (∏ q ∈ S,
            q ^ (n.factorization q - 2)) := by
        rw [Finset.prod_pow]
      _ = (∏ q ∈ S, q) ^ 2 * twoTail n := by
        rw [htail]
  rw [hsplit, sqTail_eq_piSqRad_mul_twoTail n hn]
  ring

/-- Equivalent legacy form: the repeated part consists of two copies of the
repeated support and the depth-three tail. -/
theorem repeatedPrimePowerPart_eq_piSqRad_sq_mul_twoTail
    {n : ℕ}
    (hn : n ≠ 0) :
    repeatedPrimePowerPart n =
      (piSqRad n) ^ 2 * twoTail n := by
  rw [repeatedPrimePowerPart_eq_piSqRad_mul_sqTail hn,
    sqTail_eq_piSqRad_mul_twoTail n hn]
  ring

/-- The repeated prime-power part divides the original number. -/
theorem repeatedPrimePowerPart_dvd
    {n : ℕ}
    (hn : n ≠ 0) :
    repeatedPrimePowerPart n ∣ n := by
  rcases piSqRad_dvd_rad n with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    n = sqTail n * rad n :=
      nat_eq_sqTail_mul_rad n hn
    _ = sqTail n * (piSqRad n * k) := by rw [hk]
    _ = (piSqRad n * sqTail n) * k := by ac_rfl
    _ = repeatedPrimePowerPart n * k := by
      rw [repeatedPrimePowerPart_eq_piSqRad_mul_sqTail hn]

/-- The radical of the repeated part is precisely `piSqRad`. -/
theorem rad_repeatedPrimePowerPart
    (n : ℕ) :
    rad (repeatedPrimePowerPart n) =
      piSqRad n := by
  unfold rad piSqRad
  rw [repeatedPrimePowerPart_factorization_support]

/-- The repeated support shell divides the square-free tail quotient. -/
theorem piSqRad_dvd_sqTail
    {n : ℕ}
    (hn : n ≠ 0) :
    piSqRad n ∣ sqTail n := by
  exact ⟨twoTail n, sqTail_eq_piSqRad_mul_twoTail n hn⟩

/-! ## GN specialization -/

/-- The full repeated prime-power part of the non-exceptional GN factor. -/
noncomputable def GNNonExceptionalRepeatedPart
    (p a b : ℕ) : ℕ :=
  repeatedPrimePowerPart (GNNonExceptionalPart p a b)

/-- Legacy square-tail coordinates for the non-exceptional repeated part. -/
theorem GNNonExceptionalRepeatedPart_eq_piSqRad_mul_sqTail
    (p a b : ℕ) :
    GNNonExceptionalRepeatedPart p a b =
      piSqRad (GNNonExceptionalPart p a b) *
        sqTail (GNNonExceptionalPart p a b) := by
  exact repeatedPrimePowerPart_eq_piSqRad_mul_sqTail
    (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b))

/-- Equivalent depth-three-tail coordinates for the GN repeated part. -/
theorem GNNonExceptionalRepeatedPart_eq_piSqRad_sq_mul_twoTail
    (p a b : ℕ) :
    GNNonExceptionalRepeatedPart p a b =
      piSqRad (GNNonExceptionalPart p a b) ^ 2 *
        twoTail (GNNonExceptionalPart p a b) := by
  exact repeatedPrimePowerPart_eq_piSqRad_sq_mul_twoTail
    (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b))

/-- The repeated part divides the complete non-exceptional GN factor. -/
theorem GNNonExceptionalRepeatedPart_dvd_part
    (p a b : ℕ) :
    GNNonExceptionalRepeatedPart p a b ∣
      GNNonExceptionalPart p a b := by
  exact repeatedPrimePowerPart_dvd
    (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b))

/-- The complete non-exceptional factor divides `GN`. -/
theorem GNNonExceptionalPart_dvd_GN
    {p a b : ℕ}
    (hGN : GN p a b ≠ 0) :
    GNNonExceptionalPart p a b ∣ GN p a b := by
  have hpart :
      GNNonExceptionalPart p a b ≠ 0 :=
    Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  rw [← Nat.factorization_le_iff_dvd hpart hGN]
  rw [Finsupp.le_def]
  intro q
  rw [GNNonExceptionalPart_factorization]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Hence the repeated non-exceptional part is an actual divisor of `GN`. -/
theorem GNNonExceptionalRepeatedPart_dvd_GN
    {p a b : ℕ}
    (hGN : GN p a b ≠ 0) :
    GNNonExceptionalRepeatedPart p a b ∣ GN p a b :=
  (GNNonExceptionalRepeatedPart_dvd_part p a b).trans
    (GNNonExceptionalPart_dvd_GN hGN)

/-- At a coprime point of the interval, every target non-exceptional GN prime
belongs to the canonical interval family. -/
theorem GNNonExceptionalSupport_subset_intervalPrimeFamily
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNNonExceptionalSupport p a b ⊆
      GNNonExceptionalIntervalPrimeFamily p b X := by
  intro q hq
  have hqprime :
      Nat.Prime q :=
    (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  have hqnotb : ¬ q ∣ b :=
    DkMath.NumberTheory.prime_dvd_right_not_dvd_GN_of_coprime
      hp.one_le hcop hqprime
      |> fun hnot hqb =>
        hnot hqb
          (mem_support_factorization_iff.mp
            (Finset.mem_filter.mp hq).1).2.2
  exact mem_GNNonExceptionalIntervalPrimeFamily_iff.mpr
    ⟨a, haX, hq, hqnotb⟩

/-- For the target interval point, positive excess primes are exactly the
prime factors occurring at least twice in its non-exceptional GN part. -/
theorem GNExcessActivePrimeSet_target_eq_repeatedSupport
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNExcessActivePrimeSet
        (GNNonExceptionalIntervalPrimeFamily p b X)
        (GNExcessDepthProfileAt
          (GNNonExceptionalIntervalPrimeFamily p b X) p b a) =
      (GNNonExceptionalPart p a b).factorization.support.filter
        (fun q =>
          2 ≤ (GNNonExceptionalPart p a b).factorization q) := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let S := GNNonExceptionalSupport p a b
  have hSsub : S ⊆ Q :=
    GNNonExceptionalSupport_subset_intervalPrimeFamily
      hp haX hcop
  ext q
  constructor
  · intro hqactive
    have hqQ : q ∈ Q :=
      (Finset.mem_filter.mp hqactive).1
    have hqprime :
        Nat.Prime q :=
      GNNonExceptionalIntervalPrimeFamily_prime hqQ
    have hvalue :
        GNExcessProfileValue Q
            (GNExcessDepthProfileAt Q p b a) q =
          padicValNat q (GN p a b) - 1 := by
      simp [GNExcessProfileValue, GNExcessDepthProfileAt, hqQ]
    have hv :
        2 ≤ padicValNat q (GN p a b) := by
      have :=
        (Finset.mem_filter.mp hqactive).2
      rw [hvalue] at this
      omega
    have hfacGN :
        (GN p a b).factorization q =
          padicValNat q (GN p a b) :=
      Nat.factorization_def (GN p a b) hqprime
    have hqGN :
        q ∈ (GN p a b).factorization.support := by
      rw [Finsupp.mem_support_iff, hfacGN]
      omega
    have hqS : q ∈ S :=
      Finset.mem_filter.mpr
        ⟨hqGN,
          GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent
            hqQ⟩
    have hqpart :
        q ∈ (GNNonExceptionalPart p a b).factorization.support := by
      rw [GNNonExceptionalPart_factorization_support]
      exact hqS
    refine Finset.mem_filter.mpr ⟨hqpart, ?_⟩
    rw [GNNonExceptionalPart_factorization, if_pos hqS,
      hfacGN]
    exact hv
  · intro hqrepeated
    have hqpart :=
      (Finset.mem_filter.mp hqrepeated).1
    have hvpart :=
      (Finset.mem_filter.mp hqrepeated).2
    have hqS : q ∈ S := by
      change q ∈ GNNonExceptionalSupport p a b
      rw [← GNNonExceptionalPart_factorization_support]
      exact hqpart
    have hqQ : q ∈ Q := hSsub hqS
    have hqprime :
        Nat.Prime q :=
      GNNonExceptionalIntervalPrimeFamily_prime hqQ
    have hfacGN :
        (GN p a b).factorization q =
          padicValNat q (GN p a b) :=
      Nat.factorization_def (GN p a b) hqprime
    have hv :
        2 ≤ padicValNat q (GN p a b) := by
      rw [GNNonExceptionalPart_factorization, if_pos hqS,
        hfacGN] at hvpart
      exact hvpart
    apply Finset.mem_filter.mpr
    refine ⟨hqQ, ?_⟩
    have hvalue :
        GNExcessProfileValue Q
            (GNExcessDepthProfileAt Q p b a) q =
          padicValNat q (GN p a b) - 1 := by
      simp [GNExcessProfileValue, GNExcessDepthProfileAt, hqQ]
    rw [hvalue]
    omega

/-- The canonical target active modulus is exactly the full repeated
prime-power part of the non-exceptional GN factor. -/
theorem GNExcessJointDepthModulus_target_eq_repeatedPart
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily p b X)
        (GNExcessDepthProfileAt
          (GNNonExceptionalIntervalPrimeFamily p b X) p b a) =
      GNNonExceptionalRepeatedPart p a b := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let S := GNNonExceptionalSupport p a b
  rw [GNExcessJointDepthModulus_eq_prod]
  unfold GNNonExceptionalRepeatedPart repeatedPrimePowerPart
  rw [GNExcessActivePrimeSet_target_eq_repeatedSupport
    hp haX hcop]
  apply Finset.prod_congr rfl
  intro q hq
  have hqpart :=
    (Finset.mem_filter.mp hq).1
  have hvpart :=
    (Finset.mem_filter.mp hq).2
  have hqS : q ∈ S := by
    change q ∈ GNNonExceptionalSupport p a b
    rw [← GNNonExceptionalPart_factorization_support]
    exact hqpart
  have hqQ : q ∈ Q :=
    GNNonExceptionalSupport_subset_intervalPrimeFamily
      hp haX hcop hqS
  have hqprime :
      Nat.Prime q :=
    GNNonExceptionalIntervalPrimeFamily_prime hqQ
  have hfacGN :
      (GN p a b).factorization q =
        padicValNat q (GN p a b) :=
    Nat.factorization_def (GN p a b) hqprime
  have hfacpart :
      (GNNonExceptionalPart p a b).factorization q =
        padicValNat q (GN p a b) := by
    rw [GNNonExceptionalPart_factorization, if_pos hqS,
      hfacGN]
  have hvalue :
      GNExcessProfileValue Q
          (GNExcessDepthProfileAt Q p b a) q =
        padicValNat q (GN p a b) - 1 := by
    simp [GNExcessProfileValue, GNExcessDepthProfileAt, hqQ]
  rw [hvalue]
  congr 1
  rw [hfacpart] at hvpart ⊢
  omega

/-! ## Large-boundary arithmetic packet -/

/-- Every prime divisor of a repeated part occurs there at least squared. -/
theorem prime_sq_dvd_repeatedPrimePowerPart
    {n q : ℕ}
    (hq : Nat.Prime q)
    (hqdvd : q ∣ repeatedPrimePowerPart n) :
    q ^ 2 ∣ repeatedPrimePowerPart n := by
  have hrep :
      repeatedPrimePowerPart n ≠ 0 :=
    Nat.ne_of_gt (repeatedPrimePowerPart_pos n)
  apply (hq.pow_dvd_iff_le_factorization hrep).mpr
  have hqmem :
      q ∈ (repeatedPrimePowerPart n).factorization.support :=
    mem_support_factorization_iff.mpr
      ⟨hrep, hq, hqdvd⟩
  rw [repeatedPrimePowerPart_factorization_support] at hqmem
  have hcond :=
    Finset.mem_filter.mp hqmem
  rw [repeatedPrimePowerPart_factorization,
    if_pos ⟨hcond.1, hcond.2⟩]
  exact hcond.2

/-- A prime divisor of the GN repeated part belongs to the non-exceptional
support of the original GN value. -/
theorem prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart
    {p a b q : ℕ}
    (hq : Nat.Prime q)
    (hqdvd : q ∣ GNNonExceptionalRepeatedPart p a b) :
    q ∈ GNNonExceptionalSupport p a b := by
  have hrep :
      GNNonExceptionalRepeatedPart p a b ≠ 0 :=
    Nat.ne_of_gt
      (repeatedPrimePowerPart_pos
        (GNNonExceptionalPart p a b))
  have hqmem :
      q ∈ (GNNonExceptionalRepeatedPart p a b).factorization.support :=
    mem_support_factorization_iff.mpr
      ⟨hrep, hq, hqdvd⟩
  unfold GNNonExceptionalRepeatedPart at hqmem
  rw [repeatedPrimePowerPart_factorization_support] at hqmem
  have hqpart :=
    (Finset.mem_filter.mp hqmem).1
  rw [GNNonExceptionalPart_factorization_support] at hqpart
  exact hqpart

/--
The exact arithmetic certificate carried by a large target excess profile.

The packet records no counting estimate.  It says that the large CRT modulus
is a squareful divisor of the non-exceptional GN part, and that every support
prime is a non-exceptional order prime.
-/
structure GNExcessLargeBoundaryPacket
    (p a b X : ℕ) where
  modulus : ℕ
  modulus_eq_repeated :
    modulus = GNNonExceptionalRepeatedPart p a b
  modulus_eq_piSqRad_mul_sqTail :
    modulus =
      piSqRad (GNNonExceptionalPart p a b) *
        sqTail (GNNonExceptionalPart p a b)
  modulus_eq_piSqRad_sq_mul_twoTail :
    modulus =
      piSqRad (GNNonExceptionalPart p a b) ^ 2 *
        twoTail (GNNonExceptionalPart p a b)
  interval_lt_modulus : X + 1 < modulus
  modulus_dvd_nonExceptionalPart :
    modulus ∣ GNNonExceptionalPart p a b
  modulus_dvd_GN : modulus ∣ GN p a b
  prime_sq_dvd :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ modulus → q ^ 2 ∣ modulus
  prime_mem_nonExceptionalSupport :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ modulus →
      q ∈ GNNonExceptionalSupport p a b
  support_prime_mod_exponent_eq_one :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ modulus → q % p = 1

/-- A large target profile produces the exact large-boundary packet. -/
noncomputable def GNExcessLargeBoundaryPacket.of_target
    {p a b X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (ha : 0 < a)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b)
    (hlarge :
      X + 1 <
        GNExcessJointDepthModulus
          (GNNonExceptionalIntervalPrimeFamily p b X)
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily p b X) p b a)) :
    GNExcessLargeBoundaryPacket p a b X := by
  let M :=
    GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily p b X)
      (GNExcessDepthProfileAt
        (GNNonExceptionalIntervalPrimeFamily p b X) p b a)
  have hM :
      M = GNNonExceptionalRepeatedPart p a b :=
    GNExcessJointDepthModulus_target_eq_repeatedPart
      hp haX hcop
  have hGN : GN p a b ≠ 0 :=
    GN_ne_zero_of_prime_of_right_ne_zero hp (Nat.ne_of_gt hb)
  let T : Triple :=
    Triple.mk a b (a + b) rfl hcop
  refine
    { modulus := M
      modulus_eq_repeated := hM
      modulus_eq_piSqRad_mul_sqTail := ?_
      modulus_eq_piSqRad_sq_mul_twoTail := ?_
      interval_lt_modulus := hlarge
      modulus_dvd_nonExceptionalPart := ?_
      modulus_dvd_GN := ?_
      prime_sq_dvd := ?_
      prime_mem_nonExceptionalSupport := ?_
      support_prime_mod_exponent_eq_one := ?_ }
  · rw [hM]
    exact GNNonExceptionalRepeatedPart_eq_piSqRad_mul_sqTail p a b
  · rw [hM]
    exact GNNonExceptionalRepeatedPart_eq_piSqRad_sq_mul_twoTail p a b
  · rw [hM]
    exact GNNonExceptionalRepeatedPart_dvd_part p a b
  · rw [hM]
    exact GNNonExceptionalRepeatedPart_dvd_GN hGN
  · intro q hq hqdvd
    rw [hM] at hqdvd ⊢
    exact prime_sq_dvd_repeatedPrimePowerPart hq hqdvd
  · intro q hq hqdvd
    rw [hM] at hqdvd
    exact
      prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart
        hq hqdvd
  · intro q hq hqdvd
    have hqS :
        q ∈ GNNonExceptionalSupport p a b := by
      rw [hM] at hqdvd
      exact
        prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart
          hq hqdvd
    exact
      T.mod_eq_one_of_mem_GNNonExceptionalSupport hp ha hqS

/-! ## Legacy logarithmic pincer -/

/-- A large repeated modulus forces either a large repeated-support shell or
a large depth-three tail. -/
theorem GNExcessLargeBoundaryPacket.log_piSqRad_or_log_twoTail
    {p a b X : ℕ}
    (P : GNExcessLargeBoundaryPacket p a b X) :
    (1 / 4 : ℝ) * Real.log (X + 1 : ℝ) <
        Real.log
          (piSqRad (GNNonExceptionalPart p a b) : ℝ) ∨
      (1 / 2 : ℝ) * Real.log (X + 1 : ℝ) <
        Real.log
          (twoTail (GNNonExceptionalPart p a b) : ℝ) := by
  let N := GNNonExceptionalPart p a b
  let A := piSqRad N
  let B := twoTail N
  have hA : 0 < (A : ℝ) := by
    exact_mod_cast
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
  have hB : 0 < (B : ℝ) := by
    exact_mod_cast (by
      unfold B twoTail
      exact Finset.prod_pos fun q hq =>
        pow_pos
          (mem_support_factorization_iff.mp hq).2.1.pos _)
  have hloglarge :
      Real.log (X + 1 : ℝ) < Real.log (P.modulus : ℝ) := by
    apply Real.log_lt_log
    · positivity
    · exact_mod_cast P.interval_lt_modulus
  have hlogdecomp :
      Real.log (P.modulus : ℝ) =
        2 * Real.log (A : ℝ) + Real.log (B : ℝ) := by
    have hdecomp := P.modulus_eq_piSqRad_sq_mul_twoTail
    change P.modulus = A ^ 2 * B at hdecomp
    rw [hdecomp]
    push_cast
    rw [Real.log_mul (pow_pos hA 2).ne' hB.ne',
      Real.log_pow]
    norm_num
  by_cases hleft :
      (1 / 4 : ℝ) * Real.log (X + 1 : ℝ) <
        Real.log (A : ℝ)
  · exact Or.inl hleft
  · right
    have hAle :
        Real.log (A : ℝ) ≤
          (1 / 4 : ℝ) * Real.log (X + 1 : ℝ) :=
      le_of_not_gt hleft
    by_contra hright
    have hBle :
        Real.log (B : ℝ) ≤
          (1 / 2 : ℝ) * Real.log (X + 1 : ℝ) :=
      le_of_not_gt hright
    rw [hlogdecomp] at hloglarge
    linarith

/-! ## Address-charge diagnosis -/

/-- The combinatorial root-address charge of one active excess profile. -/
def GNExcessRootAddressCharge
    (Q : Finset ℕ) (p : ℕ)
    (excess : ∀ q ∈ Q, ℕ) : ℕ :=
  (p - 1) ^ (GNExcessActivePrimeSet Q excess).card

/-- Exact target profile mass in the canonical interval family, expressed in
the legacy square-tail coordinate. -/
theorem GNExcessActiveProfileMass_target_eq_log_sqTail
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNExcessActiveProfileMass
        (GNNonExceptionalIntervalPrimeFamily p b X)
        (GNExcessDepthProfileAt
          (GNNonExceptionalIntervalPrimeFamily p b X) p b a) =
      Real.log
        (sqTail (GNNonExceptionalPart p a b) : ℝ) := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let S := GNNonExceptionalSupport p a b
  let F := fun q : ℕ =>
    ((padicValNat q (GN p a b) - 1 : ℕ) : ℝ) *
      Real.log (q : ℝ)
  have hGN : GN p a b ≠ 0 :=
    GN_ne_zero_of_prime_of_right_ne_zero hp (Nat.ne_of_gt hb)
  have hSsub : S ⊆ Q :=
    GNNonExceptionalSupport_subset_intervalPrimeFamily
      hp haX hcop
  have houtside :
      ∀ q ∈ Q, q ∉ S → F q = 0 := by
    intro q hqQ hqS
    have hqprime :=
      GNNonExceptionalIntervalPrimeFamily_prime hqQ
    have hqnotGN : ¬ q ∣ GN p a b := by
      intro hqdvd
      have hmem :
          q ∈ (GN p a b).factorization.support :=
        mem_support_factorization_iff.mpr
          ⟨hGN, hqprime, hqdvd⟩
      exact hqS (Finset.mem_filter.mpr
        ⟨hmem,
          GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent
            hqQ⟩)
    have hvzero :
        padicValNat q (GN p a b) = 0 :=
      padicValNat.eq_zero_of_not_dvd hqnotGN
    unfold F
    rw [hvzero]
    norm_num
  calc
    GNExcessActiveProfileMass Q
        (GNExcessDepthProfileAt Q p b a) =
        GNExcessMassAt Q p b a := by
      symm
      exact GNExcessMassAt_eq_activeProfileMass rfl
    _ = ∑ q ∈ Q, F q := by rfl
    _ = ∑ q ∈ S, F q := by
      symm
      exact Finset.sum_subset hSsub houtside
    _ = GNNonExceptionalValuationExcess p a b := by
      unfold GNNonExceptionalValuationExcess
      apply Finset.sum_congr rfl
      intro q hq
      have hqprime :
          Nat.Prime q :=
        (mem_support_factorization_iff.mp
          (Finset.mem_filter.mp hq).1).2.1
      unfold F
      rw [Nat.factorization_def (GN p a b) hqprime]
    _ = Real.log
        (sqTail (GNNonExceptionalPart p a b) : ℝ) :=
      GNNonExceptionalValuationExcess_eq_log_sqTail p a b

/-- Exact-order support bounds the target root-address charge by the repeated
support shell. -/
theorem GNExcessRootAddressCharge_target_le_piSqRad
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < a)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    GNExcessRootAddressCharge
        (GNNonExceptionalIntervalPrimeFamily p b X) p
        (GNExcessDepthProfileAt
          (GNNonExceptionalIntervalPrimeFamily p b X) p b a) ≤
      piSqRad (GNNonExceptionalPart p a b) := by
  classical
  let Q := GNNonExceptionalIntervalPrimeFamily p b X
  let E := GNExcessDepthProfileAt Q p b a
  let A := GNExcessActivePrimeSet Q E
  have hA :
      A =
        (GNNonExceptionalPart p a b).factorization.support.filter
          (fun q =>
            2 ≤ (GNNonExceptionalPart p a b).factorization q) :=
    GNExcessActivePrimeSet_target_eq_repeatedSupport
      hp haX hcop
  let T : Triple :=
    Triple.mk a b (a + b) rfl hcop
  unfold GNExcessRootAddressCharge
  change (p - 1) ^ A.card ≤
    piSqRad (GNNonExceptionalPart p a b)
  unfold piSqRad
  rw [← hA]
  calc
    (p - 1) ^ A.card = ∏ _q ∈ A, (p - 1) := by simp
    _ ≤ ∏ q ∈ A, q := by
      apply Finset.prod_le_prod (fun _q _hq => Nat.zero_le _)
      intro q hqA
      have hqrep : q ∣ GNNonExceptionalRepeatedPart p a b := by
        have hqmem :
            q ∈ (GNNonExceptionalPart p a b).factorization.support.filter
              (fun r =>
                2 ≤ (GNNonExceptionalPart p a b).factorization r) := by
          rw [← hA]
          exact hqA
        unfold GNNonExceptionalRepeatedPart repeatedPrimePowerPart
        have hpow :=
          Finset.dvd_prod_of_mem
          (fun r =>
            r ^ (GNNonExceptionalPart p a b).factorization r)
          hqmem
        exact
          (dvd_pow_self q (by
            have := (Finset.mem_filter.mp hqmem).2
            omega)).trans hpow
      have hqQ : q ∈ Q := by
        change q ∈ GNExcessActivePrimeSet Q E at hqA
        exact (Finset.mem_filter.mp hqA).1
      have hqprime :
          Nat.Prime q :=
        GNNonExceptionalIntervalPrimeFamily_prime hqQ
      have hqS :
          q ∈ GNNonExceptionalSupport p a b :=
        prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart
          hqprime hqrep
      have hpdiv :
          p ∣ q - 1 :=
        T.prime_dvd_sub_one_of_mem_GNNonExceptionalSupport
          hp ha hqS
      have hp_le :
          p ≤ q - 1 :=
        Nat.le_of_dvd
          (Nat.sub_pos_of_lt
            ((mem_support_factorization_iff.mp
              (Finset.mem_filter.mp hqS).1).2.1.one_lt))
          hpdiv
      omega

/-- At `t = 1/2`, target address charge times exponential excess is bounded
by the three-quarter power of the exact repeated modulus. -/
theorem GNExcess_target_boundaryWeight_le_repeatedPart_rpow
    {p b a X : ℕ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (ha : 0 < a)
    (haX : a ∈ Finset.Icc 0 X)
    (hcop : Nat.Coprime a b) :
    (GNExcessRootAddressCharge
          (GNNonExceptionalIntervalPrimeFamily p b X) p
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily p b X) p b a) : ℝ) *
        Real.exp
          ((1 / 2 : ℝ) *
            GNExcessActiveProfileMass
              (GNNonExceptionalIntervalPrimeFamily p b X)
              (GNExcessDepthProfileAt
                (GNNonExceptionalIntervalPrimeFamily p b X) p b a)) ≤
      (GNNonExceptionalRepeatedPart p a b : ℝ) ^
        (3 / 4 : ℝ) := by
  let N := GNNonExceptionalPart p a b
  let A := piSqRad N
  let C := sqTail N
  let R :=
    GNExcessRootAddressCharge
      (GNNonExceptionalIntervalPrimeFamily p b X) p
      (GNExcessDepthProfileAt
        (GNNonExceptionalIntervalPrimeFamily p b X) p b a)
  have hRleA : R ≤ A :=
    GNExcessRootAddressCharge_target_le_piSqRad
      hp ha haX hcop
  have hRpos : 0 < (R : ℝ) := by
    exact_mod_cast (by
      unfold R GNExcessRootAddressCharge
      exact pow_pos (Nat.sub_pos_of_lt hp.one_lt) _)
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
  have hCpos : 0 < (C : ℝ) := by
    change 0 < (sqTail N : ℝ)
    rw [sqTail_eq_piSqRad_mul_twoTail N
      (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b))]
    exact_mod_cast Nat.mul_pos
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
      (by
        unfold twoTail
        exact Finset.prod_pos fun q hq =>
          pow_pos
            (mem_support_factorization_iff.mp hq).2.1.pos _)
  have hAleC : (A : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast Nat.le_of_dvd
      (by exact_mod_cast hCpos)
      (piSqRad_dvd_sqTail
        (Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)))
  have hlogRleA :
      Real.log (R : ℝ) ≤ Real.log (A : ℝ) :=
    Real.log_le_log hRpos (by exact_mod_cast hRleA)
  have hlogAleC :
      Real.log (A : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log hApos hAleC
  have hmass :
      GNExcessActiveProfileMass
          (GNNonExceptionalIntervalPrimeFamily p b X)
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily p b X) p b a) =
        Real.log (C : ℝ) :=
    GNExcessActiveProfileMass_target_eq_log_sqTail
      hp hb haX hcop
  have hrep :
      (GNNonExceptionalRepeatedPart p a b : ℝ) =
        (A : ℝ) * (C : ℝ) := by
    exact_mod_cast
      GNNonExceptionalRepeatedPart_eq_piSqRad_mul_sqTail p a b
  have hreppos :
      0 < (GNNonExceptionalRepeatedPart p a b : ℝ) := by
    rw [hrep]
    positivity
  rw [hmass]
  calc
    (R : ℝ) *
        Real.exp ((1 / 2 : ℝ) * Real.log (C : ℝ)) =
        Real.exp
          (Real.log (R : ℝ) +
            (1 / 2 : ℝ) * Real.log (C : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hRpos]
    _ ≤ Real.exp
          ((3 / 4 : ℝ) *
            Real.log
              (GNNonExceptionalRepeatedPart p a b : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hrep, Real.log_mul hApos.ne' hCpos.ne']
      linarith
    _ = (GNNonExceptionalRepeatedPart p a b : ℝ) ^
          (3 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hreppos]
      congr 1
      ring

end DkMath.ABC
