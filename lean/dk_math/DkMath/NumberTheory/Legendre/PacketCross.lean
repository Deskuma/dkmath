/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.Legendre.Quotient

#print "file: DkMath.NumberTheory.Legendre.PacketCross"

/-!
## PacketCross

PRIM-L019 ordered packet cross-pair coupling and product-period sparsity.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-!
### PRIM-L019: packet cross-pair coupling

PRIM-L018 measured pair interactions within one seat.  This checkpoint adds
the complementary packet coordinate: an ordered pair `(p,q)` assigns `p` to
the left seat `r` and `q` to the right seat `n + r`.  The packet
representatives are the canonical `r` in the first half of the coprime
window.  The two support sets are disjoint, so every actual cross incidence
automatically has distinct primes.  Full cover therefore gives one cross
incidence per packet, while a fixed ordered pair is periodic with modulus
`p*q`.  These are finite coupling constraints only; no matching argument,
analytic estimate, contradiction, or proof of Legendre's conjecture is made.
-/

/-! ### PRIM-L019.1: ordered packet cross incidences -/

/-- Ordered left/right pairs of distinct anchor-nondivisor prime directions. -/
noncomputable def squareAnchorNondivisorOrderedPrimePairs (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorNondivisorPrimes n)).filter
      (fun pair => pair.1 ≠ pair.2)

@[simp] theorem mem_squareAnchorNondivisorOrderedPrimePairs
    {n p q : ℕ} :
    (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
        Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ p ≠ q := by
  simp [squareAnchorNondivisorOrderedPrimePairs, and_assoc,
    and_left_comm, and_comm]

/-- Canonical packet representatives crossed by an ordered prime pair. -/
noncomputable def squareAnchorPacketCrossOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeBaseOffsets n).filter
    (fun r =>
      SquareOffsetForbiddenBy n p r ∧
        SquareOffsetForbiddenBy n q (n + r))

@[simp] theorem mem_squareAnchorPacketCrossOffsets
    {n p q r : ℕ} :
    r ∈ squareAnchorPacketCrossOffsets n p q ↔
      r ∈ squareAnchorCoprimeBaseOffsets n ∧
        SquareOffsetForbiddenBy n p r ∧
          SquareOffsetForbiddenBy n q (n + r) := by
  simp [squareAnchorPacketCrossOffsets, and_assoc]

/-- One nondivisor prime cannot support both seats of a packet. -/
theorem not_mem_packetCross_same_prime
    {n p r : ℕ}
    (hp : p ∈ squareAnchorNondivisorPrimes n) :
    ¬ (SquareOffsetForbiddenBy n p r ∧
       SquareOffsetForbiddenBy n p (n + r)) := by
  exact not_both_squareOffsetForbiddenBy_of_not_dvd_anchor
    (mem_squareAnchorNondivisorPrimes.mp hp).2.2

/-- Ordered packet cross-incidence count. -/
noncomputable def squareAnchorPacketCrossPairCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorNondivisorOrderedPrimePairs n,
    (squareAnchorPacketCrossOffsets n pair.1 pair.2).card

/-- Exact packet transpose: each packet contributes the product of its support sizes. -/
theorem squareAnchorPacketCrossPairCount_eq_sum_support_card_mul
    (n : ℕ) :
    squareAnchorPacketCrossPairCount n =
      ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
        (squareOffsetAnchorNondivisorSupport n r).card *
        (squareOffsetAnchorNondivisorSupport n (n + r)).card := by
  classical
  have hpairset (r : ℕ) :
      (squareAnchorNondivisorOrderedPrimePairs n).filter
          (fun pair =>
            pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
              pair.2 ∈ squareOffsetAnchorNondivisorSupport n (n + r)) =
        (squareOffsetAnchorNondivisorSupport n r).product
          (squareOffsetAnchorNondivisorSupport n (n + r)) := by
    ext pair
    rcases pair with ⟨p, q⟩
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      have h'' := Finset.mem_filter.mp h'.1
      have hs := Finset.mem_product.mp h''.1
      exact Finset.mem_product.mpr ⟨h'.2.1, h'.2.2⟩
    · intro h
      have hs := Finset.mem_product.mp h
      have hp := mem_squareOffsetAnchorNondivisorSupport.mp hs.1
      have hq := mem_squareOffsetAnchorNondivisorSupport.mp hs.2
      have hne : p ≠ q := by
        intro heq
        subst q
        exact (Finset.disjoint_left.mp
          (disjoint_anchorNondivisorSupport_shift n r)) hs.1 hs.2
      apply Finset.mem_filter.mpr
      refine ⟨?_, ⟨hs.1, hs.2⟩⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨mem_squareAnchorNondivisorPrimes.mpr
          ⟨hp.1, hp.2.1, hp.2.2.1⟩,
          mem_squareAnchorNondivisorPrimes.mpr
            ⟨hq.1, hq.2.1, hq.2.2.1⟩⟩, hne⟩
  unfold squareAnchorPacketCrossPairCount
  calc
    (∑ pair ∈ squareAnchorNondivisorOrderedPrimePairs n,
        (squareAnchorPacketCrossOffsets n pair.1 pair.2).card) =
        ∑ pair ∈ squareAnchorNondivisorOrderedPrimePairs n,
          ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 (n + r) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      simp [squareAnchorPacketCrossOffsets]
    _ = ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          ∑ pair ∈ squareAnchorNondivisorOrderedPrimePairs n,
            if SquareOffsetForbiddenBy n pair.1 r ∧
                SquareOffsetForbiddenBy n pair.2 (n + r) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          ((squareAnchorNondivisorOrderedPrimePairs n).filter
            (fun pair =>
              pair.1 ∈ squareOffsetAnchorNondivisorSupport n r ∧
                pair.2 ∈ squareOffsetAnchorNondivisorSupport n (n + r))).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext pair
      rcases pair with ⟨p, q⟩
      simp [mem_squareOffsetAnchorNondivisorSupport,
        SquareOffsetForbiddenBy]
      aesop
    _ = ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          ((squareOffsetAnchorNondivisorSupport n r).product
            (squareOffsetAnchorNondivisorSupport n (n + r))).card := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hpairset]
    _ = ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card *
            (squareOffsetAnchorNondivisorSupport n (n + r)).card := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [Finset.card_product]

/-! ### PRIM-L019.2: full-cover frontier and quotient coordinates -/

/-- Full cover supplies at least one ordered cross incidence per packet. -/
theorem totient_le_packetCrossPairCount_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    Nat.totient n ≤ squareAnchorPacketCrossPairCount n := by
  have hcard := card_squareAnchorCoprimeBaseOffsets hn
  rw [← hcard]
  rw [squareAnchorPacketCrossPairCount_eq_sum_support_card_mul]
  calc
    (squareAnchorCoprimeBaseOffsets n).card =
        ∑ r ∈ squareAnchorCoprimeBaseOffsets n, 1 := by simp
    _ ≤ ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
          (squareOffsetAnchorNondivisorSupport n r).card *
            (squareOffsetAnchorNondivisorSupport n (n + r)).card := by
      apply Finset.sum_le_sum
      intro r hr
      rcases exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
        hn hr hfull with ⟨p, q, hpq, hp, hq⟩
      have hpcard : 1 ≤ (squareOffsetAnchorNondivisorSupport n r).card :=
        Finset.card_pos.mpr ⟨p, hp⟩
      have hqcard : 1 ≤
          (squareOffsetAnchorNondivisorSupport n (n + r)).card :=
        Finset.card_pos.mpr ⟨q, hq⟩
      have hmul := Nat.mul_le_mul hpcard hqcard
      simpa using hmul

/-- Quotient coordinates carried by one ordered packet cross hit. -/
theorem squareAnchorPacketCrossOffsets_factorization
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    ∃ a b,
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b := by
  have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
  have hbase := mem_squareAnchorCoprimeBaseOffsets.mp hr'.1
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hpmem : p ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.1, hpair.2.1, hpair.2.2.1, hr'.2.1⟩
  have hqmem : q ∈ squareOffsetAnchorNondivisorSupport n (n + r) :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.2.2.2.1, hpair.2.2.2.2.1,
        hpair.2.2.2.2.2.1, hr'.2.2⟩
  let a := squareOffsetSupportQuotient n p r
  let b := squareOffsetSupportQuotient n q (n + r)
  have hpa : p * a = n ^ 2 + r := by
    dsimp [a]
    exact mul_squareOffsetSupportQuotient_eq
      (mem_squareOffsetAnchorNondivisorSupport.mp hpmem).2.2.2
  have hqb : q * b = n ^ 2 + (n + r) := by
    dsimp [b]
    exact mul_squareOffsetSupportQuotient_eq
      (mem_squareOffsetAnchorNondivisorSupport.mp hqmem).2.2.2
  have hna : n < a := by
    dsimp [a]
    exact anchor_lt_squareOffsetSupportQuotient
      (mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets hr'.1)).1
      hpair.2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hpmem).2.2.2
  have hnb : n < b := by
    dsimp [b]
    exact anchor_lt_squareOffsetSupportQuotient
      (mem_squareAnchorCoprimeOffsets.mp
        (mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets hr'.1)).1
      hpair.2.2.2.2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hqmem).2.2.2
  have hca : Nat.Coprime n a := by
    dsimp [a]
    exact (coprime_anchor_squareOffsetSupportQuotient_iff
      hpair.1 hpair.2.2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hpmem).2.2.2).mpr hbase.2.2
  have hcb : Nat.Coprime n b := by
    dsimp [b]
    exact (coprime_anchor_squareOffsetSupportQuotient_iff
      hpair.2.2.2.1 hpair.2.2.2.2.2.1
      (mem_squareOffsetAnchorNondivisorSupport.mp hqmem).2.2.2).mpr
      (coprime_anchor_add_iff.mpr hbase.2.2)
  refine ⟨a, b, hpa, hqb, ?_, hna, hnb, hca, hcb⟩
  omega

/-! ### PRIM-L019.3: product-period sparsity -/

/-- A fixed ordered cross pair has both prime divisors on the packet gap. -/
theorem squareAnchorPacketCrossOffsets_mul_dvd_diff
    {n p q r s : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q)
    (hs : s ∈ squareAnchorPacketCrossOffsets n p q)
    (hrs : r ≤ s) :
    p * q ∣ s - r := by
  have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
  have hs' := mem_squareAnchorPacketCrossOffsets.mp hs
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hpdiv : p ∣ s - r := by
    have hps := (mem_squareOffsetAnchorNondivisorSupport.mp
      (mem_squareOffsetAnchorNondivisorSupport.mpr
        ⟨hpair.1, hpair.2.1, hpair.2.2.1, hs'.2.1⟩)).2.2.2
    have hpr := (mem_squareOffsetAnchorNondivisorSupport.mp
      (mem_squareOffsetAnchorNondivisorSupport.mpr
        ⟨hpair.1, hpair.2.1, hpair.2.2.1, hr'.2.1⟩)).2.2.2
    convert Nat.dvd_sub hps hpr using 1; omega
  have hqdiv : q ∣ s - r := by
    have hqs := (mem_squareOffsetAnchorNondivisorSupport.mp
      (mem_squareOffsetAnchorNondivisorSupport.mpr
        ⟨hpair.2.2.2.1, hpair.2.2.2.2.1,
          hpair.2.2.2.2.2.1, hs'.2.2⟩)).2.2.2
    have hqr := (mem_squareOffsetAnchorNondivisorSupport.mp
      (mem_squareOffsetAnchorNondivisorSupport.mpr
        ⟨hpair.2.2.2.1, hpair.2.2.2.2.1,
          hpair.2.2.2.2.2.1, hr'.2.2⟩)).2.2.2
    have hqs' : q ∣ n ^ 2 + (n + s) := hqs
    have hqr' : q ∣ n ^ 2 + (n + r) := hqr
    convert Nat.dvd_sub hqs' hqr' using 1; omega
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes hpair.1 hpair.2.2.2.1).2
      hpair.2.2.2.2.2.2) hpdiv hqdiv

/-- If `p*q > n`, one ordered cross pair hits at most one base representative. -/
theorem card_squareAnchorPacketCrossOffsets_le_one_of_anchor_lt_product
    {n p q : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hfar : n < p * q) :
    (squareAnchorPacketCrossOffsets n p q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  by_cases hrs : r ≤ s
  · have hdiv := squareAnchorPacketCrossOffsets_mul_dvd_diff hpq hr hs hrs
    have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
    have hs' := mem_squareAnchorPacketCrossOffsets.mp hs
    have hlt : s - r < p * q := by
      have hrbase := mem_squareAnchorCoprimeBaseOffsets.mp hr'.1
      have hsbase := mem_squareAnchorCoprimeBaseOffsets.mp hs'.1
      omega
    have hzero : s - r = 0 := by
      by_contra hne
      have hpos : 0 < s - r := Nat.pos_of_ne_zero hne
      have hle := Nat.le_of_dvd hpos hdiv
      omega
    omega
  · have hsr : s ≤ r := by omega
    have hdiv := squareAnchorPacketCrossOffsets_mul_dvd_diff hpq hs hr hsr
    have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
    have hs' := mem_squareAnchorPacketCrossOffsets.mp hs
    have hlt : r - s < p * q := by
      have hrbase := mem_squareAnchorCoprimeBaseOffsets.mp hr'.1
      have hsbase := mem_squareAnchorCoprimeBaseOffsets.mp hs'.1
      omega
    have hzero : r - s = 0 := by
      by_contra hne
      have hpos : 0 < r - s := Nat.pos_of_ne_zero hne
      have hle := Nat.le_of_dvd hpos hdiv
      omega
    omega

/-! ### PRIM-L019.4: near/far packet cross pairs -/

/-- Ordered packet pairs whose product period fits in the base window. -/
noncomputable def squareAnchorPacketNearCrossPairs (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (squareAnchorNondivisorOrderedPrimePairs n).filter
    (fun pair => pair.1 * pair.2 ≤ n)

/-- Ordered packet pairs whose product period exceeds the base window. -/
noncomputable def squareAnchorPacketFarCrossPairs (n : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (squareAnchorNondivisorOrderedPrimePairs n).filter
    (fun pair => n < pair.1 * pair.2)

@[simp] theorem mem_squareAnchorPacketNearCrossPairs
    {n p q : ℕ} :
    (p, q) ∈ squareAnchorPacketNearCrossPairs n ↔
      (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n ∧ p * q ≤ n := by
  simp [squareAnchorPacketNearCrossPairs]

@[simp] theorem mem_squareAnchorPacketFarCrossPairs
    {n p q : ℕ} :
    (p, q) ∈ squareAnchorPacketFarCrossPairs n ↔
      (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n ∧ n < p * q := by
  simp [squareAnchorPacketFarCrossPairs]

theorem squareAnchorPacketNearCrossPairs_union_farCrossPairs (n : ℕ) :
    squareAnchorPacketNearCrossPairs n ∪
        squareAnchorPacketFarCrossPairs n =
      squareAnchorNondivisorOrderedPrimePairs n := by
  ext pair
  rcases pair with ⟨p, q⟩
  by_cases hnear : p * q ≤ n
  · simp [squareAnchorPacketNearCrossPairs,
      squareAnchorPacketFarCrossPairs, hnear]
  · have hfar : n < p * q := lt_of_not_ge hnear
    simp [squareAnchorPacketNearCrossPairs,
      squareAnchorPacketFarCrossPairs, hnear, hfar]

theorem disjoint_squareAnchorPacketNearCrossPairs_farCrossPairs (n : ℕ) :
    Disjoint (squareAnchorPacketNearCrossPairs n)
      (squareAnchorPacketFarCrossPairs n) := by
  rw [Finset.disjoint_left]
  intro pair hnear hfar
  have hnear' := mem_squareAnchorPacketNearCrossPairs.mp hnear
  have hfar' := mem_squareAnchorPacketFarCrossPairs.mp hfar
  omega

/-- The near contribution to the packet cross ledger. -/
noncomputable def squareAnchorPacketNearCrossPairCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorPacketNearCrossPairs n,
    (squareAnchorPacketCrossOffsets n pair.1 pair.2).card

/-- The far contribution to the packet cross ledger. -/
noncomputable def squareAnchorPacketFarCrossPairCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorPacketFarCrossPairs n,
    (squareAnchorPacketCrossOffsets n pair.1 pair.2).card

theorem squareAnchorPacketCrossPairCount_eq_near_add_far
    (n : ℕ) :
    squareAnchorPacketCrossPairCount n =
      squareAnchorPacketNearCrossPairCount n +
        squareAnchorPacketFarCrossPairCount n := by
  unfold squareAnchorPacketCrossPairCount
    squareAnchorPacketNearCrossPairCount
    squareAnchorPacketFarCrossPairCount
  rw [show squareAnchorNondivisorOrderedPrimePairs n =
      squareAnchorPacketNearCrossPairs n ∪
        squareAnchorPacketFarCrossPairs n by
        symm
        exact squareAnchorPacketNearCrossPairs_union_farCrossPairs n]
  rw [Finset.sum_union
    (disjoint_squareAnchorPacketNearCrossPairs_farCrossPairs n)]

/-- The far packet contribution is at most the number of far ordered pairs. -/
theorem squareAnchorPacketFarCrossPairCount_le_card_farCrossPairs
    (n : ℕ) :
    squareAnchorPacketFarCrossPairCount n ≤
      (squareAnchorPacketFarCrossPairs n).card := by
  unfold squareAnchorPacketFarCrossPairCount
  calc
    (∑ pair ∈ squareAnchorPacketFarCrossPairs n,
        (squareAnchorPacketCrossOffsets n pair.1 pair.2).card) ≤
        ∑ pair ∈ squareAnchorPacketFarCrossPairs n, 1 := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact card_squareAnchorPacketCrossOffsets_le_one_of_anchor_lt_product
        (mem_squareAnchorPacketFarCrossPairs.mp hpair).1
        (mem_squareAnchorPacketFarCrossPairs.mp hpair).2
    _ = (squareAnchorPacketFarCrossPairs n).card := by simp

end DkMath.NumberTheory.Legendre

