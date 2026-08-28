/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PacketCross

#print "file: DkMath.NumberTheory.Legendre.PacketCoprimality"

/-!
## PacketCoprimality

PRIM-L020 upgrades the PRIM-L019 separation of old nondivisor support
directions to separation of the complete packet integers.  For a coprime
base representative `r`, the two points `n ^ 2 + r` and
`n ^ 2 + (n + r)` are coprime.  Consequently every prime factor, including
fresh factors in the complementary quotients, is separated across the two
packet sides.

The resulting rectangle leaves the same-side relations `p ⟂ a` and `q ⟂ b`
unclassified: selected-prime depth may still occur there.  No primality of a
quotient, factorization uniqueness, contradiction, matching, estimate, or
proof of Legendre's conjecture is asserted.
-/

namespace DkMath.NumberTheory.Legendre

/-! ### PRIM-L020.1: coprimality of the two packet integers -/

/--
The two points of a coprime square packet are coprime.

The proof is the Euclidean reduction
`gcd(n ^ 2 + r, n ^ 2 + (n + r)) = gcd(r, n)`.
-/
theorem coprime_squarePacketPoints_of_coprime_offset
    {n r : ℕ}
    (hcop : Nat.Coprime n r) :
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + (n + r)) := by
  have hleft : Nat.Coprime (n ^ 2 + r) n := by
    simpa only [pow_two, add_comm] using
      (Nat.coprime_add_mul_right_left r n n).mpr hcop.symm
  rw [show n ^ 2 + (n + r) = (n ^ 2 + r) + n by omega]
  exact Nat.coprime_self_add_right.mpr hleft

/-- The generic packet coprimality theorem specialized to canonical bases. -/
theorem coprime_squarePacketPoints_of_mem_base
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + (n + r)) :=
  coprime_squarePacketPoints_of_coprime_offset
    (mem_squareAnchorCoprimeBaseOffsets.mp hr).2.2

/-- No prime can divide both complete points of a canonical packet. -/
theorem not_prime_dvd_both_squarePacketPoints
    {n r ℓ : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hℓ : Nat.Prime ℓ) :
    ¬ (ℓ ∣ n ^ 2 + r ∧ ℓ ∣ n ^ 2 + (n + r)) := by
  intro hboth
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨ℓ, hℓ, hboth.1, hboth.2⟩)
    (coprime_squarePacketPoints_of_mem_base hr)

/-! ### PRIM-L020.2: quotient and factor-rectangle separation -/

/-
The exact equations for the named quotient coordinates.  This private helper
keeps the public separation theorems in the quotient notation used by the
downstream API.
-/
private theorem packetCross_quotient_factor_equations
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r = n ^ 2 + r ∧
      q * squareOffsetSupportQuotient n q (n + r) = n ^ 2 + (n + r) := by
  have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hpmem : p ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.1, hpair.2.1, hpair.2.2.1, hr'.2.1⟩
  have hqmem : q ∈ squareOffsetAnchorNondivisorSupport n (n + r) :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.2.2.2.1, hpair.2.2.2.2.1,
        hpair.2.2.2.2.2.1, hr'.2.2⟩
  exact ⟨mul_squareOffsetSupportQuotient_eq
      (mem_squareOffsetAnchorNondivisorSupport.mp hpmem).2.2.2,
    mul_squareOffsetSupportQuotient_eq
      (mem_squareOffsetAnchorNondivisorSupport.mp hqmem).2.2.2⟩

/-- The complementary quotients of one ordered packet cross hit are coprime. -/
theorem coprime_packetCross_supportQuotients
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime
      (squareOffsetSupportQuotient n p r)
      (squareOffsetSupportQuotient n q (n + r)) := by
  have heq := packetCross_quotient_factor_equations hpq hr
  have hbase := (mem_squareAnchorPacketCrossOffsets.mp hr).1
  have hpoints := coprime_squarePacketPoints_of_mem_base hbase
  have ha : squareOffsetSupportQuotient n p r ∣ n ^ 2 + r := by
    rw [← heq.1]
    exact dvd_mul_left _ _
  have hb : squareOffsetSupportQuotient n q (n + r) ∣
      n ^ 2 + (n + r) := by
    rw [← heq.2]
    exact dvd_mul_left _ _
  exact Nat.Coprime.of_dvd ha hb hpoints

/-- A prime divisor cannot occur in both complementary quotients. -/
theorem not_prime_dvd_both_packetCross_supportQuotients
    {n p q r ℓ : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q)
    (hℓ : Nat.Prime ℓ) :
    ¬ (ℓ ∣ squareOffsetSupportQuotient n p r ∧
      ℓ ∣ squareOffsetSupportQuotient n q (n + r)) := by
  intro hboth
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨ℓ, hℓ, hboth.1, hboth.2⟩)
    (coprime_packetCross_supportQuotients hpq hr)

/--
The cross-factor rectangle for one packet hit.

The four displayed relations separate the two packet sides.  The same-side
relations `p ⟂ a` and `q ⟂ b` are intentionally absent.
-/
theorem packetCross_factor_rectangle_coprime
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime p q ∧
      Nat.Coprime p (squareOffsetSupportQuotient n q (n + r)) ∧
      Nat.Coprime (squareOffsetSupportQuotient n p r) q ∧
      Nat.Coprime
        (squareOffsetSupportQuotient n p r)
        (squareOffsetSupportQuotient n q (n + r)) := by
  have heq := packetCross_quotient_factor_equations hpq hr
  have hbase := (mem_squareAnchorPacketCrossOffsets.mp hr).1
  have hpoints := coprime_squarePacketPoints_of_mem_base hbase
  have hpA : p ∣ n ^ 2 + r := by
    rw [← heq.1]
    exact dvd_mul_right _ _
  have hqB : q ∣ n ^ 2 + (n + r) := by
    rw [← heq.2]
    exact dvd_mul_right _ _
  have haA : squareOffsetSupportQuotient n p r ∣ n ^ 2 + r := by
    rw [← heq.1]
    exact dvd_mul_left _ _
  have hbB : squareOffsetSupportQuotient n q (n + r) ∣
      n ^ 2 + (n + r) := by
    rw [← heq.2]
    exact dvd_mul_left _ _
  exact ⟨Nat.Coprime.of_dvd hpA hqB hpoints,
    Nat.Coprime.of_dvd hpA hbB hpoints,
    Nat.Coprime.of_dvd haA hqB hpoints,
    Nat.Coprime.of_dvd haA hbB hpoints⟩

/-- The two complete factor products are coprime across a packet. -/
theorem coprime_packetCross_factor_products
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime
      (p * squareOffsetSupportQuotient n p r)
      (q * squareOffsetSupportQuotient n q (n + r)) := by
  have heq := packetCross_quotient_factor_equations hpq hr
  have hbase := (mem_squareAnchorPacketCrossOffsets.mp hr).1
  have hpoints := coprime_squarePacketPoints_of_mem_base hbase
  rw [heq.1, heq.2]
  exact hpoints

/-! ### PRIM-L020.3: strengthened factorization packages -/

/-- PRIM-L019 factorization strengthened by cross-side coprimality. -/
theorem squareAnchorPacketCrossOffsets_coprime_factorization
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    ∃ a b,
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime (p * a) (q * b) ∧
      Nat.Coprime p b ∧
      Nat.Coprime a q ∧
      Nat.Coprime a b := by
  rcases squareAnchorPacketCrossOffsets_factorization hpq hr with
    ⟨a, b, hpa, hqb, hgap, hna, hnb, hca, hcb⟩
  have heq := packetCross_quotient_factor_equations hpq hr
  have haeq : a = squareOffsetSupportQuotient n p r := by
    apply Nat.mul_left_cancel (mem_squareAnchorNondivisorOrderedPrimePairs.mp
      hpq).1.pos
    calc
      p * a = n ^ 2 + r := hpa
      _ = p * squareOffsetSupportQuotient n p r := heq.1.symm
  have hbeq : b = squareOffsetSupportQuotient n q (n + r) := by
    apply Nat.mul_left_cancel (mem_squareAnchorNondivisorOrderedPrimePairs.mp
      hpq).2.2.2.1.pos
    calc
      q * b = n ^ 2 + (n + r) := hqb
      _ = q * squareOffsetSupportQuotient n q (n + r) := heq.2.symm
  have hrect := packetCross_factor_rectangle_coprime hpq hr
  have hprod := coprime_packetCross_factor_products hpq hr
  refine ⟨a, b, hpa, hqb, hgap, hna, hnb, hca, hcb, ?_, ?_, ?_, ?_⟩
  · simpa [haeq, hbeq] using hprod
  · simpa [haeq, hbeq] using hrect.2.1
  · simpa [haeq, hbeq] using hrect.2.2.1
  · simpa [haeq, hbeq] using hrect.2.2.2

/--
Full cover supplies a cross-separated factor rectangle for every canonical
base representative.

This is a necessary finite structural package under full cover.  It does not
make the quotients prime, remove same-side selected-prime depth, or yield a
contradiction.
-/
theorem exists_coprime_factor_rectangle_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q a b,
      p ≠ q ∧
      p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime (p * a) (q * b) ∧
      Nat.Coprime p b ∧
      Nat.Coprime a q ∧
      Nat.Coprime a b := by
  rcases exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
      hn hr hfull with ⟨p, q, hpq, hp, hq⟩
  have hp' := mem_squareOffsetAnchorNondivisorSupport.mp hp
  have hq' := mem_squareOffsetAnchorNondivisorSupport.mp hq
  have hpqmem : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n :=
    mem_squareAnchorNondivisorOrderedPrimePairs.mpr
      ⟨hp'.1, hp'.2.1, hp'.2.2.1,
        hq'.1, hq'.2.1, hq'.2.2.1, hpq⟩
  have hrmem : r ∈ squareAnchorPacketCrossOffsets n p q :=
    mem_squareAnchorPacketCrossOffsets.mpr
      ⟨hr, hp'.2.2.2, hq'.2.2.2⟩
  rcases squareAnchorPacketCrossOffsets_coprime_factorization hpqmem hrmem with
    ⟨a, b, hpa, hqb, hgap, hna, hnb, hca, hcb, hprod, hpb, haq, hab⟩
  exact ⟨p, q, a, b, hpq,
    mem_squareAnchorNondivisorPrimes.mpr ⟨hp'.1, hp'.2.1, hp'.2.2.1⟩,
    mem_squareAnchorNondivisorPrimes.mpr ⟨hq'.1, hq'.2.1, hq'.2.2.1⟩,
    hpa, hqb, hgap, hna, hnb, hca, hcb, hprod, hpb, haq, hab⟩

end DkMath.NumberTheory.Legendre
