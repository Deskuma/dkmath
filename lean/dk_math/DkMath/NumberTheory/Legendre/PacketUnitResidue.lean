/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.PacketCoprimality

#print "file: DkMath.NumberTheory.Legendre.PacketUnitResidue"

/-!
## PacketUnitResidue

PRIM-L021 records the reduced-residue geometry of a PRIM-L019/020 packet.
For a canonical base representative `r`, both packet points are congruent to
`r` modulo the anchor `n`, while their exact factor products differ by one
copy of `n`.  The prime directions and complementary factors are all
coprime to the anchor, so they represent invertible residue classes in the
elementary `Nat.Coprime` sense.

This is a finite residue-coordinate package, not a distribution or matching
result.  Same-side selected-prime depth remains unresolved, and no quotient
group, modular inverse construction, contradiction, or proof of Legendre's
conjecture is asserted.
-/

namespace DkMath.NumberTheory.Legendre

/-! ### PRIM-L021.1: canonical reduced residues -/

/-- A canonical base representative is strictly below the anchor when `n > 1`. -/
theorem squareAnchorCoprimeBaseOffsets_lt_anchor
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    r < n := by
  have hr' := mem_squareAnchorCoprimeBaseOffsets.mp hr
  by_contra hnot
  have hre : r = n := by omega
  have hnn : Nat.Coprime n n := by simpa [hre] using hr'.2.2
  have hn_one : n = 1 := by simpa [Nat.Coprime] using hnn
  omega

/-- The canonical base representative is its own remainder modulo the anchor. -/
@[simp] theorem mod_anchor_eq_self_of_mem_coprimeBase
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    r % n = r :=
  Nat.mod_eq_of_lt (squareAnchorCoprimeBaseOffsets_lt_anchor hn hr)

/-! ### PRIM-L021.2: packet-point and quotient residues -/

/-- The left packet point has the base representative as its residue modulo `n`. -/
theorem squarePacket_left_modEq_base
    (n r : ℕ) :
    n ^ 2 + r ≡ r [MOD n] := by
  have hpow : n ^ 2 ≡ 0 [MOD n] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_pow (dvd_refl n) (by decide))
  simp

/-- The right packet point has the same base residue modulo `n`. -/
theorem squarePacket_right_modEq_base
    (n r : ℕ) :
    n ^ 2 + (n + r) ≡ r [MOD n] := by
  have hpow : n ^ 2 ≡ 0 [MOD n] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_pow (dvd_refl n) (by decide))
  have hnr : n + r ≡ r [MOD n] :=
    (Nat.modEq_modulus_add_iff.mpr (Nat.ModEq.rfl : r ≡ r [MOD n])).symm
  simpa using hpow.add hnr

/-- The left packet point has exact remainder `r` for a canonical base. -/
theorem squarePacket_left_mod_eq_base_of_mem_coprimeBase
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    (n ^ 2 + r) % n = r := by
  have hmod := squarePacket_left_modEq_base n r
  change (n ^ 2 + r) % n = r % n at hmod
  rw [mod_anchor_eq_self_of_mem_coprimeBase hn hr] at hmod
  exact hmod

/-- The right packet point has exact remainder `r` for a canonical base. -/
theorem squarePacket_right_mod_eq_base_of_mem_coprimeBase
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    (n ^ 2 + (n + r)) % n = r := by
  have hmod := squarePacket_right_modEq_base n r
  change (n ^ 2 + (n + r)) % n = r % n at hmod
  rw [mod_anchor_eq_self_of_mem_coprimeBase hn hr] at hmod
  exact hmod

/-- A support quotient reconstructs a point in the offset's residue class. -/
theorem squareOffsetSupportQuotient_mul_modEq_offset
    {n p r : ℕ}
    (hdiv : p ∣ n ^ 2 + r) :
    p * squareOffsetSupportQuotient n p r ≡ r [MOD n] := by
  rw [mul_squareOffsetSupportQuotient_eq hdiv]
  exact squarePacket_left_modEq_base n r

/-! ### PRIM-L021.3: packet determinant and anchor units -/

/- The two support divisibilities carried by one ordered packet cross hit. -/
private theorem packetCross_support_divisibility
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p ∣ n ^ 2 + r ∧ q ∣ n ^ 2 + (n + r) := by
  have hr' := mem_squareAnchorPacketCrossOffsets.mp hr
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hpmem : p ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.1, hpair.2.1, hpair.2.2.1, hr'.2.1⟩
  have hqmem : q ∈ squareOffsetAnchorNondivisorSupport n (n + r) :=
    mem_squareOffsetAnchorNondivisorSupport.mpr
      ⟨hpair.2.2.2.1, hpair.2.2.2.2.1,
        hpair.2.2.2.2.2.1, hr'.2.2⟩
  exact ⟨(mem_squareOffsetAnchorNondivisorSupport.mp hpmem).2.2.2,
    (mem_squareOffsetAnchorNondivisorSupport.mp hqmem).2.2.2⟩

/-- Both factor products of a packet cross hit represent its base residue. -/
theorem packetCross_factor_products_modEq_base
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r ≡ r [MOD n] ∧
      q * squareOffsetSupportQuotient n q (n + r) ≡ r [MOD n] := by
  have hdiv := packetCross_support_divisibility hpq hr
  constructor
  · exact squareOffsetSupportQuotient_mul_modEq_offset hdiv.1
  · rw [mul_squareOffsetSupportQuotient_eq hdiv.2]
    exact squarePacket_right_modEq_base n r

/-- The two factor products are congruent modulo the anchor. -/
theorem packetCross_factor_products_modEq
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r ≡
      q * squareOffsetSupportQuotient n q (n + r) [MOD n] := by
  exact (packetCross_factor_products_modEq_base hpq hr).1.trans
    (packetCross_factor_products_modEq_base hpq hr).2.symm

/-- The exact factor-product difference is one anchor length. -/
theorem packetCross_factor_determinant_eq_anchor
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r + n =
      q * squareOffsetSupportQuotient n q (n + r) := by
  have hdiv := packetCross_support_divisibility hpq hr
  have hleft := mul_squareOffsetSupportQuotient_eq hdiv.1
  have hright := mul_squareOffsetSupportQuotient_eq hdiv.2
  calc
    p * squareOffsetSupportQuotient n p r + n =
        (n ^ 2 + r) + n := by rw [hleft]
    _ = n ^ 2 + (n + r) := by omega
    _ = q * squareOffsetSupportQuotient n q (n + r) := hright.symm

/-- The subtraction form of the one-anchor determinant equation. -/
theorem packetCross_factor_determinant_sub_eq_anchor
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    q * squareOffsetSupportQuotient n q (n + r) -
        p * squareOffsetSupportQuotient n p r = n := by
  have hdet := packetCross_factor_determinant_eq_anchor hpq hr
  omega

/-- All four factors in a packet cross rectangle are coprime to the anchor. -/
theorem packetCross_all_factors_coprime_anchor
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime n p ∧
      Nat.Coprime n q ∧
      Nat.Coprime n (squareOffsetSupportQuotient n p r) ∧
      Nat.Coprime n (squareOffsetSupportQuotient n q (n + r)) := by
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hdiv := packetCross_support_divisibility hpq hr
  have hbase := mem_squareAnchorCoprimeBaseOffsets.mp
    (mem_squareAnchorPacketCrossOffsets.mp hr).1
  have hnp : Nat.Coprime n p :=
    (hpair.1.coprime_iff_not_dvd.mpr hpair.2.2.1).symm
  have hnq : Nat.Coprime n q :=
    (hpair.2.2.2.1.coprime_iff_not_dvd.mpr
      hpair.2.2.2.2.2.1).symm
  have hna : Nat.Coprime n (squareOffsetSupportQuotient n p r) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff
      hpair.1 hpair.2.2.1 hdiv.1).mpr hbase.2.2
  have hnb : Nat.Coprime n (squareOffsetSupportQuotient n q (n + r)) :=
    (coprime_anchor_squareOffsetSupportQuotient_iff
      hpair.2.2.2.1 hpair.2.2.2.2.2.1 hdiv.2).mpr
      (coprime_anchor_add_iff.mpr hbase.2.2)
  exact ⟨hnp, hnq, hna, hnb⟩

/-! ### PRIM-L021.4: reduced-residue factor rectangles -/

/--
The PRIM-L020 factor rectangle with its reduced-residue coordinates.

The exact determinant equation lifts the equality of the two product
residues.  The package records only cross-side coprimality; same-side depth
is deliberately left unrestricted.
-/
theorem squareAnchorPacketCrossOffsets_unitResidue_factorization
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    ∃ a b,
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n p ∧ Nat.Coprime n q ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime p b ∧ Nat.Coprime a q ∧ Nat.Coprime a b ∧
      p * a ≡ r [MOD n] ∧
      q * b ≡ r [MOD n] := by
  rcases squareAnchorPacketCrossOffsets_coprime_factorization hpq hr with
    ⟨a, b, hpa, hqb, hdet, hna, hnb, hca, hcb, hprod, hpb, haq, hab⟩
  have hpair := mem_squareAnchorNondivisorOrderedPrimePairs.mp hpq
  have hnp : Nat.Coprime n p :=
    (hpair.1.coprime_iff_not_dvd.mpr hpair.2.2.1).symm
  have hnq : Nat.Coprime n q :=
    (hpair.2.2.2.1.coprime_iff_not_dvd.mpr
      hpair.2.2.2.2.2.1).symm
  have hleft : p * a ≡ r [MOD n] := by
    rw [hpa]
    exact squarePacket_left_modEq_base n r
  have hright : q * b ≡ r [MOD n] := by
    rw [hqb]
    exact squarePacket_right_modEq_base n r
  exact ⟨a, b, hpa, hqb, hdet, hna, hnb, hnp, hnq, hca, hcb,
    hpb, haq, hab, hleft, hright⟩

/-- Full cover supplies the reduced-residue rectangle for every base packet. -/
theorem exists_unitResidue_factor_rectangle_of_fullyCovered
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
      Nat.Coprime n p ∧ Nat.Coprime n q ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime p b ∧ Nat.Coprime a q ∧ Nat.Coprime a b ∧
      p * a ≡ r [MOD n] ∧
      q * b ≡ r [MOD n] := by
  rcases exists_coprime_factor_rectangle_of_fullyCovered hn hr hfull with
    ⟨p, q, a, b, hpq, hp, hq, hpa, hqb, hdet, hlt_a, hlt_b, hcop_a,
      hcop_b, hprod, hpb, haq, hab⟩
  have hpair := mem_squareAnchorNondivisorPrimes.mp hp
  have hqpair := mem_squareAnchorNondivisorPrimes.mp hq
  have hnp : Nat.Coprime n p :=
    (hpair.1.coprime_iff_not_dvd.mpr hpair.2.2).symm
  have hnq : Nat.Coprime n q :=
    (hqpair.1.coprime_iff_not_dvd.mpr hqpair.2.2).symm
  have hleft : p * a ≡ r [MOD n] := by
    rw [hpa]
    exact squarePacket_left_modEq_base n r
  have hright : q * b ≡ r [MOD n] := by
    rw [hqb]
    exact squarePacket_right_modEq_base n r
  exact ⟨p, q, a, b, hpq, hp, hq, hpa, hqb, hdet, hlt_a, hlt_b, hnp, hnq,
    hcop_a, hcop_b, hpb, haq, hab, hleft, hright⟩

end DkMath.NumberTheory.Legendre
