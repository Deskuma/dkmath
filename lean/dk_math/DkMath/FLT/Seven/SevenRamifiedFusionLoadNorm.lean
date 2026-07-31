/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRealPairLoadAllocation

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionLoadNorm"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace SevenRealCubicInt

/-- Associated elements of the real cubic order have equal absolute
determinant norms. -/
theorem natAbs_norm_eq_of_associated
    {x y : SevenRealCubicInt} (h : Associated x y) :
    Int.natAbs (norm x) = Int.natAbs (norm y) := by
  rcases h with ⟨u, hu⟩
  have hunitNorm : IsUnit (norm (u : SevenRealCubicInt)) := by
    have hmul :
        (u : SevenRealCubicInt) *
            (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
      simp
    have hnorm :
        norm (u : SevenRealCubicInt) *
            norm (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
      have hnorm_one : norm (1 : SevenRealCubicInt) = 1 := by
        norm_num [SevenRealCubicInt.norm]
      simpa only [norm_mul, norm_intCast, one_pow, hnorm_one] using
        congrArg norm hmul
    exact IsUnit.of_mul_eq_one
      (norm (↑(u⁻¹) : SevenRealCubicInt)) hnorm
  have hnorm :
      norm x * norm (u : SevenRealCubicInt) = norm y := by
    simpa only [norm_mul] using congrArg norm hu
  have habs := congrArg Int.natAbs hnorm
  simpa only [Int.natAbs_mul, Int.natAbs_of_isUnit hunitNorm,
    mul_one] using habs

end SevenRealCubicInt

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt

/-- The first routed cell has the same absolute norm at the first two
Galois addresses. -/
theorem natAbs_norm_realPairLoad21_zero_eq_one
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad21 0)) =
      Int.natAbs (norm (p.realPairLoad21 1)) := by
  simpa only [norm_rotateEquiv] using
    natAbs_norm_eq_of_associated
      p.rotate_realPairLoad21_zero_associated_one

/-- The first routed cell has the same absolute norm at the last two
Galois addresses. -/
theorem natAbs_norm_realPairLoad21_one_eq_two
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad21 1)) =
      Int.natAbs (norm (p.realPairLoad21 2)) := by
  simpa only [norm_rotateEquiv] using
    natAbs_norm_eq_of_associated
      p.rotate_realPairLoad21_one_associated_two

/-- The second routed cell has the same absolute norm at the first two
Galois addresses. -/
theorem natAbs_norm_realPairLoad22_zero_eq_one
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad22 0)) =
      Int.natAbs (norm (p.realPairLoad22 1)) := by
  simpa only [norm_rotateEquiv] using
    natAbs_norm_eq_of_associated
      p.rotate_realPairLoad22_zero_associated_one

/-- The second routed cell has the same absolute norm at the last two
Galois addresses. -/
theorem natAbs_norm_realPairLoad22_one_eq_two
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad22 1)) =
      Int.natAbs (norm (p.realPairLoad22 2)) := by
  simpa only [norm_rotateEquiv] using
    natAbs_norm_eq_of_associated
      p.rotate_realPairLoad22_one_associated_two

/-- Taking absolute norms of the first three-way allocation recovers the
cube of its scalar routing cell. -/
theorem natAbs_norm_realPairLoad21_product
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad21 0)) *
        Int.natAbs (norm (p.realPairLoad21 1)) *
        Int.natAbs (norm (p.realPairLoad21 2)) =
      p.routing.c21 ^ 3 := by
  have h := natAbs_norm_eq_of_associated
    p.realPairLoad21_product_associated
  have hc : (p.routing.c21 : SevenRealCubicInt) = (p.routing.c21 : ℤ) := rfl
  simpa only [norm_mul, Int.natAbs_mul, row2Load21Scalar,
    norm_intCast, Int.natAbs_pow, Int.natAbs_natCast,
    Int.cast_ofNat, hc] using h

/-- Taking absolute norms of the second three-way allocation recovers the
cube of its scalar routing cell. -/
theorem natAbs_norm_realPairLoad22_product
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs (norm (p.realPairLoad22 0)) *
        Int.natAbs (norm (p.realPairLoad22 1)) *
        Int.natAbs (norm (p.realPairLoad22 2)) =
      p.routing.c22 ^ 3 := by
  have h := natAbs_norm_eq_of_associated
    p.realPairLoad22_product_associated
  have hc : (p.routing.c22 : SevenRealCubicInt) = (p.routing.c22 : ℤ) := rfl
  simpa only [norm_mul, Int.natAbs_mul, row2Load22Scalar,
    norm_intCast, Int.natAbs_pow, Int.natAbs_natCast,
    Int.cast_ofNat, hc] using h

/-- Every Galois-addressed gcd projection of the first row-two cell has
absolute determinant norm exactly equal to that cell. -/
theorem natAbs_norm_realPairLoad21
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Int.natAbs (norm (p.realPairLoad21 i)) = p.routing.c21 := by
  have h01 := p.natAbs_norm_realPairLoad21_zero_eq_one
  have h12 := p.natAbs_norm_realPairLoad21_one_eq_two
  have h02 := h01.trans h12
  have hcubed :
      Int.natAbs (norm (p.realPairLoad21 0)) ^ 3 =
        p.routing.c21 ^ 3 := by
    calc
      Int.natAbs (norm (p.realPairLoad21 0)) ^ 3 =
          Int.natAbs (norm (p.realPairLoad21 0)) *
            Int.natAbs (norm (p.realPairLoad21 0)) *
            Int.natAbs (norm (p.realPairLoad21 0)) := by ring
      _ = Int.natAbs (norm (p.realPairLoad21 0)) *
            Int.natAbs (norm (p.realPairLoad21 1)) *
            Int.natAbs (norm (p.realPairLoad21 2)) := by
          simp only [h01, h12]
      _ = p.routing.c21 ^ 3 :=
        p.natAbs_norm_realPairLoad21_product
  have hzero :
      Int.natAbs (norm (p.realPairLoad21 0)) =
        p.routing.c21 :=
    Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcubed
  fin_cases i
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h02.symm.trans hzero

/-- Every Galois-addressed gcd projection of the second row-two cell has
absolute determinant norm exactly equal to that cell. -/
theorem natAbs_norm_realPairLoad22
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Int.natAbs (norm (p.realPairLoad22 i)) = p.routing.c22 := by
  have h01 := p.natAbs_norm_realPairLoad22_zero_eq_one
  have h12 := p.natAbs_norm_realPairLoad22_one_eq_two
  have h02 := h01.trans h12
  have hcubed :
      Int.natAbs (norm (p.realPairLoad22 0)) ^ 3 =
        p.routing.c22 ^ 3 := by
    calc
      Int.natAbs (norm (p.realPairLoad22 0)) ^ 3 =
          Int.natAbs (norm (p.realPairLoad22 0)) *
            Int.natAbs (norm (p.realPairLoad22 0)) *
            Int.natAbs (norm (p.realPairLoad22 0)) := by ring
      _ = Int.natAbs (norm (p.realPairLoad22 0)) *
            Int.natAbs (norm (p.realPairLoad22 1)) *
            Int.natAbs (norm (p.realPairLoad22 2)) := by
          simp only [h01, h12]
      _ = p.routing.c22 ^ 3 :=
        p.natAbs_norm_realPairLoad22_product
  have hzero :
      Int.natAbs (norm (p.realPairLoad22 0)) =
        p.routing.c22 :=
    Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcubed
  fin_cases i
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h02.symm.trans hzero

/-- The combined load in every pair core has absolute norm equal to the
product of the two unresolved scalar routing cells. -/
theorem natAbs_norm_realPairCombinedLoad
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Int.natAbs (norm (p.realPairCombinedLoad i)) =
      p.routing.c21 * p.routing.c22 := by
  rw [realPairCombinedLoad, norm_mul, Int.natAbs_mul,
    p.natAbs_norm_realPairLoad21 i,
    p.natAbs_norm_realPairLoad22 i]

/-- Exact norm bookkeeping after removing both routed scalar loads from
one pair core. -/
theorem row2Loads_mul_natAbs_norm_realPairStrippedCore
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.routing.c21 * p.routing.c22 *
        Int.natAbs (norm (p.realPairStrippedCore i)) =
      Int.natAbs p.signedDepth.quotientRoot := by
  calc
    p.routing.c21 * p.routing.c22 *
          Int.natAbs (norm (p.realPairStrippedCore i)) =
        Int.natAbs (norm (p.realPairCombinedLoad i)) *
          Int.natAbs (norm (p.realPairStrippedCore i)) := by
      rw [p.natAbs_norm_realPairCombinedLoad i]
    _ = Int.natAbs
          (norm (p.realPairCombinedLoad i *
            p.realPairStrippedCore i)) := by
      rw [norm_mul, Int.natAbs_mul]
    _ = Int.natAbs
          (norm (p.signedDepth.realPairCore i)) := by
      rw [p.realPairCore_eq_combinedLoad_mul_strippedCore i]
    _ = Int.natAbs p.signedDepth.quotientRoot := by
      rw [p.signedDepth.norm_realPairCore i, Int.natAbs_neg]

/-- The exact norm bookkeeping and the row-two factorization show that all
three stripped cores have the same absolute norm, and that common norm is a
natural seventh power. -/
theorem exists_natAbs_norm_realPairStrippedCore_eq_pow
    (p : RamifiedSignedRootRoutingPacket) :
    ∃ t : ℕ,
      ∀ i : Fin 3,
        Int.natAbs (norm (p.realPairStrippedCore i)) =
          t ^ 7 := by
  rcases p.exists_row2_twoCellSeventhPowerFactor with ⟨t, ht⟩
  have h21 : p.routing.c21 ≠ 0 := by
    intro hzero
    exact p.activeCells_not_seven_dvd.2.2.2.1
      (by rw [hzero]; exact dvd_zero 7)
  have h22 : p.routing.c22 ≠ 0 := by
    intro hzero
    exact p.activeCells_not_seven_dvd.2.2.2.2.1
      (by rw [hzero]; exact dvd_zero 7)
  have hloadPos :
      0 < p.routing.c21 * p.routing.c22 :=
    Nat.pos_of_ne_zero (mul_ne_zero h21 h22)
  refine ⟨t, fun i => ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hloadPos
  calc
    p.routing.c21 * p.routing.c22 *
          Int.natAbs (norm (p.realPairStrippedCore i)) =
        Int.natAbs p.signedDepth.quotientRoot :=
      p.row2Loads_mul_natAbs_norm_realPairStrippedCore i
    _ = p.routing.c21 * p.routing.c22 * t ^ 7 := ht

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven
