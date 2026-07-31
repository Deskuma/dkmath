/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRealPairCoprimalityNormGate

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRealPairLoadAllocation"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

/-- In a gcd domain, a divisor of a product of three pairwise-coprime
elements is, up to a unit, the product of its three gcd projections. -/
theorem associated_gcd_three_of_dvd_product
    {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    {s a b c : R}
    (hab : IsCoprime a b) (hac : IsCoprime a c)
    (hbc : IsCoprime b c) (hs : s ∣ a * (b * c)) :
    Associated
      (GCDMonoid.gcd s a *
        GCDMonoid.gcd s b *
        GCDMonoid.gcd s c)
      s := by
  apply associated_of_dvd_dvd
  · have hgab :
        IsCoprime (GCDMonoid.gcd s a) (GCDMonoid.gcd s b) :=
      hab.mono (GCDMonoid.gcd_dvd_right s a)
        (GCDMonoid.gcd_dvd_right s b)
    have hgac :
        IsCoprime (GCDMonoid.gcd s a) (GCDMonoid.gcd s c) :=
      hac.mono (GCDMonoid.gcd_dvd_right s a)
        (GCDMonoid.gcd_dvd_right s c)
    have hgbc :
        IsCoprime (GCDMonoid.gcd s b) (GCDMonoid.gcd s c) :=
      hbc.mono (GCDMonoid.gcd_dvd_right s b)
        (GCDMonoid.gcd_dvd_right s c)
    exact
      (hgac.mul_left hgbc).mul_dvd
        (hgab.mul_dvd
          (GCDMonoid.gcd_dvd_left s a)
          (GCDMonoid.gcd_dvd_left s b))
        (GCDMonoid.gcd_dvd_left s c)
  · have hsg :
        s ∣ GCDMonoid.gcd s (a * (b * c)) :=
      GCDMonoid.dvd_gcd (dvd_refl s) hs
    apply hsg.trans
    calc
      GCDMonoid.gcd s (a * (b * c)) ∣
          GCDMonoid.gcd s a *
            GCDMonoid.gcd s (b * c) :=
        gcd_mul_dvd_mul_gcd s a (b * c)
      _ ∣ GCDMonoid.gcd s a *
            (GCDMonoid.gcd s b * GCDMonoid.gcd s c) :=
        mul_dvd_mul_left
          (GCDMonoid.gcd s a)
          (gcd_mul_dvd_mul_gcd s b c)
      _ = GCDMonoid.gcd s a *
            GCDMonoid.gcd s b *
            GCDMonoid.gcd s c := by ring

/-- A ring automorphism preserves a chosen gcd up to association.  Literal
equality is neither required nor expected because a `GCDMonoid` does not fix
a normalization convention compatible with every automorphism. -/
theorem associated_map_gcd
    {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    (e : R ≃+* R) (a b : R) :
    Associated
      (e (GCDMonoid.gcd a b))
      (GCDMonoid.gcd (e a) (e b)) := by
  apply associated_of_dvd_dvd
  · exact GCDMonoid.dvd_gcd
      ((map_dvd_iff e).2 (GCDMonoid.gcd_dvd_left a b))
      ((map_dvd_iff e).2 (GCDMonoid.gcd_dvd_right a b))
  · apply (map_dvd_iff e.symm).1
    simpa only [e.symm_apply_apply] using
      GCDMonoid.dvd_gcd
        (map_dvd e.symm
          (GCDMonoid.gcd_dvd_left (e a) (e b)))
        (map_dvd e.symm
          (GCDMonoid.gcd_dvd_right (e a) (e b)))

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt

/-- The product of the three pair cores is associated to the signed
quotient root, without assuming that the latter is a seventh power. -/
theorem pairCore_product_associated_quotientRoot
    (p : RamifiedSignedRootDepthPacket) :
    Associated
      (p.realPairCore 0 *
        (p.realPairCore 1 * p.realPairCore 2))
      (p.quotientRoot : SevenRealCubicInt) := by
  have hunit :
      IsUnit (-(eisensteinAxis + 1) ^ 2) := by
    have hbase :
        IsUnit ((eisensteinAxis + 1) ^ 2) := by
      simpa [eisensteinAxisUnit] using
        (eisensteinAxisUnit_isUnit.pow 2)
    exact hbase.neg
  have hproduct :
      -(eisensteinAxis + 1) ^ 2 *
          (p.realPairCore 0 *
            (p.realPairCore 1 * p.realPairCore 2)) =
        (p.quotientRoot : SevenRealCubicInt) := by
    simpa [mul_assoc] using p.pairCore_product_eq_quotientRoot
  exact
    (associated_unit_mul_left _ _ hunit).symm.trans
      (Associated.of_eq hproduct)

/-- The first Galois rotation of the zeroth pair core is the first pair
core up to its explicit axis unit. -/
theorem rotate_realPairCore_zero_associated_one
    (p : RamifiedSignedRootDepthPacket) :
    Associated
      (rotateEquiv (p.realPairCore 0))
      (p.realPairCore 1) := by
  have hunit : IsUnit (pairAxisUnit 1) := by
    simpa only [pairAxisUnit_one] using alphaAddOne_isUnit
  exact
    (associated_unit_mul_left _ _ hunit).symm.trans
      (Associated.of_eq
        p.realPairCore_one_eq_unit_mul_rotate.symm)

/-- The second Galois step carries the first pair core to the second one
up to association. -/
theorem rotate_realPairCore_one_associated_two
    (p : RamifiedSignedRootDepthPacket) :
    Associated
      (rotateEquiv (p.realPairCore 1))
      (p.realPairCore 2) := by
  have hunit1 : IsUnit (pairAxisUnit 1) := by
    simpa only [pairAxisUnit_one] using alphaAddOne_isUnit
  have hrotateUnit1 :
      IsUnit (rotateEquiv (pairAxisUnit 1)) :=
    IsUnit.map rotateEquiv.toRingHom hunit1
  have hunit2 : IsUnit (pairAxisUnit 2) := by
    simpa only [pairAxisUnit_two] using alpha_isUnit.pow 2
  have hrotate :
      rotateEquiv (p.realPairCore 1) =
        rotateEquiv (pairAxisUnit 1) *
          rotateEquiv (rotateEquiv (p.realPairCore 0)) := by
    rw [p.realPairCore_one_eq_unit_mul_rotate, map_mul]
  have hleft :
      Associated
        (rotateEquiv (p.realPairCore 1))
        (rotateEquiv (rotateEquiv
          (p.realPairCore 0))) :=
    (Associated.of_eq hrotate).trans
      (associated_unit_mul_left _ _ hrotateUnit1)
  have hright :
      Associated
        (p.realPairCore 2)
        (rotateEquiv (rotateEquiv
          (p.realPairCore 0))) :=
    (Associated.of_eq
      p.realPairCore_two_eq_unit_mul_rotate_sq).trans
        (associated_unit_mul_left _ _ hunit2)
  exact hleft.trans hright.symm

/-- The third Galois step closes the associated core orbit. -/
theorem rotate_realPairCore_two_associated_zero
    (p : RamifiedSignedRootDepthPacket) :
    Associated
      (rotateEquiv (p.realPairCore 2))
      (p.realPairCore 0) := by
  have hunit2 : IsUnit (pairAxisUnit 2) := by
    simpa only [pairAxisUnit_two] using alpha_isUnit.pow 2
  have hrotateUnit2 :
      IsUnit (rotateEquiv (pairAxisUnit 2)) :=
    IsUnit.map rotateEquiv.toRingHom hunit2
  have hrotate :
      rotateEquiv (p.realPairCore 2) =
        rotateEquiv (pairAxisUnit 2) *
          p.realPairCore 0 := by
    rw [p.realPairCore_two_eq_unit_mul_rotate_sq,
      map_mul, rotateEquiv_three]
  exact
    (Associated.of_eq hrotate).trans
      (associated_unit_mul_left _ _ hrotateUnit2)

end RamifiedSignedRootDepthPacket

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt

local instance realPairLoadGCDMonoid :
    GCDMonoid SevenRealCubicInt :=
  IsBezout.toGCDDomain SevenRealCubicInt

/-- Scalar cast of the first unresolved row-two routing cell. -/
def row2Load21Scalar
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  (p.routing.c21 : SevenRealCubicInt)

/-- Scalar cast of the second unresolved row-two routing cell. -/
def row2Load22Scalar
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  (p.routing.c22 : SevenRealCubicInt)

/-- Canonical PID gcd projection of the first scalar load into core `i`. -/
def realPairLoad21
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  GCDMonoid.gcd p.row2Load21Scalar
    (p.signedDepth.realPairCore i)

/-- Canonical PID gcd projection of the second scalar load into core `i`. -/
def realPairLoad22
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  GCDMonoid.gcd p.row2Load22Scalar
    (p.signedDepth.realPairCore i)

private theorem rotate_gcd_associated_of_fixed_left
    (s a b : SevenRealCubicInt)
    (hs : rotateEquiv s = s)
    (hab : Associated (rotateEquiv a) b) :
    Associated
      (rotateEquiv (GCDMonoid.gcd s a))
      (GCDMonoid.gcd s b) := by
  exact
    (associated_map_gcd rotateEquiv s a).trans
      (Associated.gcd (Associated.of_eq hs) hab)

/-- The first cell-load projections form the same Galois orbit as the
three pair cores, up to gcd normalization units. -/
theorem rotate_realPairLoad21_zero_associated_one
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad21 0))
      (p.realPairLoad21 1) := by
  have hs :
      rotateEquiv p.row2Load21Scalar =
        p.row2Load21Scalar := by
    simp [row2Load21Scalar]
  simpa only [realPairLoad21] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load21Scalar
      (p.signedDepth.realPairCore 0)
      (p.signedDepth.realPairCore 1)
      hs p.signedDepth.rotate_realPairCore_zero_associated_one

theorem rotate_realPairLoad21_one_associated_two
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad21 1))
      (p.realPairLoad21 2) := by
  have hs :
      rotateEquiv p.row2Load21Scalar =
        p.row2Load21Scalar := by
    simp [row2Load21Scalar]
  simpa only [realPairLoad21] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load21Scalar
      (p.signedDepth.realPairCore 1)
      (p.signedDepth.realPairCore 2)
      hs p.signedDepth.rotate_realPairCore_one_associated_two

theorem rotate_realPairLoad21_two_associated_zero
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad21 2))
      (p.realPairLoad21 0) := by
  have hs :
      rotateEquiv p.row2Load21Scalar =
        p.row2Load21Scalar := by
    simp [row2Load21Scalar]
  simpa only [realPairLoad21] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load21Scalar
      (p.signedDepth.realPairCore 2)
      (p.signedDepth.realPairCore 0)
      hs p.signedDepth.rotate_realPairCore_two_associated_zero

/-- The second cell-load projections obey the same complete associated
Galois cycle. -/
theorem rotate_realPairLoad22_zero_associated_one
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad22 0))
      (p.realPairLoad22 1) := by
  have hs :
      rotateEquiv p.row2Load22Scalar =
        p.row2Load22Scalar := by
    simp [row2Load22Scalar]
  simpa only [realPairLoad22] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load22Scalar
      (p.signedDepth.realPairCore 0)
      (p.signedDepth.realPairCore 1)
      hs p.signedDepth.rotate_realPairCore_zero_associated_one

theorem rotate_realPairLoad22_one_associated_two
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad22 1))
      (p.realPairLoad22 2) := by
  have hs :
      rotateEquiv p.row2Load22Scalar =
        p.row2Load22Scalar := by
    simp [row2Load22Scalar]
  simpa only [realPairLoad22] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load22Scalar
      (p.signedDepth.realPairCore 1)
      (p.signedDepth.realPairCore 2)
      hs p.signedDepth.rotate_realPairCore_one_associated_two

theorem rotate_realPairLoad22_two_associated_zero
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairLoad22 2))
      (p.realPairLoad22 0) := by
  have hs :
      rotateEquiv p.row2Load22Scalar =
        p.row2Load22Scalar := by
    simp [row2Load22Scalar]
  simpa only [realPairLoad22] using
    rotate_gcd_associated_of_fixed_left
      p.row2Load22Scalar
      (p.signedDepth.realPairCore 2)
      (p.signedDepth.realPairCore 0)
      hs p.signedDepth.rotate_realPairCore_two_associated_zero

private theorem row2Load21Scalar_dvd_coreProduct
    (p : RamifiedSignedRootRoutingPacket) :
    p.row2Load21Scalar ∣
      p.signedDepth.realPairCore 0 *
        (p.signedDepth.realPairCore 1 *
          p.signedDepth.realPairCore 2) := by
  have hnat :
      p.routing.c21 ∣
        Int.natAbs p.signedDepth.quotientRoot :=
    p.routing.c21_dvd_row2
  have hint :
      (p.routing.c21 : ℤ) ∣
        p.signedDepth.quotientRoot :=
    Int.natCast_dvd.mpr hnat
  rcases hint with ⟨k, hk⟩
  have hcubic :
      p.row2Load21Scalar ∣
        (p.signedDepth.quotientRoot : SevenRealCubicInt) := by
    refine ⟨(k : SevenRealCubicInt), ?_⟩
    convert congrArg (fun z : ℤ => (z : SevenRealCubicInt)) hk using 1 <;>
      simp [row2Load21Scalar, Int.cast_mul, Int.cast_ofNat]
  exact hcubic.trans
    p.signedDepth.pairCore_product_associated_quotientRoot.symm.dvd

private theorem row2Load22Scalar_dvd_coreProduct
    (p : RamifiedSignedRootRoutingPacket) :
    p.row2Load22Scalar ∣
      p.signedDepth.realPairCore 0 *
        (p.signedDepth.realPairCore 1 *
          p.signedDepth.realPairCore 2) := by
  have hnat :
      p.routing.c22 ∣
        Int.natAbs p.signedDepth.quotientRoot :=
    p.routing.c22_dvd_row2
  have hint :
      (p.routing.c22 : ℤ) ∣
        p.signedDepth.quotientRoot :=
    Int.natCast_dvd.mpr hnat
  rcases hint with ⟨k, hk⟩
  have hcubic :
      p.row2Load22Scalar ∣
        (p.signedDepth.quotientRoot : SevenRealCubicInt) := by
    refine ⟨(k : SevenRealCubicInt), ?_⟩
    convert congrArg (fun z : ℤ => (z : SevenRealCubicInt)) hk using 1 <;>
      simp [row2Load22Scalar, Int.cast_mul, Int.cast_ofNat]
  exact hcubic.trans
    p.signedDepth.pairCore_product_associated_quotientRoot.symm.dvd

/-- The three PID projections allocate the entire first scalar cell load,
up to the unavoidable gcd normalization unit. -/
theorem realPairLoad21_product_associated
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (p.realPairLoad21 0 *
        p.realPairLoad21 1 *
        p.realPairLoad21 2)
      p.row2Load21Scalar := by
  have h01 :
      IsCoprime (p.signedDepth.realPairCore 0)
        (p.signedDepth.realPairCore 1) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  have h02 :
      IsCoprime (p.signedDepth.realPairCore 0)
        (p.signedDepth.realPairCore 2) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  have h12 :
      IsCoprime (p.signedDepth.realPairCore 1)
        (p.signedDepth.realPairCore 2) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  simpa [realPairLoad21, mul_assoc] using
    associated_gcd_three_of_dvd_product
      h01 h02 h12 p.row2Load21Scalar_dvd_coreProduct

/-- The three PID projections allocate the entire second scalar cell load,
again only up to gcd normalization. -/
theorem realPairLoad22_product_associated
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (p.realPairLoad22 0 *
        p.realPairLoad22 1 *
        p.realPairLoad22 2)
      p.row2Load22Scalar := by
  have h01 :
      IsCoprime (p.signedDepth.realPairCore 0)
        (p.signedDepth.realPairCore 1) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  have h02 :
      IsCoprime (p.signedDepth.realPairCore 0)
        (p.signedDepth.realPairCore 2) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  have h12 :
      IsCoprime (p.signedDepth.realPairCore 1)
        (p.signedDepth.realPairCore 2) :=
    p.signedDepth.realPairCores_pairwiseCoprime (by decide)
  simpa [realPairLoad22, mul_assoc] using
    associated_gcd_three_of_dvd_product
      h01 h02 h12 p.row2Load22Scalar_dvd_coreProduct

/-- The two scalar routing cells remain coprime after mapping into the
real cubic order. -/
theorem row2LoadScalars_isCoprime
    (p : RamifiedSignedRootRoutingPacket) :
    IsCoprime p.row2Load21Scalar p.row2Load22Scalar := by
  simpa [row2Load21Scalar, row2Load22Scalar] using
    p.routing.row2_coprime.1.isCoprime.map
      (Int.castRingHom SevenRealCubicInt)

theorem realPairLoad21_dvd_core
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.realPairLoad21 i ∣ p.signedDepth.realPairCore i :=
  GCDMonoid.gcd_dvd_right _ _

theorem realPairLoad22_dvd_core
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.realPairLoad22 i ∣ p.signedDepth.realPairCore i :=
  GCDMonoid.gcd_dvd_right _ _

/-- The two gcd projections in one core are coprime because they divide
the two coprime scalar routing cells. -/
theorem realPairLoads_isCoprime
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    IsCoprime (p.realPairLoad21 i) (p.realPairLoad22 i) := by
  exact p.row2LoadScalars_isCoprime.mono
    (GCDMonoid.gcd_dvd_left _ _)
    (GCDMonoid.gcd_dvd_left _ _)

/-- Product of the two routed load projections carried by core `i`. -/
def realPairCombinedLoad
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  p.realPairLoad21 i * p.realPairLoad22 i

/-- The combined two-cell loads inherit the complete associated Galois
cycle from their two gcd projections. -/
theorem rotate_realPairCombinedLoad_zero_associated_one
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairCombinedLoad 0))
      (p.realPairCombinedLoad 1) := by
  simpa only [realPairCombinedLoad, map_mul] using
    p.rotate_realPairLoad21_zero_associated_one.mul_mul
      p.rotate_realPairLoad22_zero_associated_one

theorem rotate_realPairCombinedLoad_one_associated_two
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairCombinedLoad 1))
      (p.realPairCombinedLoad 2) := by
  simpa only [realPairCombinedLoad, map_mul] using
    p.rotate_realPairLoad21_one_associated_two.mul_mul
      p.rotate_realPairLoad22_one_associated_two

theorem rotate_realPairCombinedLoad_two_associated_zero
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (p.realPairCombinedLoad 2))
      (p.realPairCombinedLoad 0) := by
  simpa only [realPairCombinedLoad, map_mul] using
    p.rotate_realPairLoad21_two_associated_zero.mul_mul
      p.rotate_realPairLoad22_two_associated_zero

/-- Both projected loads divide the same core, hence their coprime product
does too. -/
theorem realPairCombinedLoad_dvd_core
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.realPairCombinedLoad i ∣
      p.signedDepth.realPairCore i := by
  exact p.realPairLoads_isCoprime i |>.mul_dvd
    (p.realPairLoad21_dvd_core i)
    (p.realPairLoad22_dvd_core i)

/-- Integral quotient after removing precisely the two routed gcd loads.
No field division is used. -/
def realPairStrippedCore
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  Classical.choose (p.realPairCombinedLoad_dvd_core i)

/-- Exact integral reconstruction of a core from its two loads and its
stripped residual. -/
theorem realPairCore_eq_combinedLoad_mul_strippedCore
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.signedDepth.realPairCore i =
      p.realPairCombinedLoad i * p.realPairStrippedCore i :=
  Classical.choose_spec (p.realPairCombinedLoad_dvd_core i)

theorem realPairStrippedCore_dvd_core
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.realPairStrippedCore i ∣
      p.signedDepth.realPairCore i := by
  refine ⟨p.realPairCombinedLoad i, ?_⟩
  rw [p.realPairCore_eq_combinedLoad_mul_strippedCore]
  ring

/-- Removing routed factors cannot introduce a common factor between two
formerly coprime cores. -/
theorem realPairStrippedCores_pairwiseCoprime
    (p : RamifiedSignedRootRoutingPacket) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (p.realPairStrippedCore i)
          (p.realPairStrippedCore j)) := by
  intro i j hij
  exact
    (p.signedDepth.realPairCores_pairwiseCoprime hij).mono
      (p.realPairStrippedCore_dvd_core i)
      (p.realPairStrippedCore_dvd_core j)

/-- Grouping the two three-way allocation theorems allocates the complete
two-cell scalar load. -/
theorem realPairLoadProducts_associated
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      ((p.realPairLoad21 0 *
          p.realPairLoad21 1 *
          p.realPairLoad21 2) *
        (p.realPairLoad22 0 *
          p.realPairLoad22 1 *
          p.realPairLoad22 2))
      (p.row2Load21Scalar * p.row2Load22Scalar) :=
  p.realPairLoad21_product_associated.mul_mul
    p.realPairLoad22_product_associated

/-- Product of the three per-core combined loads. -/
def realPairCombinedLoadProduct
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  p.realPairCombinedLoad 0 *
    (p.realPairCombinedLoad 1 * p.realPairCombinedLoad 2)

/-- Product of the three stripped residual cores. -/
def realPairStrippedCoreProduct
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  p.realPairStrippedCore 0 *
    (p.realPairStrippedCore 1 * p.realPairStrippedCore 2)

/-- The grouped product of all six gcd loads is associated to the product
of the two scalar routing cells. -/
theorem realPairCombinedLoadProduct_associated
    (p : RamifiedSignedRootRoutingPacket) :
    Associated p.realPairCombinedLoadProduct
      (p.row2Load21Scalar * p.row2Load22Scalar) := by
  have hgroup :
      p.realPairCombinedLoadProduct =
        (p.realPairLoad21 0 *
          p.realPairLoad21 1 *
          p.realPairLoad21 2) *
        (p.realPairLoad22 0 *
          p.realPairLoad22 1 *
          p.realPairLoad22 2) := by
    simp only [realPairCombinedLoadProduct, realPairCombinedLoad]
    ring
  exact (Associated.of_eq hgroup).trans
    p.realPairLoadProducts_associated

/-- Exact factorization of the three-core product into all routed loads
and the residual stripped product. -/
theorem realPairCoreProduct_eq_loadProduct_mul_strippedProduct
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.realPairCore 0 *
        (p.signedDepth.realPairCore 1 *
          p.signedDepth.realPairCore 2) =
      p.realPairCombinedLoadProduct *
        p.realPairStrippedCoreProduct := by
  rw [p.realPairCore_eq_combinedLoad_mul_strippedCore 0,
    p.realPairCore_eq_combinedLoad_mul_strippedCore 1,
    p.realPairCore_eq_combinedLoad_mul_strippedCore 2]
  simp only [realPairCombinedLoadProduct, realPairStrippedCoreProduct]
  ring

/-- The signed quotient root is associated to the two scalar loads times
the seventh power left in routing column three. -/
theorem exists_quotientRoot_associated_row2Loads_mul_pow
    (p : RamifiedSignedRootRoutingPacket) :
    ∃ t : ℕ,
      Associated
        (p.signedDepth.quotientRoot : SevenRealCubicInt)
        (p.row2Load21Scalar * p.row2Load22Scalar *
          (t : SevenRealCubicInt) ^ 7) := by
  rcases p.exists_row2_twoCellSeventhPowerFactor with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have habs :
      ((Int.natAbs p.signedDepth.quotientRoot : ℕ) :
          SevenRealCubicInt) =
        p.row2Load21Scalar * p.row2Load22Scalar *
          (t : SevenRealCubicInt) ^ 7 := by
    simpa only [row2Load21Scalar, row2Load22Scalar,
      Nat.cast_mul, Nat.cast_pow] using
        congrArg
          (fun n : ℕ => (n : SevenRealCubicInt)) ht
  rcases Int.natAbs_eq p.signedDepth.quotientRoot with hq | hq
  · have hqC := congrArg
      (fun z : ℤ => (z : SevenRealCubicInt)) hq
    exact Associated.of_eq <| by
      calc
        (p.signedDepth.quotientRoot : SevenRealCubicInt) =
            ((Int.natAbs p.signedDepth.quotientRoot : ℕ) :
              SevenRealCubicInt) := by simpa using hqC
        _ = _ := habs
  · have hqC := congrArg
      (fun z : ℤ => (z : SevenRealCubicInt)) hq
    have hneg :
        (p.signedDepth.quotientRoot : SevenRealCubicInt) =
          -(p.row2Load21Scalar * p.row2Load22Scalar *
            (t : SevenRealCubicInt) ^ 7) := by
      calc
        (p.signedDepth.quotientRoot : SevenRealCubicInt) =
            -(((Int.natAbs p.signedDepth.quotientRoot : ℕ) :
              SevenRealCubicInt)) := by simpa using hqC
        _ = _ := by rw [habs]
    exact (Associated.of_eq hneg).trans Associated.rfl.neg_left

private theorem row2Load21Scalar_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.row2Load21Scalar ≠ 0 := by
  have h21 : p.routing.c21 ≠ 0 := by
    intro hzero
    exact p.activeCells_not_seven_dvd.2.2.2.1
      (by rw [hzero]; exact dvd_zero 7)
  intro hzero
  apply h21
  have hfst := congrArg SevenRealCubicInt.fst hzero
  simpa [row2Load21Scalar] using hfst

private theorem row2Load22Scalar_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.row2Load22Scalar ≠ 0 := by
  have h22 : p.routing.c22 ≠ 0 := by
    intro hzero
    exact p.activeCells_not_seven_dvd.2.2.2.2.1
      (by rw [hzero]; exact dvd_zero 7)
  intro hzero
  apply h22
  have hfst := congrArg SevenRealCubicInt.fst hzero
  simpa [row2Load22Scalar] using hfst

/-- After the canonically allocated scalar loads are cancelled, the three
stripped cores have product associated to an unconditional seventh power. -/
theorem exists_realPairStrippedCoreProduct_associated_pow
    (p : RamifiedSignedRootRoutingPacket) :
    ∃ t : SevenRealCubicInt,
      Associated p.realPairStrippedCoreProduct (t ^ 7) := by
  rcases p.exists_quotientRoot_associated_row2Loads_mul_pow with
    ⟨t, hquotient⟩
  refine ⟨(t : SevenRealCubicInt), ?_⟩
  have hcore :
      Associated
        (p.signedDepth.realPairCore 0 *
          (p.signedDepth.realPairCore 1 *
            p.signedDepth.realPairCore 2))
        (p.row2Load21Scalar * p.row2Load22Scalar *
          (t : SevenRealCubicInt) ^ 7) :=
    p.signedDepth.pairCore_product_associated_quotientRoot.trans
      hquotient
  have hfactored :
      Associated
        (p.realPairCombinedLoadProduct *
          p.realPairStrippedCoreProduct)
        ((p.row2Load21Scalar * p.row2Load22Scalar) *
          (t : SevenRealCubicInt) ^ 7) :=
    (Associated.of_eq
      p.realPairCoreProduct_eq_loadProduct_mul_strippedProduct.symm).trans
        hcore
  have hload_ne :
      p.realPairCombinedLoadProduct ≠ 0 :=
    p.realPairCombinedLoadProduct_associated.ne_zero_iff.mpr
      (mul_ne_zero p.row2Load21Scalar_ne_zero
        p.row2Load22Scalar_ne_zero)
  exact Associated.of_mul_left hfactored
    p.realPairCombinedLoadProduct_associated hload_ne

/-- The routed load split with an unconditional seventh-power residual in
each of the three pair cores. -/
structure RealPairLoadedPowerSplit
    (p : RamifiedSignedRootRoutingPacket) where
  load21 : Fin 3 → SevenRealCubicInt
  load22 : Fin 3 → SevenRealCubicInt
  residualRoot : Fin 3 → SevenRealCubicInt
  load21_eq_gcd : load21 = p.realPairLoad21
  load22_eq_gcd : load22 = p.realPairLoad22
  residualAssociated :
    ∀ i,
      Associated
        (residualRoot i ^ 7)
        (p.realPairStrippedCore i)
  coreAssociated :
    ∀ i,
      Associated
        (load21 i * load22 i * residualRoot i ^ 7)
        (p.signedDepth.realPairCore i)
  load21Product :
    Associated
      (load21 0 * load21 1 * load21 2)
      p.row2Load21Scalar
  load22Product :
    Associated
      (load22 0 * load22 1 * load22 2)
      p.row2Load22Scalar

/-- FUSION-003F loaded-core output: both scalar cells are allocated by PID
gcd projection and every remaining integral core is a seventh power up to
a unit. -/
theorem nonempty_realPairLoadedPowerSplit
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty (RealPairLoadedPowerSplit p) := by
  rcases p.exists_realPairStrippedCoreProduct_associated_pow with
    ⟨t, hproduct⟩
  have h01 :
      IsCoprime (p.realPairStrippedCore 0)
        (p.realPairStrippedCore 1) :=
    p.realPairStrippedCores_pairwiseCoprime (by decide)
  have h02 :
      IsCoprime (p.realPairStrippedCore 0)
        (p.realPairStrippedCore 2) :=
    p.realPairStrippedCores_pairwiseCoprime (by decide)
  have h12 :
      IsCoprime (p.realPairStrippedCore 1)
        (p.realPairStrippedCore 2) :=
    p.realPairStrippedCores_pairwiseCoprime (by decide)
  have hpow :
      Associated (t ^ 7)
        (p.realPairStrippedCore 0 *
          (p.realPairStrippedCore 1 *
            p.realPairStrippedCore 2)) :=
    hproduct.symm
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.mul_right h02) hpow with
    ⟨root0, hroot0⟩
  have hpow1 :
      Associated (t ^ 7)
        (p.realPairStrippedCore 1 *
          (p.realPairStrippedCore 0 *
            p.realPairStrippedCore 2)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.symm.mul_right h12) hpow1 with
    ⟨root1, hroot1⟩
  have hpow2 :
      Associated (t ^ 7)
        (p.realPairStrippedCore 2 *
          (p.realPairStrippedCore 0 *
            p.realPairStrippedCore 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
  rcases exists_associated_pow_of_associated_pow_mul
      (h02.symm.mul_right h12.symm) hpow2 with
    ⟨root2, hroot2⟩
  let roots : Fin 3 → SevenRealCubicInt :=
    ![root0, root1, root2]
  have hroot :
      ∀ i : Fin 3,
        Associated (roots i ^ 7)
          (p.realPairStrippedCore i) := by
    intro i
    fin_cases i
    · exact hroot0
    · exact hroot1
    · exact hroot2
  refine ⟨{
    load21 := p.realPairLoad21
    load22 := p.realPairLoad22
    residualRoot := roots
    load21_eq_gcd := rfl
    load22_eq_gcd := rfl
    residualAssociated := hroot
    coreAssociated := ?_
    load21Product := p.realPairLoad21_product_associated
    load22Product := p.realPairLoad22_product_associated }⟩
  intro i
  have hmul :
      Associated
        (p.realPairCombinedLoad i * roots i ^ 7)
        (p.realPairCombinedLoad i *
          p.realPairStrippedCore i) :=
    Associated.rfl.mul_mul (hroot i)
  have hcore :
      Associated
        (p.realPairCombinedLoad i *
          p.realPairStrippedCore i)
        (p.signedDepth.realPairCore i) :=
    Associated.of_eq
      (p.realPairCore_eq_combinedLoad_mul_strippedCore i).symm
  simpa [realPairCombinedLoad, mul_assoc] using hmul.trans hcore

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven
