/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionLoadedCore
import DkMath.FLT.Seven.SevenRamifiedFusionLoadNorm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadAddress"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

/-- The two unresolved scalar-load families in routing row two. -/
inductive RamifiedFusionRow2LoadFamily
  | cell21
  | cell22
deriving DecidableEq, Repr

namespace RamifiedFusionRow2LoadFamily

open SevenRealCubicInt

/-- Integer routing cell underlying one of the two load families. -/
def cell
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) : ℕ :=
  match family with
  | .cell21 => p.routing.c21
  | .cell22 => p.routing.c22

/-- Scalar cast of the selected routing cell into the real cubic order. -/
def scalar
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  match family with
  | .cell21 => p.row2Load21Scalar
  | .cell22 => p.row2Load22Scalar

/-- Canonical gcd projection of the selected scalar cell into pair core `i`. -/
def load
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  match family with
  | .cell21 => p.realPairLoad21 i
  | .cell22 => p.realPairLoad22 i

/-- The other gcd-load family in the same pair core. -/
def otherLoad
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  match family with
  | .cell21 => p.realPairLoad22 i
  | .cell22 => p.realPairLoad21 i

/-- The other scalar routing cell. -/
def otherScalar
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    SevenRealCubicInt :=
  match family with
  | .cell21 => p.row2Load22Scalar
  | .cell22 => p.row2Load21Scalar

/-- Either unresolved scalar cell divides the absolute signed quotient root. -/
theorem cell_dvd_quotientRoot_natAbs
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    family.cell p ∣ Int.natAbs p.signedDepth.quotientRoot := by
  cases family
  · exact p.routing.c21_dvd_row2
  · exact p.routing.c22_dvd_row2

end RamifiedFusionRow2LoadFamily

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt

local instance primeLoadAddressGCDMonoid :
    GCDMonoid SevenRealCubicInt :=
  IsBezout.toGCDDomain SevenRealCubicInt

/-- A rational prime divisor of either unresolved row-two cell, retaining
which scalar gcd-load family it addresses.

The associated `muSevenAddress` below is not arbitrary packet data: it is
definitionally reconstructed from the signed roots and this prime divisor. -/
structure QuotientPrimeGCDLoadAddress
    (p : RamifiedSignedRootRoutingPacket) (q : ℕ) where
  family : RamifiedFusionRow2LoadFamily
  prime : Nat.Prime q
  dividesCell : q ∣ family.cell p

/-- Canonical address of a prime divisor of cell `c21`. -/
def quotientPrimeGCDLoadAddress21
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqc : q ∣ p.routing.c21) :
    QuotientPrimeGCDLoadAddress p q where
  family := .cell21
  prime := hq
  dividesCell := hqc

/-- Canonical address of a prime divisor of cell `c22`. -/
def quotientPrimeGCDLoadAddress22
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqc : q ∣ p.routing.c22) :
    QuotientPrimeGCDLoadAddress p q where
  family := .cell22
  prime := hq
  dividesCell := hqc

namespace QuotientPrimeGCDLoadAddress

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- The selected cell prime is also a prime divisor of the signed quotient
root, hence supplies the canonical signed-root `mu_7` ratio. -/
def muSevenAddress
    (a : QuotientPrimeGCDLoadAddress p q) :
    p.signedDepth.QuotientPrimeMuSevenAddress q where
  prime := a.prime
  dividesQuotientRoot :=
    Int.natCast_dvd.mpr
      (a.dividesCell.trans
        (a.family.cell_dvd_quotientRoot_natAbs p))

/-- The explicit real-cubic residue-field evaluation at this load address. -/
def evalAlphaRoot
    (a : QuotientPrimeGCDLoadAddress p q) :
    SevenRealCubicInt →+* ZMod q :=
  a.muSevenAddress.evalAlphaRoot

/-- The degree-one prime ideal selected by the signed-root ratio. -/
def evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    Ideal SevenRealCubicInt :=
  RingHom.ker a.evalAlphaRoot

/-- The selected scalar gcd projection in the zeroth real-pair core. -/
def addressedLoad
    (a : QuotientPrimeGCDLoadAddress p q) :
    SevenRealCubicInt :=
  a.family.load p 0

/-- The projection of the other, coprime row-two scalar cell into the same
core. -/
def competingLoad
    (a : QuotientPrimeGCDLoadAddress p q) :
    SevenRealCubicInt :=
  a.family.otherLoad p 0

/-- The scalar routing cell selected by this address. -/
def addressedScalar
    (a : QuotientPrimeGCDLoadAddress p q) :
    SevenRealCubicInt :=
  a.family.scalar p

/-- The other scalar routing cell. -/
def competingScalar
    (a : QuotientPrimeGCDLoadAddress p q) :
    SevenRealCubicInt :=
  a.family.otherScalar p

/-- Every row-two load prime is one modulo fourteen. -/
theorem prime_modFourteen_eq_one
    (a : QuotientPrimeGCDLoadAddress p q) :
    q % 14 = 1 :=
  p.signedDepth.prime_dvd_quotientRoot_modFourteen_eq_one
    a.prime a.muSevenAddress.dividesQuotientRoot

/-- The selected local evaluation kills the zeroth normalized pair core. -/
theorem evalAlphaRoot_realPairCore_zero
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalAlphaRoot (p.signedDepth.realPairCore 0) = 0 :=
  a.muSevenAddress.evalAlphaRoot_realPairCore_zero

/-- The normalized pair core lies in the selected explicit kernel ideal. -/
theorem realPairCore_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    p.signedDepth.realPairCore 0 ∈ a.evalKernel :=
  a.evalAlphaRoot_realPairCore_zero

/-- The ramified prime above seven is excluded from every row-two load
address. -/
theorem eisensteinAxis_not_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    eisensteinAxis ∉ a.evalKernel :=
  a.muSevenAddress.eisensteinAxis_not_mem_evalAlphaRoot_ker

/-- The selected scalar cell vanishes at its rational prime address. -/
theorem evalAlphaRoot_addressedScalar_zero
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalAlphaRoot a.addressedScalar = 0 := by
  cases hfamily : a.family with
  | cell21 =>
      have hqc : q ∣ p.routing.c21 := by
        simpa only [hfamily, RamifiedFusionRow2LoadFamily.cell] using
          a.dividesCell
      rw [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar]
      change
        a.evalAlphaRoot (p.routing.c21 : SevenRealCubicInt) = 0
      simpa only [map_natCast] using
        (ZMod.natCast_eq_zero_iff p.routing.c21 q).2 hqc
  | cell22 =>
      have hqc : q ∣ p.routing.c22 := by
        simpa only [hfamily, RamifiedFusionRow2LoadFamily.cell] using
          a.dividesCell
      rw [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar]
      change
        a.evalAlphaRoot (p.routing.c22 : SevenRealCubicInt) = 0
      simpa only [map_natCast] using
        (ZMod.natCast_eq_zero_iff p.routing.c22 q).2 hqc

private theorem map_gcd_eq_zero
    {S : Type*} [CommRing S]
    (f : SevenRealCubicInt →+* S)
    (x y : SevenRealCubicInt)
    (hx : f x = 0) (hy : f y = 0) :
    f (GCDMonoid.gcd x y) = 0 := by
  rcases exists_gcd_eq_mul_add_mul x y with ⟨u, v, huv⟩
  rw [huv, map_add, map_mul, map_mul, hx, hy,
    zero_mul, zero_mul, add_zero]

/-- The canonical gcd projection of the addressed scalar and the zeroth
pair core belongs to their common residue-field kernel. -/
theorem evalAlphaRoot_addressedLoad_zero
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalAlphaRoot a.addressedLoad = 0 := by
  cases hfamily : a.family with
  | cell21 =>
      have hscalar := a.evalAlphaRoot_addressedScalar_zero
      rw [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar] at hscalar
      rw [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load]
      change
        a.evalAlphaRoot
          (GCDMonoid.gcd p.row2Load21Scalar
            (p.signedDepth.realPairCore 0)) = 0
      exact map_gcd_eq_zero a.evalAlphaRoot _ _
        hscalar
        a.evalAlphaRoot_realPairCore_zero
  | cell22 =>
      have hscalar := a.evalAlphaRoot_addressedScalar_zero
      rw [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar] at hscalar
      rw [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load]
      change
        a.evalAlphaRoot
          (GCDMonoid.gcd p.row2Load22Scalar
            (p.signedDepth.realPairCore 0)) = 0
      exact map_gcd_eq_zero a.evalAlphaRoot _ _
        hscalar
        a.evalAlphaRoot_realPairCore_zero

/-- Ideal-membership form of the prime-to-gcd-load address theorem. -/
theorem addressedLoad_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.addressedLoad ∈ a.evalKernel :=
  a.evalAlphaRoot_addressedLoad_zero

/-- The principal ideal generated by the addressed gcd load is contained in
the explicit degree-one prime ideal. -/
theorem span_addressedLoad_le_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    Ideal.span {a.addressedLoad} ≤ a.evalKernel :=
  (Ideal.span_singleton_le_iff_mem a.evalKernel).mpr
    a.addressedLoad_mem_evalKernel

/-- The addressed zeroth load is coprime to every other load in the same
scalar family.  This is inherited from pairwise coprimality of the three
normalized pair cores. -/
theorem addressedLoad_isCoprime_sameFamilyLoad
    (a : QuotientPrimeGCDLoadAddress p q)
    (i : Fin 3) (hi : i ≠ 0) :
    IsCoprime a.addressedLoad (a.family.load p i) := by
  have hcores :
      IsCoprime
        (p.signedDepth.realPairCore 0)
        (p.signedDepth.realPairCore i) :=
    p.signedDepth.realPairCores_pairwiseCoprime hi.symm
  cases hfamily : a.family with
  | cell21 =>
      simpa only [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load] using
          hcores.mono
            (p.realPairLoad21_dvd_core 0)
            (p.realPairLoad21_dvd_core i)
  | cell22 =>
      simpa only [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load] using
          hcores.mono
            (p.realPairLoad22_dvd_core 0)
            (p.realPairLoad22_dvd_core i)

/-- A prime address of the zeroth load does not kill either of the other
Galois-positioned loads in the same scalar family. -/
theorem evalAlphaRoot_sameFamilyLoad_ne_zero
    (a : QuotientPrimeGCDLoadAddress p q)
    (i : Fin 3) (hi : i ≠ 0) :
    a.evalAlphaRoot (a.family.load p i) ≠ 0 := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro hother
  rcases a.addressedLoad_isCoprime_sameFamilyLoad i hi with
    ⟨u, v, huv⟩
  have hmap := congrArg a.evalAlphaRoot huv
  rw [map_add, map_mul, map_mul,
    a.evalAlphaRoot_addressedLoad_zero, hother,
    mul_zero, mul_zero, add_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- Kernel-exclusion packet for all nonzero pair-core indices in the same
load family. -/
theorem sameFamilyLoad_not_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q)
    (i : Fin 3) (hi : i ≠ 0) :
    a.family.load p i ∉ a.evalKernel :=
  a.evalAlphaRoot_sameFamilyLoad_ne_zero i hi

/-- The index-one conjugate load is outside the zeroth address kernel. -/
theorem sameFamilyLoad_one_not_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.family.load p 1 ∉ a.evalKernel :=
  a.sameFamilyLoad_not_mem_evalKernel 1 (by decide)

/-- The index-two conjugate load is outside the zeroth address kernel. -/
theorem sameFamilyLoad_two_not_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.family.load p 2 ∉ a.evalKernel :=
  a.sameFamilyLoad_not_mem_evalKernel 2 (by decide)

/-- Neither nonzero-index load principal ideal in the selected family is
contained in the zeroth address kernel. -/
theorem span_sameFamilyLoad_not_le_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q)
    (i : Fin 3) (hi : i ≠ 0) :
    ¬ Ideal.span {a.family.load p i} ≤ a.evalKernel := by
  intro hle
  exact a.sameFamilyLoad_not_mem_evalKernel i hi
    ((Ideal.span_singleton_le_iff_mem a.evalKernel).mp hle)

/-- The selected and competing gcd loads remain coprime in the zeroth core. -/
theorem addressedLoad_isCoprime_competingLoad
    (a : QuotientPrimeGCDLoadAddress p q) :
    IsCoprime a.addressedLoad a.competingLoad := by
  cases hfamily : a.family with
  | cell21 =>
      simpa only [addressedLoad, competingLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load,
        RamifiedFusionRow2LoadFamily.otherLoad] using
          p.realPairLoads_isCoprime 0
  | cell22 =>
      simpa only [addressedLoad, competingLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load,
        RamifiedFusionRow2LoadFamily.otherLoad] using
          (p.realPairLoads_isCoprime 0).symm

/-- A proper kernel cannot contain both of two coprime elements.  Therefore
the other routing-cell load is excluded from this oriented prime address. -/
theorem evalAlphaRoot_competingLoad_ne_zero
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalAlphaRoot a.competingLoad ≠ 0 := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro hother
  rcases a.addressedLoad_isCoprime_competingLoad with
    ⟨u, v, huv⟩
  have hmap := congrArg a.evalAlphaRoot huv
  rw [map_add, map_mul, map_mul,
    a.evalAlphaRoot_addressedLoad_zero, hother,
    mul_zero, mul_zero, add_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- Kernel-exclusion form of the competing-load theorem. -/
theorem competingLoad_not_mem_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.competingLoad ∉ a.evalKernel :=
  a.evalAlphaRoot_competingLoad_ne_zero

/-- Consequently the competing-load principal ideal is not contained in the
selected prime ideal. -/
theorem span_competingLoad_not_le_evalKernel
    (a : QuotientPrimeGCDLoadAddress p q) :
    ¬ Ideal.span {a.competingLoad} ≤ a.evalKernel := by
  intro hle
  exact a.competingLoad_not_mem_evalKernel
    ((Ideal.span_singleton_le_iff_mem a.evalKernel).mp hle)

/-- The same address separates the two coprime scalar routing cells. -/
theorem evalAlphaRoot_competingScalar_ne_zero
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalAlphaRoot a.competingScalar ≠ 0 := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  have hcop :
      IsCoprime a.addressedScalar a.competingScalar := by
    cases hfamily : a.family with
    | cell21 =>
        simpa only [addressedScalar, competingScalar, hfamily,
          RamifiedFusionRow2LoadFamily.scalar,
          RamifiedFusionRow2LoadFamily.otherScalar] using
            p.row2LoadScalars_isCoprime
    | cell22 =>
        simpa only [addressedScalar, competingScalar, hfamily,
          RamifiedFusionRow2LoadFamily.scalar,
          RamifiedFusionRow2LoadFamily.otherScalar] using
            p.row2LoadScalars_isCoprime.symm
  intro hother
  rcases hcop with ⟨u, v, huv⟩
  have hmap := congrArg a.evalAlphaRoot huv
  rw [map_add, map_mul, map_mul,
    a.evalAlphaRoot_addressedScalar_zero, hother,
    mul_zero, mul_zero, add_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- The determinant norm of the addressed algebraic load is exactly the
integer routing cell from which it was projected. -/
theorem natAbs_norm_addressedLoad
    (a : QuotientPrimeGCDLoadAddress p q) :
    Int.natAbs (norm a.addressedLoad) = a.family.cell p := by
  cases hfamily : a.family with
  | cell21 =>
      simpa only [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load,
        RamifiedFusionRow2LoadFamily.cell] using
          p.natAbs_norm_realPairLoad21 0
  | cell22 =>
      simpa only [addressedLoad, hfamily,
        RamifiedFusionRow2LoadFamily.load,
        RamifiedFusionRow2LoadFamily.cell] using
          p.natAbs_norm_realPairLoad22 0

/-- The local evaluation is onto its residue field because scalar constants
already map onto `ZMod q`. -/
theorem evalAlphaRoot_surjective
    (a : QuotientPrimeGCDLoadAddress p q) :
    Function.Surjective a.evalAlphaRoot := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro z
  refine ⟨(z.val : SevenRealCubicInt), ?_⟩
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- The explicit evaluation kernel is a maximal, hence prime, ideal above
the addressed rational prime. -/
theorem evalKernel_isMaximal
    (a : QuotientPrimeGCDLoadAddress p q) :
    a.evalKernel.IsMaximal := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    a.evalAlphaRoot a.evalAlphaRoot_surjective

/-- The contraction of the explicit real-cubic kernel to the integers is
exactly the rational prime ideal `(q)`. -/
theorem evalKernel_comap_intCast
    (a : QuotientPrimeGCDLoadAddress p q) :
    Ideal.comap (Int.castRingHom SevenRealCubicInt) a.evalKernel =
      Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change a.evalAlphaRoot (z : SevenRealCubicInt) = 0 ↔ (q : ℤ) ∣ z
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The residue degree of the selected prime ideal is one: its quotient has
exactly `q` elements. -/
theorem evalKernel_cardQuot
    (a : QuotientPrimeGCDLoadAddress p q) :
    Submodule.cardQuot a.evalKernel = q := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card (SevenRealCubicInt ⧸ a.evalKernel) =
        Nat.card (ZMod q) :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective
          a.evalAlphaRoot_surjective).toEquiv
    _ = q := Nat.card_zmod q

end QuotientPrimeGCDLoadAddress

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven
