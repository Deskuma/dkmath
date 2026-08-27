/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadValuation
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGalois

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadExactValuation"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

open SevenRealCubicInt
open UniqueFactorizationMonoid

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- Every member of the addressed three-load Galois orbit is nonzero. -/
private theorem familyLoad_ne_zero
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    a.family.load p i ≠ 0 := by
  intro hzero
  have hnorm :
      Int.natAbs (norm (a.family.load p i)) =
        a.family.cell p := by
    cases hfamily : a.family with
    | cell21 =>
        simpa only [hfamily,
          RamifiedFusionRow2LoadFamily.load,
          RamifiedFusionRow2LoadFamily.cell] using
            p.natAbs_norm_realPairLoad21 i
    | cell22 =>
        simpa only [hfamily,
          RamifiedFusionRow2LoadFamily.load,
          RamifiedFusionRow2LoadFamily.cell] using
            p.natAbs_norm_realPairLoad22 i
  rw [hzero] at hnorm
  norm_num [SevenRealCubicInt.norm] at hnorm
  exact a.addressedCell_ne_zero hnorm.symm

/-- None of the three degree-one Galois kernels is the zero ideal. -/
private theorem galoisKernel_ne_bot
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    a.galoisKernel i ≠ (⊥ : Ideal SevenRealCubicInt) := by
  intro hzero
  have hmem := a.ownLoad_mem_galoisKernel i
  rw [hzero, Ideal.mem_bot] at hmem
  exact a.familyLoad_ne_zero i hmem

/-- Each Galois kernel is a prime element of the ideal monoid. -/
private theorem galoisKernel_prime
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Prime (a.galoisKernel i) :=
  Ideal.prime_of_isPrime
    (a.galoisKernel_ne_bot i)
    (a.galoisKernel_isMaximal i).isPrime

private theorem mk_galoisKernel_ne_zero
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Associates.mk (a.galoisKernel i) ≠ 0 :=
  Associates.mk_ne_zero.mpr (a.galoisKernel_ne_bot i)

private theorem mk_galoisKernel_irreducible
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Irreducible (Associates.mk (a.galoisKernel i)) :=
  Associates.irreducible_mk.mpr
    (a.galoisKernel_prime i).irreducible

private theorem mk_galoisKernel_ne
    (a : p.QuotientPrimeGCDLoadAddress q)
    {i j : Fin 3} (hij : i ≠ j) :
    Associates.mk (a.galoisKernel i) ≠
      Associates.mk (a.galoisKernel j) := by
  rw [Ne, Associates.mk_eq_mk_iff_associated,
    associated_iff_eq]
  exact a.galoisKernels_pairwise_ne hij

/-- Complete splitting makes the canonical kernel occur exactly once in
the rational-prime principal ideal `(q)`. -/
theorem evalKernel_count_span_prime_eq_one
    (a : p.QuotientPrimeGCDLoadAddress q) :
    (Associates.mk a.evalKernel).count
        (Associates.mk
          (Ideal.span
            ({(q : SevenRealCubicInt)} :
              Set SevenRealCubicInt))).factors =
      1 := by
  rw [← a.galoisKernel_product_eq_span_prime,
    ← Associates.mk_mul_mk, ← Associates.mk_mul_mk]
  have h0 := a.mk_galoisKernel_ne_zero 0
  have h1 := a.mk_galoisKernel_ne_zero 1
  have h2 := a.mk_galoisKernel_ne_zero 2
  have hirr0 := a.mk_galoisKernel_irreducible 0
  have hirr1 := a.mk_galoisKernel_irreducible 1
  have hirr2 := a.mk_galoisKernel_irreducible 2
  have h0' : Associates.mk a.evalKernel ≠ 0 := by
    simpa only [a.galoisKernel_zero] using h0
  have hirr0' : Irreducible (Associates.mk a.evalKernel) := by
    simpa only [a.galoisKernel_zero] using hirr0
  rw [a.galoisKernel_zero]
  rw [Associates.count_mul (mul_ne_zero h0' h1) h2 hirr0',
    Associates.count_mul h0' h1 hirr0',
    Associates.count_self hirr0',
    Associates.count_eq_zero_of_ne hirr0' hirr1
      (by
        simpa only [a.galoisKernel_zero] using
          a.mk_galoisKernel_ne (show (0 : Fin 3) ≠ 1 by decide)),
    Associates.count_eq_zero_of_ne hirr0' hirr2
      (by
        simpa only [a.galoisKernel_zero] using
          a.mk_galoisKernel_ne (show (0 : Fin 3) ≠ 2 by decide))]

/-- The selected scalar is literally the selected natural routing cell
embedded in the real cubic order. -/
private theorem addressedScalar_eq_natCast
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.addressedScalar =
      (a.family.cell p : SevenRealCubicInt) := by
  cases hfamily : a.family with
  | cell21 =>
      simp only [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar,
        RamifiedFusionRow2LoadFamily.cell,
        RamifiedSignedRootRoutingPacket.row2Load21Scalar]
  | cell22 =>
      simp only [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar,
        RamifiedFusionRow2LoadFamily.cell,
        RamifiedSignedRootRoutingPacket.row2Load22Scalar]

/-- The three same-family loads allocate the selected scalar cell up to
the harmless gcd normalization unit. -/
private theorem load_product_associated_addressedScalar
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Associated
      (a.family.load p 0 * a.family.load p 1 *
        a.family.load p 2)
      a.addressedScalar := by
  cases hfamily : a.family with
  | cell21 =>
      simpa only [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar,
        RamifiedFusionRow2LoadFamily.load] using
          p.realPairLoad21_product_associated
  | cell22 =>
      simpa only [addressedScalar, hfamily,
        RamifiedFusionRow2LoadFamily.scalar,
        RamifiedFusionRow2LoadFamily.load] using
          p.realPairLoad22_product_associated

/-- Principal-ideal form of the exact three-load scalar allocation. -/
private theorem span_addressedCell_eq_loadIdeal_product
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Ideal.span
        ({(a.family.cell p : SevenRealCubicInt)} :
          Set SevenRealCubicInt) =
      Ideal.span {a.family.load p 0} *
        Ideal.span {a.family.load p 1} *
          Ideal.span {a.family.load p 2} := by
  calc
    Ideal.span
          ({(a.family.cell p : SevenRealCubicInt)} :
            Set SevenRealCubicInt) =
        Ideal.span {a.addressedScalar} := by
      rw [a.addressedScalar_eq_natCast]
    _ =
        Ideal.span
          {a.family.load p 0 * a.family.load p 1 *
            a.family.load p 2} :=
      (Ideal.span_singleton_eq_span_singleton.mpr
        a.load_product_associated_addressedScalar).symm
    _ =
        Ideal.span {a.family.load p 0} *
          Ideal.span {a.family.load p 1} *
            Ideal.span {a.family.load p 2} := by
      rw [Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton]

private theorem span_familyLoad_ne_bot
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Ideal.span {a.family.load p i} ≠
      (⊥ : Ideal SevenRealCubicInt) := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
    a.familyLoad_ne_zero i

/-- The zeroth prime-kernel factor count in either other Galois load is
zero. -/
private theorem evalKernel_count_otherLoad_eq_zero
    (a : p.QuotientPrimeGCDLoadAddress q)
    (j : Fin 3) (hj : (0 : Fin 3) ≠ j) :
    (Associates.mk a.evalKernel).count
        (Associates.mk
          (Ideal.span {a.family.load p j})).factors =
      0 := by
  by_contra hcount
  have hdvd :
      a.evalKernel ∣
        Ideal.span {a.family.load p j} :=
    (Associates.count_ne_zero_iff_dvd
      (a.span_familyLoad_ne_bot j)
      (by
        simpa only [a.galoisKernel_zero] using
          (a.galoisKernel_prime 0).irreducible)).mp hcount
  have hmem :
      a.family.load p j ∈ a.evalKernel :=
    Ideal.dvd_span_singleton.mp hdvd
  have hnot :
      a.family.load p j ∉ a.evalKernel := by
    simpa only [a.galoisKernel_zero] using
      a.otherLoad_not_mem_galoisKernel 0 j hj
  exact hnot hmem

/-- All of the zeroth kernel multiplicity in the scalar cell is allocated
to load zero; the other two Galois loads contribute zero. -/
theorem evalKernel_count_span_addressedCell_eq_multiplicity
    (a : p.QuotientPrimeGCDLoadAddress q) :
    (Associates.mk a.evalKernel).count
        (Associates.mk
          (Ideal.span
            ({(a.family.cell p : SevenRealCubicInt)} :
              Set SevenRealCubicInt))).factors =
      a.evalKernelMultiplicity := by
  rw [a.span_addressedCell_eq_loadIdeal_product,
    ← Associates.mk_mul_mk, ← Associates.mk_mul_mk]
  have h0 :
      Associates.mk
          (Ideal.span {a.family.load p 0}) ≠ 0 :=
    Associates.mk_ne_zero.mpr
      (a.span_familyLoad_ne_bot 0)
  have h1 :
      Associates.mk
          (Ideal.span {a.family.load p 1}) ≠ 0 :=
    Associates.mk_ne_zero.mpr
      (a.span_familyLoad_ne_bot 1)
  have h2 :
      Associates.mk
          (Ideal.span {a.family.load p 2}) ≠ 0 :=
    Associates.mk_ne_zero.mpr
      (a.span_familyLoad_ne_bot 2)
  have hirr :
      Irreducible (Associates.mk a.evalKernel) := by
    simpa only [a.galoisKernel_zero] using
      a.mk_galoisKernel_irreducible 0
  rw [Associates.count_mul (mul_ne_zero h0 h1) h2 hirr,
    Associates.count_mul h0 h1 hirr,
    a.evalKernel_count_otherLoad_eq_zero 1 (by decide),
    a.evalKernel_count_otherLoad_eq_zero 2 (by decide),
    add_zero, add_zero]
  rfl

/-- The complete three-prime splitting lifts the full rational `q`-adic
power of the integer cell into the zeroth Galois kernel power. -/
private theorem evalKernel_pow_padicValNat_dvd_span_addressedCell
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.evalKernel ^ padicValNat q (a.family.cell p) ∣
      Ideal.span
        ({(a.family.cell p : SevenRealCubicInt)} :
          Set SevenRealCubicInt) := by
  let v := padicValNat q (a.family.cell p)
  have hPq :
      a.evalKernel ∣
        Ideal.span
          ({(q : SevenRealCubicInt)} :
            Set SevenRealCubicInt) := by
    refine
      ⟨a.galoisKernel 1 * a.galoisKernel 2, ?_⟩
    simpa only [a.galoisKernel_zero, mul_assoc] using
      a.galoisKernel_product_eq_span_prime.symm
  have hPpow :
      a.evalKernel ^ v ∣
        (Ideal.span
          ({(q : SevenRealCubicInt)} :
            Set SevenRealCubicInt)) ^ v :=
    pow_dvd_pow_of_dvd hPq v
  have hPpow' :
      a.evalKernel ^ v ∣
        Ideal.span
          ({((q : SevenRealCubicInt) ^ v)} :
            Set SevenRealCubicInt) := by
    simpa only [Ideal.span_singleton_pow] using hPpow
  have hnat :
      q ^ v ∣ a.family.cell p := by
    exact pow_padicValNat_dvd
  have hcast :
      (q : SevenRealCubicInt) ^ v ∣
        (a.family.cell p : SevenRealCubicInt) := by
    rcases hnat with ⟨m, hm⟩
    refine ⟨(m : SevenRealCubicInt), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg
        (fun n : ℕ => (n : SevenRealCubicInt)) hm
  exact hPpow'.trans
    (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
      hcast)

/-- Lower bound complementary to the norm-derived upper bound: complete
splitting and load allocation force the entire integer `q`-adic exponent
into the addressed load. -/
theorem padicValNat_addressedCell_le_evalKernelMultiplicity
    (a : p.QuotientPrimeGCDLoadAddress q) :
    padicValNat q (a.family.cell p) ≤
      a.evalKernelMultiplicity := by
  have hspan0 :
      Ideal.span
          ({(a.family.cell p : SevenRealCubicInt)} :
            Set SevenRealCubicInt) ≠
        (⊥ : Ideal SevenRealCubicInt) := by
    intro hbot
    have hcast :
        (a.family.cell p : SevenRealCubicInt) = 0 :=
      Ideal.span_singleton_eq_bot.mp hbot
    have hfst := congrArg SevenRealCubicInt.fst hcast
    apply a.addressedCell_ne_zero
    simpa only [SevenRealCubicInt.fst_natCast,
      SevenRealCubicInt.fst_zero, Int.ofNat_eq_zero] using hfst
  have hirr :
      Irreducible (Associates.mk a.evalKernel) := by
    simpa only [a.galoisKernel_zero] using
      a.mk_galoisKernel_irreducible 0
  have hle :
      padicValNat q (a.family.cell p) ≤
        (Associates.mk a.evalKernel).count
          (Associates.mk
            (Ideal.span
              ({(a.family.cell p : SevenRealCubicInt)} :
                Set SevenRealCubicInt))).factors := by
    apply
      (Associates.prime_pow_dvd_iff_le
        (Associates.mk_ne_zero.mpr hspan0) hirr).mp
    rw [← Associates.mk_pow,
      Associates.mk_le_mk_iff_dvd]
    exact a.evalKernel_pow_padicValNat_dvd_span_addressedCell
  rwa [a.evalKernel_count_span_addressedCell_eq_multiplicity] at hle

/-- Exact valuation theorem for the addressed load: its explicit degree-one
kernel multiplicity is exactly the ordinary `q`-adic exponent of the routed
integer cell. -/
theorem evalKernelMultiplicity_eq_padicValNat_addressedCell
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.evalKernelMultiplicity =
      padicValNat q (a.family.cell p) :=
  Nat.le_antisymm
    a.evalKernelMultiplicity_le_padicValNat_addressedCell
    a.padicValNat_addressedCell_le_evalKernelMultiplicity

/-- Prime-power divisibility of the addressed-load ideal is now expressed
entirely in terms of the ordinary routed-cell valuation. -/
theorem evalKernel_pow_dvd_span_addressedLoad_iff_padicValNat
    (a : p.QuotientPrimeGCDLoadAddress q)
    (k : ℕ) :
    a.evalKernel ^ k ∣ Ideal.span {a.addressedLoad} ↔
      k ≤ padicValNat q (a.family.cell p) := by
  rw [a.evalKernel_pow_dvd_span_addressedLoad_iff,
    a.evalKernelMultiplicity_eq_padicValNat_addressedCell]

/-- Element-membership version of the exact addressed-load valuation. -/
theorem addressedLoad_mem_evalKernel_pow_iff_padicValNat
    (a : p.QuotientPrimeGCDLoadAddress q)
    (k : ℕ) :
    a.addressedLoad ∈ a.evalKernel ^ k ↔
      k ≤ padicValNat q (a.family.cell p) := by
  rw [a.addressedLoad_mem_evalKernel_pow_iff,
    a.evalKernelMultiplicity_eq_padicValNat_addressedCell]

/-- The exact routed-cell valuation is the largest explicit-kernel power
containing the addressed algebraic load. -/
theorem addressedLoad_not_mem_evalKernel_pow_padicValNat_succ
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.addressedLoad ∉
      a.evalKernel ^
        (padicValNat q (a.family.cell p) + 1) := by
  rw [a.addressedLoad_mem_evalKernel_pow_iff_padicValNat]
  omega

end RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

end

end DkMath.FLT.Seven
