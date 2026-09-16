/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionOrientedCarrierValuationOwnership"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedFusionRow2LoadFamily

open SevenCyclotomicDegreeSixInt
open Module

private def carrierOwnershipCoordinateAddEquiv :
    SevenRealCubicInt ≃+ (Fin 3 → ℤ) where
  toFun x i :=
    if i = 0 then x.fst else
    if i = 1 then x.snd else x.thd
  invFun f := ⟨f 0, f 1, f 2⟩
  left_inv x := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp

private def carrierOwnershipCoordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun carrierOwnershipCoordinateAddEquiv.toIntLinearEquiv

local instance carrierOwnershipModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis carrierOwnershipCoordinateBasis

local instance carrierOwnershipModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis carrierOwnershipCoordinateBasis

private theorem carrierOwnershipAlgebraNorm_eq_norm
    (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = SevenRealCubicInt.norm x := by
  rw [Algebra.norm_eq_matrix_det carrierOwnershipCoordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    carrierOwnershipCoordinateBasis,
    carrierOwnershipCoordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

variable (family : RamifiedFusionRow2LoadFamily)
  (p : RamifiedSignedRootRoutingPacket)

namespace PrimeSupport

variable {family : RamifiedFusionRow2LoadFamily}
  {p : RamifiedSignedRootRoutingPacket}

private theorem load_dvd_realPairCore_zero
    (s : PrimeSupport family p) :
    family.load p 0 ∣ p.signedDepth.realPairCore 0 := by
  cases family with
  | cell21 =>
      exact p.realPairLoad21_dvd_core 0
  | cell22 =>
      exact p.realPairLoad22_dvd_core 0

private theorem span_ofReal_load_dvd_span_carrierProduct
    (s : PrimeSupport family p) :
    Ideal.span {ofReal (family.load p 0)} ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier *
          p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  rcases s.load_dvd_realPairCore_zero with ⟨c, hc⟩
  let d : SevenCyclotomicDegreeSixInt.Ring :=
    ofReal (SevenRealCubicInt.eisensteinAxis * c)
  refine ⟨Ideal.span {d}, ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 2
  rw [p.signedDepth.cyclotomicDegreeSixCarrier_mul_conj,
    p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core,
    hc, map_mul, map_mul]
  simp only [d, map_mul]
  ring

private theorem orientedPairPower_dvd_span_carrierProduct
    (s : PrimeSupport family p) :
    s.orientedPairPower ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier *
          p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  have hmap :=
    map_dvd (Ideal.mapHom ofReal)
      s.kernelPower_dvd_span_load
  change
    Ideal.map ofReal s.kernelPower ∣
      Ideal.map ofReal
        (Ideal.span {family.load p 0}) at hmap
  rw [s.map_kernelPower_eq_orientedPairPower,
    Ideal.map_span] at hmap
  have hmap' :
      s.orientedPairPower ∣
        Ideal.span {ofReal (family.load p 0)} := by
    simpa only [Set.image_singleton] using hmap
  exact hmap'.trans s.span_ofReal_load_dvd_span_carrierProduct

private theorem evalKernel_isCoprime_span_conjugateCarrier
    (s : PrimeSupport family p) :
    IsCoprime s.cyclotomicAddress.evalKernel
      (Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.cyclotomicAddress.evalKernel =
        s.cyclotomicAddress.evalKernel ⊔
          Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrierConj} :=
    s.cyclotomicAddress.evalKernel_isMaximal.eq_of_le
      hne le_sup_left
  have hmem :
      p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.cyclotomicAddress.evalKernel := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  exact
    s.cyclotomicAddress.cyclotomicDegreeSixCarrierConj_not_mem_evalKernel
      hmem

private theorem conjugateEvalKernel_isCoprime_span_carrier
    (s : PrimeSupport family p) :
    IsCoprime s.cyclotomicAddress.conjugateEvalKernel
      (Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.cyclotomicAddress.conjugateEvalKernel =
        s.cyclotomicAddress.conjugateEvalKernel ⊔
          Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrier} :=
    s.cyclotomicAddress.conjugateEvalKernel_isMaximal.eq_of_le
      hne le_sup_left
  have hmem :
      p.signedDepth.cyclotomicDegreeSixCarrier ∈
        s.cyclotomicAddress.conjugateEvalKernel := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  exact
    s.cyclotomicAddress.carrier_not_mem_conjugateEvalKernel hmem

/-- The entire routed-cell exponent owned by one real load is assigned to
the oriented linear carrier, not merely to the unordered conjugate pair.

This is an ideal-divisibility statement in the concrete commutative
quadratic carrier.  It uses no domain or unique-factorization instance for
that carrier. -/
theorem orientedKernelPower_dvd_span_carrier
    (s : PrimeSupport family p) :
    s.orientedKernelPower ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} := by
  have hpow :
      IsCoprime s.orientedKernelPower
        (Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj}) := by
    exact s.evalKernel_isCoprime_span_conjugateCarrier.pow_left
  apply hpow.dvd_of_dvd_mul_right
  rw [Ideal.span_singleton_mul_span_singleton]
  exact
    (show s.orientedKernelPower ∣ s.orientedPairPower by
      refine ⟨s.conjugateKernelPower, ?_⟩
      rfl).trans
      s.orientedPairPower_dvd_span_carrierProduct

/-- The conjugate load power is assigned to the conjugate linear carrier. -/
theorem conjugateKernelPower_dvd_span_conjugateCarrier
    (s : PrimeSupport family p) :
    s.conjugateKernelPower ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  have hpow :
      IsCoprime s.conjugateKernelPower
        (Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier}) := by
    exact s.conjugateEvalKernel_isCoprime_span_carrier.pow_left
  apply hpow.dvd_of_dvd_mul_right
  rw [Ideal.span_singleton_mul_span_singleton, mul_comm]
  exact
    (show s.conjugateKernelPower ∣ s.orientedPairPower by
      refine ⟨s.orientedKernelPower, ?_⟩
      rw [mul_comm]
      rfl).trans
      s.orientedPairPower_dvd_span_carrierProduct

/-- Element-membership form of the exact routed-load lower bound. -/
theorem carrier_mem_orientedKernelPower
    (s : PrimeSupport family p) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∈
      s.orientedKernelPower := by
  rcases s.orientedKernelPower_dvd_span_carrier with
    ⟨J, hJ⟩
  apply
    (Ideal.span_singleton_le_iff_mem
      s.orientedKernelPower).mp
  rw [hJ]
  change s.orientedKernelPower * J ≤ s.orientedKernelPower
  exact Ideal.mul_le_left

/-- Conjugate element-membership form of the routed-load lower bound. -/
theorem conjugateCarrier_mem_conjugateKernelPower
    (s : PrimeSupport family p) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
      s.conjugateKernelPower := by
  rcases s.conjugateKernelPower_dvd_span_conjugateCarrier with
    ⟨J, hJ⟩
  apply
    (Ideal.span_singleton_le_iff_mem
      s.conjugateKernelPower).mp
  rw [hJ]
  change s.conjugateKernelPower * J ≤ s.conjugateKernelPower
  exact Ideal.mul_le_left

end PrimeSupport

end RamifiedFusionRow2LoadFamily

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt

/-- The full finite support of rational primes in the signed quotient root.

Unlike the two row-cell supports used by the NORMAL launchpad, this support
also includes primes contributed only by the residual seventh-power
coordinate.  The ramified prime seven is absent automatically because the
quotient root is one modulo seven. -/
def QuotientPrimeSupport (p : RamifiedSignedRootRoutingPacket) :=
  {q : ℕ //
    q ∈ (Int.natAbs p.signedDepth.quotientRoot).primeFactors}

instance quotientPrimeSupportFintype
    (p : RamifiedSignedRootRoutingPacket) :
    Fintype p.QuotientPrimeSupport :=
  Finset.fintypeCoeSort _

namespace QuotientPrimeSupport

variable {p : RamifiedSignedRootRoutingPacket}

set_option maxRecDepth 4000

local instance quotientSupportModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis
    RamifiedFusionRow2LoadFamily.carrierOwnershipCoordinateBasis

local instance quotientSupportModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis
    RamifiedFusionRow2LoadFamily.carrierOwnershipCoordinateBasis

theorem prime (s : p.QuotientPrimeSupport) :
    Nat.Prime s.1 :=
  Nat.prime_of_mem_primeFactors s.2

theorem dividesNatAbs (s : p.QuotientPrimeSupport) :
    s.1 ∣ Int.natAbs p.signedDepth.quotientRoot :=
  Nat.dvd_of_mem_primeFactors s.2

theorem dividesQuotientRoot (s : p.QuotientPrimeSupport) :
    (s.1 : ℤ) ∣ p.signedDepth.quotientRoot :=
  Int.natCast_dvd.mpr s.dividesNatAbs

theorem ne_seven (s : p.QuotientPrimeSupport) :
    s.1 ≠ 7 :=
  p.signedDepth.quotientPrime_ne_seven
    s.prime s.dividesQuotientRoot

/-- The canonical primitive-seventh-root address at a full-support prime. -/
def muSevenAddress (s : p.QuotientPrimeSupport) :
    p.signedDepth.QuotientPrimeMuSevenAddress s.1 where
  prime := s.prime
  dividesQuotientRoot := s.dividesQuotientRoot

/-- The three real-cubic evaluations above a full-support rational prime. -/
def realEval
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    SevenRealCubicInt →+* ZMod s.1 :=
  if i = 0 then
    s.muSevenAddress.evalAlphaRoot
  else if i = 1 then
    s.muSevenAddress.evalAlphaRoot.comp
      SevenRealCubicInt.rotateEquiv.symm.toRingHom
  else
    s.muSevenAddress.evalAlphaRoot.comp
      SevenRealCubicInt.rotateEquiv.toRingHom

/-- The three real-cubic degree-one kernels above a full-support prime. -/
def realKernel
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    Ideal SevenRealCubicInt :=
  RingHom.ker (s.realEval i)

@[simp] theorem realEval_zero
    (s : p.QuotientPrimeSupport) :
    s.realEval 0 = s.muSevenAddress.evalAlphaRoot := by
  simp [realEval]

@[simp] theorem realEval_one
    (s : p.QuotientPrimeSupport) :
    s.realEval 1 =
      s.muSevenAddress.evalAlphaRoot.comp
        SevenRealCubicInt.rotateEquiv.symm.toRingHom := by
  simp [realEval]

@[simp] theorem realEval_two
    (s : p.QuotientPrimeSupport) :
    s.realEval 2 =
      s.muSevenAddress.evalAlphaRoot.comp
        SevenRealCubicInt.rotateEquiv.toRingHom := by
  simp [realEval]

private theorem map_eq_zero_of_dvd
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x y : R}
    (hx : f x = 0) (hxy : x ∣ y) :
    f y = 0 := by
  rcases hxy with ⟨c, rfl⟩
  rw [map_mul, hx, zero_mul]

/-- Each transported evaluation kills the pair core in the matching real
Galois phase. -/
theorem realEval_ownCore_zero
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    s.realEval i (p.signedDepth.realPairCore i) = 0 := by
  fin_cases i
  · exact s.muSevenAddress.evalAlphaRoot_realPairCore_zero
  · change
      s.muSevenAddress.evalAlphaRoot
        (SevenRealCubicInt.rotateEquiv.symm
          (p.signedDepth.realPairCore 1)) = 0
    have hdiv :
        p.signedDepth.realPairCore 0 ∣
          SevenRealCubicInt.rotateEquiv.symm
            (p.signedDepth.realPairCore 1) := by
      have hmap :=
        map_dvd SevenRealCubicInt.rotateEquiv.symm.toRingHom
          p.signedDepth.rotate_realPairCore_zero_associated_one.dvd
      change
        SevenRealCubicInt.rotateEquiv.symm
            (SevenRealCubicInt.rotateEquiv
              (p.signedDepth.realPairCore 0)) ∣
          SevenRealCubicInt.rotateEquiv.symm
            (p.signedDepth.realPairCore 1) at hmap
      rw [RingEquiv.symm_apply_apply] at hmap
      exact hmap
    exact map_eq_zero_of_dvd
      s.muSevenAddress.evalAlphaRoot
      s.muSevenAddress.evalAlphaRoot_realPairCore_zero hdiv
  · change
      s.muSevenAddress.evalAlphaRoot
        (SevenRealCubicInt.rotateEquiv
          (p.signedDepth.realPairCore 2)) = 0
    exact map_eq_zero_of_dvd
      s.muSevenAddress.evalAlphaRoot
      s.muSevenAddress.evalAlphaRoot_realPairCore_zero
      p.signedDepth.rotate_realPairCore_two_associated_zero.symm.dvd

theorem ownCore_mem_realKernel
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    p.signedDepth.realPairCore i ∈ s.realKernel i :=
  s.realEval_ownCore_zero i

/-- The other two pair cores are excluded from each transported kernel. -/
theorem otherCore_not_mem_realKernel
    (s : p.QuotientPrimeSupport)
    (i j : Fin 3) (hij : i ≠ j) :
    p.signedDepth.realPairCore j ∉ s.realKernel i := by
  let : Fact (Nat.Prime s.1) := ⟨s.prime⟩
  intro hother
  rcases
      p.signedDepth.realPairCores_pairwiseCoprime hij with
    ⟨u, v, huv⟩
  have hmap := congrArg (s.realEval i) huv
  change
    s.realEval i (p.signedDepth.realPairCore j) = 0 at hother
  rw [map_add, map_mul, map_mul,
    s.realEval_ownCore_zero i, hother,
    mul_zero, mul_zero, add_zero, map_one] at hmap
  exact zero_ne_one hmap

theorem realKernels_pairwise_ne
    (s : p.QuotientPrimeSupport) :
    Pairwise
      (fun i j : Fin 3 =>
        s.realKernel i ≠ s.realKernel j) := by
  intro i j hij heq
  exact s.otherCore_not_mem_realKernel j i hij.symm
    (heq ▸ s.ownCore_mem_realKernel i)

theorem realEval_surjective
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    Function.Surjective (s.realEval i) := by
  let : Fact (Nat.Prime s.1) := ⟨s.prime⟩
  fin_cases i
  · change
      Function.Surjective
        s.muSevenAddress.evalAlphaRoot
    intro z
    refine ⟨(z.val : SevenRealCubicInt), ?_⟩
    simpa only [map_natCast] using
      ZMod.natCast_zmod_val z
  · intro z
    rcases s.realEval_surjective 0 z with ⟨x, hx⟩
    refine ⟨SevenRealCubicInt.rotateEquiv x, ?_⟩
    change
      s.muSevenAddress.evalAlphaRoot
        (SevenRealCubicInt.rotateEquiv.symm
          (SevenRealCubicInt.rotateEquiv x)) = z
    rw [RingEquiv.symm_apply_apply]
    exact hx
  · intro z
    rcases s.realEval_surjective 0 z with ⟨x, hx⟩
    refine ⟨SevenRealCubicInt.rotateEquiv.symm x, ?_⟩
    change
      s.muSevenAddress.evalAlphaRoot
        (SevenRealCubicInt.rotateEquiv
          (SevenRealCubicInt.rotateEquiv.symm x)) = z
    rw [RingEquiv.apply_symm_apply]
    exact hx

theorem realKernel_isMaximal
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    (s.realKernel i).IsMaximal := by
  let : Fact (Nat.Prime s.1) := ⟨s.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    (s.realEval i) (s.realEval_surjective i)

theorem realKernel_cardQuot
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    Submodule.cardQuot (s.realKernel i) = s.1 := by
  let : Fact (Nat.Prime s.1) := ⟨s.prime⟩
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card (SevenRealCubicInt ⧸ s.realKernel i) =
        Nat.card (ZMod s.1) :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective
          (s.realEval_surjective i)).toEquiv
    _ = s.1 := Nat.card_zmod s.1

theorem absNorm_realKernel
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    Ideal.absNorm (s.realKernel i) = s.1 := by
  rw [Ideal.absNorm_apply]
  exact s.realKernel_cardQuot i

theorem realKernels_pairwise_isCoprime
    (s : p.QuotientPrimeSupport) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (s.realKernel i) (s.realKernel j)) := by
  intro i j hij
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      (s.realKernel_isMaximal i)
      (s.realKernel_isMaximal j)
      (s.realKernels_pairwise_ne hij))

theorem span_prime_le_realKernel
    (s : p.QuotientPrimeSupport) (i : Fin 3) :
    Ideal.span
        ({(s.1 : SevenRealCubicInt)} :
          Set SevenRealCubicInt) ≤
      s.realKernel i := by
  rw [Ideal.span_singleton_le_iff_mem]
  change s.realEval i (s.1 : SevenRealCubicInt) = 0
  simpa only [map_natCast] using ZMod.natCast_self s.1

private theorem realKernel_product_eq_inf
    (s : p.QuotientPrimeSupport) :
    s.realKernel 0 * s.realKernel 1 * s.realKernel 2 =
      (s.realKernel 0 ⊓ s.realKernel 1) ⊓
        s.realKernel 2 := by
  have h01 :=
    s.realKernels_pairwise_isCoprime
      (show (0 : Fin 3) ≠ 1 by decide)
  have h02 :=
    s.realKernels_pairwise_isCoprime
      (show (0 : Fin 3) ≠ 2 by decide)
  have h12 :=
    s.realKernels_pairwise_isCoprime
      (show (1 : Fin 3) ≠ 2 by decide)
  calc
    s.realKernel 0 * s.realKernel 1 * s.realKernel 2 =
        (s.realKernel 0 * s.realKernel 1) ⊓
          s.realKernel 2 :=
      Ideal.mul_eq_inf_of_isCoprime
        (h02.mul_left h12)
    _ =
        (s.realKernel 0 ⊓ s.realKernel 1) ⊓
          s.realKernel 2 := by
      rw [Ideal.mul_eq_inf_of_isCoprime h01]

private theorem absNorm_realKernel_product
    (s : p.QuotientPrimeSupport) :
    Ideal.absNorm
        (s.realKernel 0 * s.realKernel 1 *
          s.realKernel 2) =
      s.1 ^ 3 := by
  rw [map_mul, map_mul, s.absNorm_realKernel,
    s.absNorm_realKernel, s.absNorm_realKernel]
  ring

/-- Every full-support quotient prime splits completely into the three
explicit real degree-one kernels. -/
theorem realKernel_product_eq_span_prime
    (s : p.QuotientPrimeSupport) :
    s.realKernel 0 * s.realKernel 1 * s.realKernel 2 =
      Ideal.span
        ({(s.1 : SevenRealCubicInt)} :
          Set SevenRealCubicInt) := by
  let P : Ideal SevenRealCubicInt :=
    s.realKernel 0 * s.realKernel 1 * s.realKernel 2
  let Q : Ideal SevenRealCubicInt :=
    Ideal.span
      ({(s.1 : SevenRealCubicInt)} :
        Set SevenRealCubicInt)
  have hQP : Q ≤ P := by
    dsimp only [P, Q]
    rw [s.realKernel_product_eq_inf]
    exact le_inf
      (le_inf
        (s.span_prime_le_realKernel 0)
        (s.span_prime_le_realKernel 1))
      (s.span_prime_le_realKernel 2)
  have hdiv : P ∣ Q :=
    Ideal.dvd_iff_le.mpr hQP
  rcases hdiv with ⟨J, hJ⟩
  have hnormJ : Ideal.absNorm J = 1 := by
    have hnorm := congrArg Ideal.absNorm hJ
    rw [map_mul] at hnorm
    have hnormP : Ideal.absNorm P = s.1 ^ 3 := by
      simpa only [P] using s.absNorm_realKernel_product
    have hnormQ : Ideal.absNorm Q = s.1 ^ 3 := by
      simpa only [Q] using
        QuotientPrimeGCDLoadAddress.absNorm_span_natCast s.1
    rw [hnormQ, hnormP] at hnorm
    exact Nat.eq_of_mul_eq_mul_left
      (pow_pos s.prime.pos 3)
      (by simpa only [mul_one] using hnorm.symm)
  have hJtop : J = ⊤ :=
    Ideal.absNorm_eq_one_iff.mp hnormJ
  rw [hJtop, Ideal.mul_top] at hJ
  simpa only [P, Q] using hJ.symm

/-- The complete quotient-root exponent at one full-support prime. -/
def quotientExponent (s : p.QuotientPrimeSupport) : ℕ :=
  padicValNat s.1
    (Int.natAbs p.signedDepth.quotientRoot)

private theorem quotientRoot_ne_zero :
    p.signedDepth.quotientRoot ≠ 0 := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hzero
  have hmod := p.signedDepth.quotientRoot_modSeven_eq_one
  rw [hzero] at hmod
  exact zero_ne_one hmod

private theorem quotientRoot_natAbs_ne_zero :
    Int.natAbs p.signedDepth.quotientRoot ≠ 0 :=
  Int.natAbs_ne_zero.mpr quotientRoot_ne_zero

private theorem realPairCore_zero_ne_zero :
    p.signedDepth.realPairCore 0 ≠ 0 := by
  intro hzero
  have hnorm := p.signedDepth.norm_realPairCore 0
  rw [hzero] at hnorm
  have hquotient :
      p.signedDepth.quotientRoot = 0 := by
    have :
        -p.signedDepth.quotientRoot = 0 := by
      rw [← hnorm]
      rfl
    exact neg_eq_zero.mp this
  exact quotientRoot_ne_zero hquotient

private theorem absNorm_span_realPairCore_zero :
    Ideal.absNorm
        (Ideal.span {p.signedDepth.realPairCore 0}) =
      Int.natAbs p.signedDepth.quotientRoot := by
  rw [Ideal.absNorm_span_singleton,
    RamifiedFusionRow2LoadFamily.carrierOwnershipAlgebraNorm_eq_norm,
    p.signedDepth.norm_realPairCore,
    Int.natAbs_neg]

private theorem realKernel_zero_isCoprime_span_otherCore
    (s : p.QuotientPrimeSupport)
    (i : Fin 3) (hi : i ≠ 0) :
    IsCoprime (s.realKernel 0)
      (Ideal.span {p.signedDepth.realPairCore i}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.realKernel 0 =
        s.realKernel 0 ⊔
          Ideal.span {p.signedDepth.realPairCore i} :=
    (s.realKernel_isMaximal 0).eq_of_le
      hne le_sup_left
  have hmem :
      p.signedDepth.realPairCore i ∈
        s.realKernel 0 := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  exact s.otherCore_not_mem_realKernel 0 i hi.symm hmem

/-- The full ordinary `q`-adic quotient-root exponent belongs to the
phase-zero real core.  Pairwise coprimality of the three cores allocates the
entire exponent to one phase after complete real splitting. -/
theorem realKernelPower_dvd_span_realPairCore
    (s : p.QuotientPrimeSupport) :
    s.realKernel 0 ^ s.quotientExponent ∣
      Ideal.span {p.signedDepth.realPairCore 0} := by
  let v := s.quotientExponent
  have hPq :
      s.realKernel 0 ∣
        Ideal.span
          ({(s.1 : SevenRealCubicInt)} :
            Set SevenRealCubicInt) := by
    refine
      ⟨s.realKernel 1 * s.realKernel 2, ?_⟩
    simpa only [mul_assoc] using
      s.realKernel_product_eq_span_prime.symm
  have hPpow :
      s.realKernel 0 ^ v ∣
        Ideal.span
          ({((s.1 : SevenRealCubicInt) ^ v)} :
            Set SevenRealCubicInt) := by
    simpa only [Ideal.span_singleton_pow] using
      pow_dvd_pow_of_dvd hPq v
  have hnat :
      s.1 ^ v ∣
        Int.natAbs p.signedDepth.quotientRoot := by
    exact pow_padicValNat_dvd
  have hint :
      (s.1 ^ v : ℤ) ∣ p.signedDepth.quotientRoot :=
    Int.natCast_dvd.mpr hnat
  have hcast :
      (s.1 : SevenRealCubicInt) ^ v ∣
        (p.signedDepth.quotientRoot :
          SevenRealCubicInt) := by
    rcases hint with ⟨z, hz⟩
    refine ⟨(z : SevenRealCubicInt), ?_⟩
    simpa using
      congrArg
        (Int.castRingHom SevenRealCubicInt) hz
  have hPquotient :
      s.realKernel 0 ^ v ∣
        Ideal.span
          {(p.signedDepth.quotientRoot :
            SevenRealCubicInt)} :=
    hPpow.trans
      (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
        hcast)
  have hspan :
      Ideal.span
          {(p.signedDepth.quotientRoot :
            SevenRealCubicInt)} =
        Ideal.span {p.signedDepth.realPairCore 0} *
          (Ideal.span {p.signedDepth.realPairCore 1} *
            Ideal.span {p.signedDepth.realPairCore 2}) := by
    calc
      _ =
          Ideal.span
            {p.signedDepth.realPairCore 0 *
              (p.signedDepth.realPairCore 1 *
                p.signedDepth.realPairCore 2)} :=
        (Ideal.span_singleton_eq_span_singleton.mpr
          p.signedDepth.pairCore_product_associated_quotientRoot).symm
      _ =
          Ideal.span {p.signedDepth.realPairCore 0} *
            Ideal.span
              {p.signedDepth.realPairCore 1 *
                p.signedDepth.realPairCore 2} := by
        rw [Ideal.span_singleton_mul_span_singleton]
      _ =
          Ideal.span {p.signedDepth.realPairCore 0} *
            (Ideal.span {p.signedDepth.realPairCore 1} *
              Ideal.span {p.signedDepth.realPairCore 2}) := by
        exact congrArg
          (fun J =>
            Ideal.span {p.signedDepth.realPairCore 0} * J)
          (Ideal.span_singleton_mul_span_singleton
            (p.signedDepth.realPairCore 1)
            (p.signedDepth.realPairCore 2)).symm
  rw [hspan] at hPquotient
  have hcop1 :
      IsCoprime (s.realKernel 0 ^ v)
        (Ideal.span {p.signedDepth.realPairCore 1}) :=
    (s.realKernel_zero_isCoprime_span_otherCore 1
      (by decide)).pow_left
  have hcop2 :
      IsCoprime (s.realKernel 0 ^ v)
        (Ideal.span {p.signedDepth.realPairCore 2}) :=
    (s.realKernel_zero_isCoprime_span_otherCore 2
      (by decide)).pow_left
  exact (hcop1.mul_right hcop2).dvd_of_dvd_mul_right
    hPquotient

/-- Exact real-core multiplicity cutoff for every rational prime in the
full quotient-root support. -/
theorem realPairCore_mem_realKernelPower_iff
    (s : p.QuotientPrimeSupport) (k : ℕ) :
    p.signedDepth.realPairCore 0 ∈
        s.realKernel 0 ^ k ↔
      k ≤ s.quotientExponent := by
  let : Fact (Nat.Prime s.1) := ⟨s.prime⟩
  constructor
  · intro hmem
    have hdiv :
        s.realKernel 0 ^ k ∣
          Ideal.span {p.signedDepth.realPairCore 0} := by
      rw [Ideal.dvd_iff_le]
      exact
        (Ideal.span_singleton_le_iff_mem
          (s.realKernel 0 ^ k)).mpr hmem
    have hnorm := map_dvd Ideal.absNorm hdiv
    have hpow :
        s.1 ^ k ∣
          Int.natAbs p.signedDepth.quotientRoot := by
      simpa only [map_pow, s.absNorm_realKernel,
        absNorm_span_realPairCore_zero] using hnorm
    exact
      (padicValNat_dvd_iff_le
        quotientRoot_natAbs_ne_zero).mp hpow
  · intro hle
    have hdiv := s.realKernelPower_dvd_span_realPairCore
    have hcontain :
        Ideal.span {p.signedDepth.realPairCore 0} ≤
          s.realKernel 0 ^ s.quotientExponent :=
      Ideal.dvd_iff_le.mp hdiv
    have hfull :
        p.signedDepth.realPairCore 0 ∈
          s.realKernel 0 ^ s.quotientExponent :=
      (Ideal.span_singleton_le_iff_mem
        (s.realKernel 0 ^ s.quotientExponent)).mp
          hcontain
    exact (Ideal.pow_le_pow_right hle) hfull

theorem realPairCore_not_mem_realKernelPower_succ
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.realPairCore 0 ∉
      s.realKernel 0 ^ (s.quotientExponent + 1) := by
  rw [s.realPairCore_mem_realKernelPower_iff]
  omega

/-- Canonical oriented degree-six address above a full-support prime. -/
def cyclotomicAddress (s : p.QuotientPrimeSupport) :
    p.CyclotomicLinearPrimeAddress s.1 :=
  p.cyclotomicLinearPrimeAddress s.muSevenAddress

def orientedKernel (s : p.QuotientPrimeSupport) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.evalKernel

def conjugateKernel (s : p.QuotientPrimeSupport) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.conjugateEvalKernel

@[simp] theorem realKernel_zero
    (s : p.QuotientPrimeSupport) :
    s.realKernel 0 =
      RingHom.ker s.muSevenAddress.evalAlphaRoot := by
  simp [realKernel]

/-- The phase-zero real prime extends to the two oriented degree-six
linear primes. -/
theorem map_realKernel_zero_eq_orientedProduct
    (s : p.QuotientPrimeSupport) :
    Ideal.map ofReal (s.realKernel 0) =
      s.orientedKernel * s.conjugateKernel := by
  rw [s.realKernel_zero]
  exact
    s.cyclotomicAddress.realPrimeFiberIdeal_eq_conjugateProduct

/-- Power form of the exact conjugate-prime fibre. -/
theorem map_realKernelPower_eq_orientedProduct
    (s : p.QuotientPrimeSupport) (k : ℕ) :
    Ideal.map ofReal (s.realKernel 0 ^ k) =
      s.orientedKernel ^ k * s.conjugateKernel ^ k := by
  rw [Ideal.map_pow,
    s.map_realKernel_zero_eq_orientedProduct,
    mul_pow]

/-- The opposite linear carrier is excluded from the oriented kernel. -/
theorem conjugateCarrier_not_mem_orientedKernel
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∉
      s.orientedKernel :=
  s.cyclotomicAddress.cyclotomicDegreeSixCarrierConj_not_mem_evalKernel

/-- The oriented linear carrier is excluded from the conjugate kernel. -/
theorem carrier_not_mem_conjugateKernel
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∉
      s.conjugateKernel :=
  s.cyclotomicAddress.carrier_not_mem_conjugateEvalKernel

private theorem orientedKernel_isCoprime_span_conjugateCarrier
    (s : p.QuotientPrimeSupport) :
    IsCoprime s.orientedKernel
      (Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.orientedKernel =
        s.orientedKernel ⊔
          Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrierConj} :=
    s.cyclotomicAddress.evalKernel_isMaximal.eq_of_le
      hne le_sup_left
  have hmem :
      p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.orientedKernel := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  exact s.conjugateCarrier_not_mem_orientedKernel hmem

private theorem conjugateKernel_isCoprime_span_carrier
    (s : p.QuotientPrimeSupport) :
    IsCoprime s.conjugateKernel
      (Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.conjugateKernel =
        s.conjugateKernel ⊔
          Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrier} :=
    s.cyclotomicAddress.conjugateEvalKernel_isMaximal.eq_of_le
      hne le_sup_left
  have hmem :
      p.signedDepth.cyclotomicDegreeSixCarrier ∈
        s.conjugateKernel := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  exact s.carrier_not_mem_conjugateKernel hmem

private theorem realKernel_zero_isCoprime_span_axis
    (s : p.QuotientPrimeSupport) :
    IsCoprime (s.realKernel 0)
      (Ideal.span {SevenRealCubicInt.eisensteinAxis}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq :
      s.realKernel 0 =
        s.realKernel 0 ⊔
          Ideal.span {SevenRealCubicInt.eisensteinAxis} :=
    (s.realKernel_isMaximal 0).eq_of_le
      hne le_sup_left
  have hmem :
      SevenRealCubicInt.eisensteinAxis ∈
        s.realKernel 0 := by
    rw [heq]
    exact Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self _)
  rw [s.realKernel_zero] at hmem
  exact
    s.muSevenAddress.eisensteinAxis_not_mem_evalAlphaRoot_ker
      hmem

private theorem span_realPairCore_dvd_span_realPairCarrier :
    Ideal.span {p.signedDepth.realPairCore 0} ∣
      Ideal.span {p.signedDepth.realPairCarrier 0} := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  refine ⟨SevenRealCubicInt.eisensteinAxis, ?_⟩
  rw [p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core]
  ring

private theorem mapped_total_pairPower_dvd_span_carrierProduct
    (s : p.QuotientPrimeSupport) :
    s.orientedKernel ^ s.quotientExponent *
        s.conjugateKernel ^ s.quotientExponent ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier *
          p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  have hreal :
      s.realKernel 0 ^ s.quotientExponent ∣
        Ideal.span {p.signedDepth.realPairCarrier 0} :=
    s.realKernelPower_dvd_span_realPairCore.trans
      (span_realPairCore_dvd_span_realPairCarrier (p := p))
  have hmap :=
    map_dvd (Ideal.mapHom ofReal) hreal
  change
    Ideal.map ofReal
        (s.realKernel 0 ^ s.quotientExponent) ∣
      Ideal.map ofReal
        (Ideal.span {p.signedDepth.realPairCarrier 0}) at hmap
  rw [s.map_realKernelPower_eq_orientedProduct,
    Ideal.map_span] at hmap
  have hmap' :
      s.orientedKernel ^ s.quotientExponent *
          s.conjugateKernel ^ s.quotientExponent ∣
        Ideal.span
          {ofReal (p.signedDepth.realPairCarrier 0)} := by
    simpa only [Set.image_singleton] using hmap
  simpa only [
    p.signedDepth.cyclotomicDegreeSixCarrier_mul_conj] using hmap'

/-- Exact lower ownership of the complete quotient-root exponent by the
oriented linear carrier. -/
theorem orientedKernelPower_dvd_span_carrier
    (s : p.QuotientPrimeSupport) :
    s.orientedKernel ^ s.quotientExponent ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} := by
  have hcop :
      IsCoprime (s.orientedKernel ^ s.quotientExponent)
        (Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj}) :=
    s.orientedKernel_isCoprime_span_conjugateCarrier.pow_left
  apply hcop.dvd_of_dvd_mul_right
  rw [Ideal.span_singleton_mul_span_singleton]
  exact
    (show
        s.orientedKernel ^ s.quotientExponent ∣
          s.orientedKernel ^ s.quotientExponent *
            s.conjugateKernel ^ s.quotientExponent by
      exact dvd_mul_right _ _).trans
      s.mapped_total_pairPower_dvd_span_carrierProduct

/-- Exact lower ownership of the same complete exponent by the conjugate
linear carrier. -/
theorem conjugateKernelPower_dvd_span_conjugateCarrier
    (s : p.QuotientPrimeSupport) :
    s.conjugateKernel ^ s.quotientExponent ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  have hcop :
      IsCoprime (s.conjugateKernel ^ s.quotientExponent)
        (Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier}) :=
    s.conjugateKernel_isCoprime_span_carrier.pow_left
  apply hcop.dvd_of_dvd_mul_right
  rw [Ideal.span_singleton_mul_span_singleton, mul_comm]
  exact
    (show
        s.conjugateKernel ^ s.quotientExponent ∣
          s.orientedKernel ^ s.quotientExponent *
            s.conjugateKernel ^ s.quotientExponent by
      exact dvd_mul_left _ _).trans
      s.mapped_total_pairPower_dvd_span_carrierProduct

theorem carrier_mem_orientedKernelPower
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∈
      s.orientedKernel ^ s.quotientExponent := by
  rcases s.orientedKernelPower_dvd_span_carrier with
    ⟨J, hJ⟩
  apply
    (Ideal.span_singleton_le_iff_mem
      (s.orientedKernel ^ s.quotientExponent)).mp
  rw [hJ]
  exact Ideal.mul_le_left

theorem conjugateCarrier_mem_conjugateKernelPower
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
      s.conjugateKernel ^ s.quotientExponent := by
  rcases s.conjugateKernelPower_dvd_span_conjugateCarrier with
    ⟨J, hJ⟩
  apply
    (Ideal.span_singleton_le_iff_mem
      (s.conjugateKernel ^ s.quotientExponent)).mp
  rw [hJ]
  exact Ideal.mul_le_left

private theorem star_mem_conjugateKernelPower_of_mem_oriented
    (s : p.QuotientPrimeSupport) {k : ℕ}
    (h :
      p.signedDepth.cyclotomicDegreeSixCarrier ∈
        s.orientedKernel ^ k) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
      s.conjugateKernel ^ k := by
  have hmap :=
    Ideal.mem_map_of_mem
      (starRingEnd SevenCyclotomicDegreeSixInt.Ring) h
  change
    star p.signedDepth.cyclotomicDegreeSixCarrier ∈
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (s.cyclotomicAddress.evalKernel ^ k) at hmap
  rw [p.signedDepth.star_cyclotomicDegreeSixCarrier,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_evalKernel_eq_conjugateEvalKernel] at hmap
  exact hmap

private theorem star_mem_orientedKernelPower_of_mem_conjugate
    (s : p.QuotientPrimeSupport) {k : ℕ}
    (h :
      p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.conjugateKernel ^ k) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∈
      s.orientedKernel ^ k := by
  have hmap :=
    Ideal.mem_map_of_mem
      (starRingEnd SevenCyclotomicDegreeSixInt.Ring) h
  change
    star p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (s.cyclotomicAddress.conjugateEvalKernel ^ k) at hmap
  rw [p.signedDepth.star_cyclotomicDegreeSixCarrierConj,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_conjugateEvalKernel_eq_evalKernel] at hmap
  exact hmap

/-- The next oriented prime power cannot still contain the carrier.

The proof does not assume that the degree-six carrier is a domain.  It
multiplies by the star-conjugate carrier, contracts the extended real ideal
through the faithfully-flat quadratic algebra, cancels the ramified axis in
the real PID, and invokes the exact real-core cutoff. -/
theorem carrier_not_mem_orientedKernelPower_succ
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∉
      s.orientedKernel ^ (s.quotientExponent + 1) := by
  intro hcarrier
  let k := s.quotientExponent + 1
  have hconjugate :
      p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.conjugateKernel ^ k :=
    s.star_mem_conjugateKernelPower_of_mem_oriented hcarrier
  have hproduct :
      p.signedDepth.cyclotomicDegreeSixCarrier *
          p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.orientedKernel ^ k *
          s.conjugateKernel ^ k :=
    Ideal.mul_mem_mul hcarrier hconjugate
  have hmapped :
      ofReal
          (SevenRealCubicInt.eisensteinAxis *
            p.signedDepth.realPairCore 0) ∈
        Ideal.map ofReal (s.realKernel 0 ^ k) := by
    rw [s.map_realKernelPower_eq_orientedProduct]
    simpa only [
      p.signedDepth.cyclotomicDegreeSixCarrier_mul_conj,
      p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core] using
        hproduct
  have hcontracted :
      SevenRealCubicInt.eisensteinAxis *
          p.signedDepth.realPairCore 0 ∈
        s.realKernel 0 ^ k := by
    have hcomap :
        SevenRealCubicInt.eisensteinAxis *
            p.signedDepth.realPairCore 0 ∈
          Ideal.comap ofReal
            (Ideal.map ofReal (s.realKernel 0 ^ k)) :=
      hmapped
    simpa only [SevenCyclotomicDegreeSixInt.ofReal,
      Ideal.comap_map_eq_self_of_faithfullyFlat] using hcomap
  have hdiv :
      s.realKernel 0 ^ k ∣
        Ideal.span
          {SevenRealCubicInt.eisensteinAxis *
            p.signedDepth.realPairCore 0} := by
    rw [Ideal.dvd_iff_le]
    exact
      (Ideal.span_singleton_le_iff_mem
        (s.realKernel 0 ^ k)).mpr hcontracted
  rw [← Ideal.span_singleton_mul_span_singleton] at hdiv
  have hcop :
      IsCoprime (s.realKernel 0 ^ k)
        (Ideal.span {SevenRealCubicInt.eisensteinAxis}) :=
    s.realKernel_zero_isCoprime_span_axis.pow_left
  have hcoreDiv :
      s.realKernel 0 ^ k ∣
        Ideal.span {p.signedDepth.realPairCore 0} :=
    hcop.dvd_of_dvd_mul_left hdiv
  have hcore :
      p.signedDepth.realPairCore 0 ∈
        s.realKernel 0 ^ k := by
    exact
      (Ideal.span_singleton_le_iff_mem
        (s.realKernel 0 ^ k)).mp
          (Ideal.dvd_iff_le.mp hcoreDiv)
  exact s.realPairCore_not_mem_realKernelPower_succ hcore

theorem conjugateCarrier_not_mem_conjugateKernelPower_succ
    (s : p.QuotientPrimeSupport) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∉
      s.conjugateKernel ^ (s.quotientExponent + 1) := by
  intro hconjugate
  exact s.carrier_not_mem_orientedKernelPower_succ
    (s.star_mem_orientedKernelPower_of_mem_conjugate hconjugate)

/-- Exact total oriented-carrier multiplicity at every unramified
quotient-root prime. -/
theorem carrier_mem_orientedKernelPower_iff
    (s : p.QuotientPrimeSupport) (k : ℕ) :
    p.signedDepth.cyclotomicDegreeSixCarrier ∈
        s.orientedKernel ^ k ↔
      k ≤ s.quotientExponent := by
  constructor
  · intro hmem
    by_contra hle
    have hsucc : s.quotientExponent + 1 ≤ k := by
      omega
    have :
        p.signedDepth.cyclotomicDegreeSixCarrier ∈
          s.orientedKernel ^ (s.quotientExponent + 1) :=
      (Ideal.pow_le_pow_right hsucc) hmem
    exact s.carrier_not_mem_orientedKernelPower_succ this
  · intro hle
    exact
      (Ideal.pow_le_pow_right hle)
        s.carrier_mem_orientedKernelPower

/-- Exact total conjugate-carrier multiplicity at the paired prime. -/
theorem conjugateCarrier_mem_conjugateKernelPower_iff
    (s : p.QuotientPrimeSupport) (k : ℕ) :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
        s.conjugateKernel ^ k ↔
      k ≤ s.quotientExponent := by
  constructor
  · intro hmem
    by_contra hle
    have hsucc : s.quotientExponent + 1 ≤ k := by
      omega
    have :
        p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
          s.conjugateKernel ^ (s.quotientExponent + 1) :=
      (Ideal.pow_le_pow_right hsucc) hmem
    exact
      s.conjugateCarrier_not_mem_conjugateKernelPower_succ this
  · intro hle
    exact
      (Ideal.pow_le_pow_right hle)
        s.conjugateCarrier_mem_conjugateKernelPower

/-- Different rational primes in the full quotient-root support give
different phase-zero real prime ideals. -/
theorem realKernel_zero_ne_of_ne
    {s t : p.QuotientPrimeSupport} (hst : s ≠ t) :
    s.realKernel 0 ≠ t.realKernel 0 := by
  have hst' : s.1 ≠ t.1 :=
    Subtype.coe_ne_coe.mpr hst
  have htmem :
      (t.1 : SevenRealCubicInt) ∈ t.realKernel 0 := by
    change t.realEval 0 (t.1 : SevenRealCubicInt) = 0
    simpa only [map_natCast] using ZMod.natCast_self t.1
  have htnot :
      (t.1 : SevenRealCubicInt) ∉ s.realKernel 0 := by
    change s.realEval 0 (t.1 : SevenRealCubicInt) ≠ 0
    have hnotdvd : ¬s.1 ∣ t.1 := by
      intro hdvd
      exact hst'
        ((Nat.prime_dvd_prime_iff_eq s.prime t.prime).mp hdvd)
    rw [map_natCast]
    exact
      (not_congr
        (ZMod.natCast_eq_zero_iff t.1 s.1)).mpr hnotdvd
  intro heq
  exact htnot (heq ▸ htmem)

/-- Phase-zero real primes are pairwise comaximal across the complete
quotient-root support. -/
theorem realKernelZeros_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime (s.realKernel 0) (t.realKernel 0)) := by
  intro s t hst
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      (s.realKernel_isMaximal 0)
      (t.realKernel_isMaximal 0)
      (realKernel_zero_ne_of_ne hst))

/-- Their exact quotient-root powers remain pairwise comaximal. -/
theorem realKernelPowers_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime
          (s.realKernel 0 ^ s.quotientExponent)
          (t.realKernel 0 ^ t.quotientExponent)) := by
  intro s t hst
  exact (realKernelZeros_pairwise_isCoprime hst).pow

/-- Product of all exact phase-zero real-prime powers supported by the
signed quotient root. -/
def globalRealCoreFactorIdeal :
    Ideal SevenRealCubicInt :=
  ∏ s : p.QuotientPrimeSupport,
    s.realKernel 0 ^ s.quotientExponent

/-- The ordinary rational prime powers indexed by the full support
reconstruct the absolute signed quotient root. -/
theorem prod_quotientPrimeSupport_primePow_eq_natAbs :
    (∏ s : p.QuotientPrimeSupport,
        s.1 ^ s.quotientExponent) =
      Int.natAbs p.signedDepth.quotientRoot := by
  calc
    (∏ s : p.QuotientPrimeSupport,
          s.1 ^ s.quotientExponent) =
        ∏ s : p.QuotientPrimeSupport,
          s.1 ^
            (Int.natAbs p.signedDepth.quotientRoot).factorization s.1 := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [quotientExponent,
        Nat.factorization_def _ s.prime]
    _ = Int.natAbs p.signedDepth.quotientRoot := by
      simpa only [RamifiedSignedRootRoutingPacket.QuotientPrimeSupport] using
        (Nat.prod_primeFactors_coe_pow_factorization
          quotientRoot_natAbs_ne_zero).symm

/-- Pairwise comaximality combines all local exact lower bounds. -/
theorem globalRealCoreFactorIdeal_dvd_span_realPairCore :
    globalRealCoreFactorIdeal (p := p) ∣
      Ideal.span {p.signedDepth.realPairCore 0} := by
  apply Fintype.prod_dvd_of_coprime
    realKernelPowers_pairwise_isCoprime
  intro s
  exact s.realKernelPower_dvd_span_realPairCore

theorem absNorm_realKernelPower
    (s : p.QuotientPrimeSupport) :
    Ideal.absNorm
        (s.realKernel 0 ^ s.quotientExponent) =
      s.1 ^ s.quotientExponent := by
  rw [map_pow, s.absNorm_realKernel]

/-- The complete real-prime product has exactly the absolute norm of the
signed quotient root. -/
theorem absNorm_globalRealCoreFactorIdeal :
    Ideal.absNorm (globalRealCoreFactorIdeal (p := p)) =
      Int.natAbs p.signedDepth.quotientRoot := by
  rw [globalRealCoreFactorIdeal, map_prod]
  simpa only [absNorm_realKernelPower] using
    prod_quotientPrimeSupport_primePow_eq_natAbs (p := p)

/-- Exact global factorization of the phase-zero real pair core over every
rational prime dividing the signed quotient root. -/
theorem globalRealCoreFactorIdeal_eq_span_realPairCore :
    globalRealCoreFactorIdeal (p := p) =
      Ideal.span {p.signedDepth.realPairCore 0} := by
  rcases globalRealCoreFactorIdeal_dvd_span_realPairCore (p := p) with
    ⟨J, hJ⟩
  have hnormJ : Ideal.absNorm J = 1 := by
    have hnorm := congrArg Ideal.absNorm hJ
    rw [map_mul, absNorm_span_realPairCore_zero,
      absNorm_globalRealCoreFactorIdeal] at hnorm
    exact Nat.eq_of_mul_eq_mul_left
      (Int.natAbs_pos.mpr quotientRoot_ne_zero)
      (by simpa only [mul_one] using hnorm.symm)
  have hJtop : J = ⊤ :=
    Ideal.absNorm_eq_one_iff.mp hnormJ
  rw [hJtop, Ideal.mul_top] at hJ
  exact hJ.symm

/-- The oriented half of the complete unramified quotient-root
factorization in the degree-six carrier. -/
def globalOrientedCoreHalfIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.orientedKernel ^ s.quotientExponent

/-- The quadratic-conjugate half of the same complete unramified
factorization. -/
def globalConjugateCoreHalfIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.conjugateKernel ^ s.quotientExponent

/-- Extending the complete real-core factorization splits it into the two
explicit degree-six oriented halves. -/
theorem map_globalRealCoreFactorIdeal_eq_halfProduct :
    Ideal.map SevenCyclotomicDegreeSixInt.ofReal
        (globalRealCoreFactorIdeal (p := p)) =
      globalOrientedCoreHalfIdeal (p := p) *
        globalConjugateCoreHalfIdeal (p := p) := by
  rw [globalRealCoreFactorIdeal,
    globalOrientedCoreHalfIdeal,
    globalConjugateCoreHalfIdeal]
  change
    (Ideal.mapHom SevenCyclotomicDegreeSixInt.ofReal)
        (∏ s : p.QuotientPrimeSupport,
          s.realKernel 0 ^ s.quotientExponent) =
      (∏ s : p.QuotientPrimeSupport,
          s.orientedKernel ^ s.quotientExponent) *
        ∏ s : p.QuotientPrimeSupport,
          s.conjugateKernel ^ s.quotientExponent
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_realKernelPower_eq_orientedProduct
    s.quotientExponent

/-- The product of the two complete unramified halves is the principal
ideal generated by the mapped phase-zero real core. -/
theorem globalCoreHalfProduct_eq_span_ofReal_realPairCore :
    globalOrientedCoreHalfIdeal (p := p) *
        globalConjugateCoreHalfIdeal (p := p) =
      Ideal.span
        {SevenCyclotomicDegreeSixInt.ofReal
          (p.signedDepth.realPairCore 0)} := by
  calc
    globalOrientedCoreHalfIdeal (p := p) *
          globalConjugateCoreHalfIdeal (p := p) =
        Ideal.map SevenCyclotomicDegreeSixInt.ofReal
          (globalRealCoreFactorIdeal (p := p)) :=
      map_globalRealCoreFactorIdeal_eq_halfProduct.symm
    _ =
        Ideal.map SevenCyclotomicDegreeSixInt.ofReal
          (Ideal.span {p.signedDepth.realPairCore 0}) := by
      rw [globalRealCoreFactorIdeal_eq_span_realPairCore]
    _ =
        Ideal.span
          {SevenCyclotomicDegreeSixInt.ofReal
            (p.signedDepth.realPairCore 0)} := by
      rw [Ideal.map_span]
      simp only [Set.image_singleton]

/-- Different full-support rational primes give different oriented
degree-six primes. -/
theorem orientedKernel_ne_of_ne
    {s t : p.QuotientPrimeSupport} (hst : s ≠ t) :
    s.orientedKernel ≠ t.orientedKernel := by
  have hst' : s.1 ≠ t.1 :=
    Subtype.coe_ne_coe.mpr hst
  have htmem :
      (t.1 : SevenCyclotomicDegreeSixInt.Ring) ∈
        t.orientedKernel := by
    change
      t.cyclotomicAddress.eval
        (t.1 : SevenCyclotomicDegreeSixInt.Ring) = 0
    simpa only [map_natCast] using ZMod.natCast_self t.1
  have htnot :
      (t.1 : SevenCyclotomicDegreeSixInt.Ring) ∉
        s.orientedKernel := by
    change
      s.cyclotomicAddress.eval
        (t.1 : SevenCyclotomicDegreeSixInt.Ring) ≠ 0
    have hnotdvd : ¬s.1 ∣ t.1 := by
      intro hdvd
      exact hst'
        ((Nat.prime_dvd_prime_iff_eq s.prime t.prime).mp hdvd)
    rw [map_natCast]
    exact
      (not_congr
        (ZMod.natCast_eq_zero_iff t.1 s.1)).mpr hnotdvd
  intro heq
  exact htnot (heq ▸ htmem)

/-- Different full-support rational primes also give different conjugate
degree-six primes. -/
theorem conjugateKernel_ne_of_ne
    {s t : p.QuotientPrimeSupport} (hst : s ≠ t) :
    s.conjugateKernel ≠ t.conjugateKernel := by
  have hst' : s.1 ≠ t.1 :=
    Subtype.coe_ne_coe.mpr hst
  have htmem :
      (t.1 : SevenCyclotomicDegreeSixInt.Ring) ∈
        t.conjugateKernel := by
    change
      t.cyclotomicAddress.conjugateEval
        (t.1 : SevenCyclotomicDegreeSixInt.Ring) = 0
    simpa only [map_natCast] using ZMod.natCast_self t.1
  have htnot :
      (t.1 : SevenCyclotomicDegreeSixInt.Ring) ∉
        s.conjugateKernel := by
    change
      s.cyclotomicAddress.conjugateEval
        (t.1 : SevenCyclotomicDegreeSixInt.Ring) ≠ 0
    have hnotdvd : ¬s.1 ∣ t.1 := by
      intro hdvd
      exact hst'
        ((Nat.prime_dvd_prime_iff_eq s.prime t.prime).mp hdvd)
    rw [map_natCast]
    exact
      (not_congr
        (ZMod.natCast_eq_zero_iff t.1 s.1)).mpr hnotdvd
  intro heq
  exact htnot (heq ▸ htmem)

theorem orientedKernels_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime s.orientedKernel t.orientedKernel) := by
  intro s t hst
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      s.cyclotomicAddress.evalKernel_isMaximal
      t.cyclotomicAddress.evalKernel_isMaximal
      (orientedKernel_ne_of_ne hst))

theorem conjugateKernels_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime s.conjugateKernel t.conjugateKernel) := by
  intro s t hst
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      s.cyclotomicAddress.conjugateEvalKernel_isMaximal
      t.cyclotomicAddress.conjugateEvalKernel_isMaximal
      (conjugateKernel_ne_of_ne hst))

theorem orientedKernelPowers_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime
          (s.orientedKernel ^ s.quotientExponent)
          (t.orientedKernel ^ t.quotientExponent)) := by
  intro s t hst
  exact (orientedKernels_pairwise_isCoprime hst).pow

theorem conjugateKernelPowers_pairwise_isCoprime :
    Pairwise
      (fun s t : p.QuotientPrimeSupport =>
        IsCoprime
          (s.conjugateKernel ^ s.quotientExponent)
          (t.conjugateKernel ^ t.quotientExponent)) := by
  intro s t hst
  exact (conjugateKernels_pairwise_isCoprime hst).pow

/-- All unramified oriented local lower bounds combine into one global
oriented-half divisibility. -/
theorem globalOrientedCoreHalfIdeal_dvd_span_carrier :
    globalOrientedCoreHalfIdeal (p := p) ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} := by
  apply Fintype.prod_dvd_of_coprime
    orientedKernelPowers_pairwise_isCoprime
  intro s
  exact s.orientedKernelPower_dvd_span_carrier

/-- Conjugate form of the global unramified lower bound. -/
theorem globalConjugateCoreHalfIdeal_dvd_span_conjugateCarrier :
    globalConjugateCoreHalfIdeal (p := p) ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  apply Fintype.prod_dvd_of_coprime
    conjugateKernelPowers_pairwise_isCoprime
  intro s
  exact s.conjugateKernelPower_dvd_span_conjugateCarrier

private theorem ramifiedPrime_ne_orientedKernel
    (s : p.QuotientPrimeSupport) :
    SevenCyclotomicDegreeSixInt.ramifiedPrime ≠
      s.orientedKernel := by
  have hseven :
      (7 : SevenCyclotomicDegreeSixInt.Ring) ∈
        SevenCyclotomicDegreeSixInt.ramifiedPrime := by
    change
      SevenCyclotomicDegreeSixInt.ramifiedEval
        (7 : SevenCyclotomicDegreeSixInt.Ring) = 0
    change SevenCyclotomicDegreeSixInt.ramifiedEval
      (SevenCyclotomicDegreeSixInt.ofReal (7 : SevenRealCubicInt)) = 0
    rw [SevenCyclotomicDegreeSixInt.ramifiedEval_ofReal]
    change (7 : ZMod 7) + 3 * 0 + 9 * 0 = 0
    simpa using (ZMod.natCast_self 7)
  have hnot :
      (7 : SevenCyclotomicDegreeSixInt.Ring) ∉
        s.orientedKernel := by
    change
      s.cyclotomicAddress.eval
        (7 : SevenCyclotomicDegreeSixInt.Ring) ≠ 0
    have hnotdvd : ¬s.1 ∣ 7 := by
      intro hdvd
      exact s.ne_seven
        ((Nat.prime_dvd_prime_iff_eq s.prime
          (by norm_num)).mp hdvd)
    have hzmod : (7 : ZMod s.1) ≠ 0 :=
      (not_congr
        (ZMod.natCast_eq_zero_iff 7 s.1)).mpr hnotdvd
    simpa only [map_ofNat] using hzmod
  intro heq
  exact hnot (heq ▸ hseven)

private theorem ramifiedPrime_ne_conjugateKernel
    (s : p.QuotientPrimeSupport) :
    SevenCyclotomicDegreeSixInt.ramifiedPrime ≠
      s.conjugateKernel := by
  have hseven :
      (7 : SevenCyclotomicDegreeSixInt.Ring) ∈
        SevenCyclotomicDegreeSixInt.ramifiedPrime := by
    change
      SevenCyclotomicDegreeSixInt.ramifiedEval
        (7 : SevenCyclotomicDegreeSixInt.Ring) = 0
    change SevenCyclotomicDegreeSixInt.ramifiedEval
      (SevenCyclotomicDegreeSixInt.ofReal (7 : SevenRealCubicInt)) = 0
    rw [SevenCyclotomicDegreeSixInt.ramifiedEval_ofReal]
    change (7 : ZMod 7) + 3 * 0 + 9 * 0 = 0
    simpa using (ZMod.natCast_self 7)
  have hnot :
      (7 : SevenCyclotomicDegreeSixInt.Ring) ∉
        s.conjugateKernel := by
    change
      s.cyclotomicAddress.conjugateEval
        (7 : SevenCyclotomicDegreeSixInt.Ring) ≠ 0
    have hnotdvd : ¬s.1 ∣ 7 := by
      intro hdvd
      exact s.ne_seven
        ((Nat.prime_dvd_prime_iff_eq s.prime
          (by norm_num)).mp hdvd)
    have hzmod : (7 : ZMod s.1) ≠ 0 :=
      (not_congr
        (ZMod.natCast_eq_zero_iff 7 s.1)).mpr hnotdvd
    simpa only [map_ofNat] using hzmod
  intro heq
  exact hnot (heq ▸ hseven)

/-- The ramified prime above seven is comaximal with every unramified
oriented support prime. -/
theorem ramifiedPrime_isCoprime_orientedKernel
    (s : p.QuotientPrimeSupport) :
    IsCoprime SevenCyclotomicDegreeSixInt.ramifiedPrime
      s.orientedKernel := by
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (SevenCyclotomicDegreeSixInt.ramifiedPrime_isMaximal.coprime_of_ne
      s.cyclotomicAddress.evalKernel_isMaximal
      (ramifiedPrime_ne_orientedKernel s))

/-- Conjugate form of the separation from the ramified prime. -/
theorem ramifiedPrime_isCoprime_conjugateKernel
    (s : p.QuotientPrimeSupport) :
    IsCoprime SevenCyclotomicDegreeSixInt.ramifiedPrime
      s.conjugateKernel := by
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (SevenCyclotomicDegreeSixInt.ramifiedPrime_isMaximal.coprime_of_ne
      s.cyclotomicAddress.conjugateEvalKernel_isMaximal
      (ramifiedPrime_ne_conjugateKernel s))

theorem ramifiedPrime_isCoprime_globalOrientedCoreHalfIdeal :
    IsCoprime SevenCyclotomicDegreeSixInt.ramifiedPrime
      (globalOrientedCoreHalfIdeal (p := p)) := by
  rw [globalOrientedCoreHalfIdeal]
  apply IsCoprime.prod_right
  intro s hs
  exact (ramifiedPrime_isCoprime_orientedKernel s).pow_right

theorem ramifiedPrime_isCoprime_globalConjugateCoreHalfIdeal :
    IsCoprime SevenCyclotomicDegreeSixInt.ramifiedPrime
      (globalConjugateCoreHalfIdeal (p := p)) := by
  rw [globalConjugateCoreHalfIdeal]
  apply IsCoprime.prod_right
  intro s hs
  exact (ramifiedPrime_isCoprime_conjugateKernel s).pow_right

/-- The full predicted factor ideal for the oriented linear carrier:
one ramified prime and every unramified quotient-root prime at its exact
ordinary exponent. -/
def globalOrientedCarrierFactorIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  SevenCyclotomicDegreeSixInt.ramifiedPrime *
    globalOrientedCoreHalfIdeal (p := p)

/-- Quadratic-conjugate full predicted carrier factor ideal. -/
def globalConjugateCarrierFactorIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  SevenCyclotomicDegreeSixInt.ramifiedPrime *
    globalConjugateCoreHalfIdeal (p := p)

private theorem ramifiedPrime_dvd_span_carrier :
    SevenCyclotomicDegreeSixInt.ramifiedPrime ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} := by
  rw [SevenCyclotomicDegreeSixInt.ramifiedPrime_eq_span_uniformizer]
  refine
    ⟨Ideal.span {p.signedDepth.ramifiedCarrierQuotient}, ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 2
  exact
    p.signedDepth.cyclotomicDegreeSixCarrier_eq_uniformizer_mul_quotient

private theorem ramifiedPrime_dvd_span_conjugateCarrier :
    SevenCyclotomicDegreeSixInt.ramifiedPrime ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  rw [SevenCyclotomicDegreeSixInt.ramifiedPrime_eq_span_uniformizer]
  refine
    ⟨Ideal.span
      {p.signedDepth.ramifiedConjugateCarrierQuotient}, ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 2
  exact
    p.signedDepth.cyclotomicDegreeSixCarrierConj_eq_uniformizer_mul_quotient

/-- The complete predicted oriented factor ideal divides the oriented
carrier principal ideal. -/
theorem globalOrientedCarrierFactorIdeal_dvd_span_carrier :
    globalOrientedCarrierFactorIdeal (p := p) ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} := by
  exact
    ramifiedPrime_isCoprime_globalOrientedCoreHalfIdeal.mul_dvd
      ramifiedPrime_dvd_span_carrier
      globalOrientedCoreHalfIdeal_dvd_span_carrier

/-- Conjugate complete lower bound. -/
theorem globalConjugateCarrierFactorIdeal_dvd_span_conjugateCarrier :
    globalConjugateCarrierFactorIdeal (p := p) ∣
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  exact
    ramifiedPrime_isCoprime_globalConjugateCoreHalfIdeal.mul_dvd
      ramifiedPrime_dvd_span_conjugateCarrier
      globalConjugateCoreHalfIdeal_dvd_span_conjugateCarrier

private theorem ramifiedPrime_sq_eq_span_ofReal_eisensteinAxis :
    SevenCyclotomicDegreeSixInt.ramifiedPrime ^ 2 =
      Ideal.span
        {SevenCyclotomicDegreeSixInt.ofReal
          SevenRealCubicInt.eisensteinAxis} := by
  symm
  rw [SevenCyclotomicDegreeSixInt.ofReal_eisensteinAxis_eq,
    SevenCyclotomicDegreeSixInt.ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow]
  exact
    Ideal.span_singleton_eq_span_singleton.mpr
      (associated_unit_mul_left
        (SevenCyclotomicDegreeSixInt.ramifiedUniformizer ^ 2)
        SevenCyclotomicDegreeSixInt.zetaInv
        (show IsUnit SevenCyclotomicDegreeSixInt.zetaInv from
          ⟨SevenCyclotomicDegreeSixInt.zetaUnit⁻¹, rfl⟩))

/-- The two predicted full carrier factors multiply to the actual product
of the two conjugate carrier principal ideals. -/
theorem globalCarrierFactorIdeal_pair_eq_spanCarrierPair :
    globalOrientedCarrierFactorIdeal (p := p) *
        globalConjugateCarrierFactorIdeal (p := p) =
      Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} *
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  calc
    globalOrientedCarrierFactorIdeal (p := p) *
          globalConjugateCarrierFactorIdeal (p := p) =
        SevenCyclotomicDegreeSixInt.ramifiedPrime ^ 2 *
          (globalOrientedCoreHalfIdeal (p := p) *
            globalConjugateCoreHalfIdeal (p := p)) := by
      simp only [globalOrientedCarrierFactorIdeal,
        globalConjugateCarrierFactorIdeal, pow_two]
      ring
    _ =
        Ideal.span
            {SevenCyclotomicDegreeSixInt.ofReal
              SevenRealCubicInt.eisensteinAxis} *
          Ideal.span
            {SevenCyclotomicDegreeSixInt.ofReal
              (p.signedDepth.realPairCore 0)} := by
      rw [ramifiedPrime_sq_eq_span_ofReal_eisensteinAxis,
        globalCoreHalfProduct_eq_span_ofReal_realPairCore]
    _ =
        Ideal.span
          {SevenCyclotomicDegreeSixInt.ofReal
            (SevenRealCubicInt.eisensteinAxis *
              p.signedDepth.realPairCore 0)} := by
      rw [map_mul, Ideal.span_singleton_mul_span_singleton]
    _ =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier *
            p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
      rw [p.signedDepth.cyclotomicDegreeSixCarrier_mul_conj,
        p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core]
    _ =
        Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrier} *
          Ideal.span
            {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
      rw [Ideal.span_singleton_mul_span_singleton]

private theorem cyclotomicDegreeSixCarrier_ne_zero :
    p.signedDepth.cyclotomicDegreeSixCarrier ≠ 0 := by
  intro hzero
  apply
    p.signedDepth.cyclotomicDegreeSixCarrier_not_mem_ramifiedPrime_sq
  rw [hzero]
  exact Ideal.zero_mem _

private theorem cyclotomicDegreeSixCarrierConj_ne_zero :
    p.signedDepth.cyclotomicDegreeSixCarrierConj ≠ 0 := by
  intro hzero
  apply
    p.signedDepth.cyclotomicDegreeSixCarrierConj_not_mem_ramifiedPrime_sq
  rw [hzero]
  exact Ideal.zero_mem _

/-- Simultaneous exact global ownership of all ramified and unramified
prime factors by the two conjugate linear carriers.

The last step uses only the proved integral-domain structure of the
concrete degree-six carrier: after extracting both predicted factors, the
pair identity forces the two residual ideals to multiply to top. -/
theorem globalCarrierFactorIdeal_pair_exact :
    globalOrientedCarrierFactorIdeal (p := p) =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} ∧
      globalConjugateCarrierFactorIdeal (p := p) =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
  rcases globalOrientedCarrierFactorIdeal_dvd_span_carrier (p := p) with
    ⟨J, hJ⟩
  rcases
      globalConjugateCarrierFactorIdeal_dvd_span_conjugateCarrier
        (p := p) with
    ⟨K, hK⟩
  have hpair :=
    globalCarrierFactorIdeal_pair_eq_spanCarrierPair (p := p)
  have hresidual :
      (globalOrientedCarrierFactorIdeal (p := p) *
          globalConjugateCarrierFactorIdeal (p := p)) *
          (J * K) =
        globalOrientedCarrierFactorIdeal (p := p) *
          globalConjugateCarrierFactorIdeal (p := p) := by
    calc
      (globalOrientedCarrierFactorIdeal (p := p) *
            globalConjugateCarrierFactorIdeal (p := p)) *
            (J * K) =
          (globalOrientedCarrierFactorIdeal (p := p) * J) *
            (globalConjugateCarrierFactorIdeal (p := p) * K) := by
        ring
      _ =
          Ideal.span
              {p.signedDepth.cyclotomicDegreeSixCarrier} *
            Ideal.span
              {p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
        rw [← hJ, ← hK]
      _ =
          globalOrientedCarrierFactorIdeal (p := p) *
            globalConjugateCarrierFactorIdeal (p := p) :=
        hpair.symm
  have hfactorPrincipal :
      globalOrientedCarrierFactorIdeal (p := p) *
          globalConjugateCarrierFactorIdeal (p := p) =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier *
            p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
    rw [hpair, Ideal.span_singleton_mul_span_singleton]
  have hcarrierProduct :
      p.signedDepth.cyclotomicDegreeSixCarrier *
          p.signedDepth.cyclotomicDegreeSixCarrierConj ≠ 0 :=
    mul_ne_zero cyclotomicDegreeSixCarrier_ne_zero
      cyclotomicDegreeSixCarrierConj_ne_zero
  have hJKtop : J * K = ⊤ := by
    apply
      Ideal.span_singleton_mul_right_injective hcarrierProduct
    rw [hfactorPrincipal] at hresidual
    simpa only [Ideal.mul_top] using hresidual
  have hJtop : J = ⊤ := by
    apply top_unique
    rw [← hJKtop]
    exact Ideal.mul_le_left
  have hKtop : K = ⊤ := by
    apply top_unique
    rw [← hJKtop]
    exact Ideal.mul_le_right
  constructor
  · rw [hJtop, Ideal.mul_top] at hJ
    exact hJ.symm
  · rw [hKtop, Ideal.mul_top] at hK
    exact hK.symm

/-- Exact principal-ideal factorization of the oriented carrier. -/
theorem globalOrientedCarrierFactorIdeal_eq_span_carrier :
    globalOrientedCarrierFactorIdeal (p := p) =
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} :=
  (globalCarrierFactorIdeal_pair_exact (p := p)).1

/-- Exact principal-ideal factorization of the conjugate carrier. -/
theorem globalConjugateCarrierFactorIdeal_eq_span_conjugateCarrier :
    globalConjugateCarrierFactorIdeal (p := p) =
      Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} :=
  (globalCarrierFactorIdeal_pair_exact (p := p)).2

/-- Compact U1.2 global valuation-ownership packet. -/
theorem globalCarrierValuationOwnershipPacket :
    globalOrientedCarrierFactorIdeal (p := p) =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} ∧
      globalConjugateCarrierFactorIdeal (p := p) =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} ∧
      (∀ s : p.QuotientPrimeSupport, ∀ k : ℕ,
        p.signedDepth.cyclotomicDegreeSixCarrier ∈
            s.orientedKernel ^ k ↔
          k ≤ s.quotientExponent) ∧
      ∀ s : p.QuotientPrimeSupport, ∀ k : ℕ,
        p.signedDepth.cyclotomicDegreeSixCarrierConj ∈
            s.conjugateKernel ^ k ↔
          k ≤ s.quotientExponent :=
  ⟨globalOrientedCarrierFactorIdeal_eq_span_carrier,
    globalConjugateCarrierFactorIdeal_eq_span_conjugateCarrier,
    fun s k => s.carrier_mem_orientedKernelPower_iff k,
    fun s k => s.conjugateCarrier_mem_conjugateKernelPower_iff k⟩

end QuotientPrimeSupport

end RamifiedSignedRootRoutingPacket


end

end DkMath.FLT.Seven
