/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadAddress
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGalois"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedFusionRow2LoadFamily

open SevenRealCubicInt

instance : Infinite SevenRealCubicInt :=
  Infinite.of_injective SevenRealCubicInt.ofInt (by
    intro a b hab
    exact congrArg (fun x : SevenRealCubicInt => x.fst) hab)

/-- The first Galois step transports the zeroth load to the first load,
up to the normalization unit chosen by `gcd`. -/
theorem rotate_load_zero_associated_one
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (family.load p 0))
      (family.load p 1) := by
  cases family
  · exact p.rotate_realPairLoad21_zero_associated_one
  · exact p.rotate_realPairLoad22_zero_associated_one

/-- The second Galois step transports the first load to the second load. -/
theorem rotate_load_one_associated_two
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (family.load p 1))
      (family.load p 2) := by
  cases family
  · exact p.rotate_realPairLoad21_one_associated_two
  · exact p.rotate_realPairLoad22_one_associated_two

/-- The third Galois step closes the load orbit. -/
theorem rotate_load_two_associated_zero
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    Associated
      (rotateEquiv (family.load p 2))
      (family.load p 0) := by
  cases family
  · exact p.rotate_realPairLoad21_two_associated_zero
  · exact p.rotate_realPairLoad22_two_associated_zero

/-- Loads in distinct real-pair positions remain Bezout-coprime. -/
theorem loads_pairwiseCoprime
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (family.load p i) (family.load p j)) := by
  cases family
  · exact p.realPairLoad21_pairwiseCoprime
  · exact p.realPairLoad22_pairwiseCoprime

end RamifiedFusionRow2LoadFamily

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

open SevenRealCubicInt
open Module

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

private def galoisCoordinateAddEquiv :
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

private def galoisCoordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun galoisCoordinateAddEquiv.toIntLinearEquiv

local instance galoisModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis galoisCoordinateBasis

local instance galoisModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis galoisCoordinateBasis

private theorem galoisAlgebraNorm_eq_norm
    (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = norm x := by
  rw [Algebra.norm_eq_matrix_det galoisCoordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    galoisCoordinateBasis, galoisCoordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

/-- The three local evaluations obtained from the canonical zeroth
quotient-prime address by the order-three real-cubic automorphism.

The index-one evaluation precomposes by `rotateEquiv⁻¹`; the index-two
evaluation precomposes by `rotateEquiv`.  This orientation makes evaluation
`i` vanish on the load in pair-core position `i`. -/
def galoisEval
    (a : p.QuotientPrimeGCDLoadAddress q) (i : Fin 3) :
    SevenRealCubicInt →+* ZMod q :=
  if i = 0 then
    a.evalAlphaRoot
  else if i = 1 then
    a.evalAlphaRoot.comp rotateEquiv.symm.toRingHom
  else
    a.evalAlphaRoot.comp rotateEquiv.toRingHom

/-- The three conjugate degree-one kernels above the addressed rational
prime. -/
def galoisKernel
    (a : p.QuotientPrimeGCDLoadAddress q) (i : Fin 3) :
    Ideal SevenRealCubicInt :=
  RingHom.ker (a.galoisEval i)

@[simp] theorem galoisEval_zero
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 0 = a.evalAlphaRoot := by
  simp [galoisEval]

@[simp] theorem galoisEval_one
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 1 =
      a.evalAlphaRoot.comp rotateEquiv.symm.toRingHom := by
  simp [galoisEval]

@[simp] theorem galoisEval_two
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 2 =
      a.evalAlphaRoot.comp rotateEquiv.toRingHom := by
  simp [galoisEval]

@[simp] theorem galoisKernel_zero
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisKernel 0 = a.evalKernel := by
  simp [galoisKernel, evalKernel]

private theorem map_eq_zero_of_dvd
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x y : R}
    (hx : f x = 0) (hxy : x ∣ y) :
    f y = 0 := by
  rcases hxy with ⟨c, rfl⟩
  rw [map_mul, hx, zero_mul]

/-- The first transported evaluation reverses the first Galois step. -/
theorem galoisEval_one_rotate
    (a : p.QuotientPrimeGCDLoadAddress q)
    (x : SevenRealCubicInt) :
    a.galoisEval 1 (rotateEquiv x) =
      a.galoisEval 0 x := by
  change
    a.evalAlphaRoot (rotateEquiv.symm (rotateEquiv x)) =
      a.evalAlphaRoot x
  rw [RingEquiv.symm_apply_apply]

/-- The second transported evaluation reverses the second Galois step. -/
theorem galoisEval_two_rotate
    (a : p.QuotientPrimeGCDLoadAddress q)
    (x : SevenRealCubicInt) :
    a.galoisEval 2 (rotateEquiv x) =
      a.galoisEval 1 x := by
  change
    a.evalAlphaRoot (rotateEquiv (rotateEquiv x)) =
      a.evalAlphaRoot (rotateEquiv.symm x)
  congr 1

/-- The final rotation closes the evaluation cycle. -/
theorem galoisEval_zero_rotate
    (a : p.QuotientPrimeGCDLoadAddress q)
    (x : SevenRealCubicInt) :
    a.galoisEval 0 (rotateEquiv x) =
      a.galoisEval 2 x := by
  simp

/-- The zeroth local coordinate is the canonical real `mu_7` coordinate
`beta = ratio + ratio⁻¹ + 1`. -/
theorem galoisEval_zero_alpha
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 0 alpha = a.muSevenAddress.beta := by
  change a.evalAlphaRoot alpha = a.muSevenAddress.beta
  exact a.muSevenAddress.evalAlphaRoot_alpha

/-- Explicit first conjugate of the real `mu_7` coordinate. -/
theorem galoisEval_one_alpha
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 1 alpha =
      -a.muSevenAddress.beta ^ 2 +
        a.muSevenAddress.beta + 2 := by
  have hinv :
      rotateEquiv.symm alpha =
        rotateEquiv (rotateEquiv alpha) := by
    apply rotateEquiv.injective
    rw [RingEquiv.apply_symm_apply, rotateEquiv_three]
  have hbeta :
      a.evalAlphaRoot alpha = a.muSevenAddress.beta :=
    a.muSevenAddress.evalAlphaRoot_alpha
  change
    a.evalAlphaRoot (rotateEquiv.symm alpha) =
      -a.muSevenAddress.beta ^ 2 +
        a.muSevenAddress.beta + 2
  rw [hinv, rotateEquiv_sq_alpha, map_add, map_add,
    map_neg, map_pow, hbeta, map_ofNat]

/-- Explicit second conjugate of the real `mu_7` coordinate. -/
theorem galoisEval_two_alpha
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisEval 2 alpha =
      a.muSevenAddress.beta ^ 2 -
        2 * a.muSevenAddress.beta := by
  have hbeta :
      a.evalAlphaRoot alpha = a.muSevenAddress.beta :=
    a.muSevenAddress.evalAlphaRoot_alpha
  change
    a.evalAlphaRoot (rotateEquiv alpha) =
      a.muSevenAddress.beta ^ 2 -
        2 * a.muSevenAddress.beta
  rw [rotateEquiv_alpha, map_sub, map_pow, map_mul,
    hbeta, map_ofNat]

/-- Each same-family gcd load belongs to its own transported local kernel. -/
theorem galoisEval_ownLoad_zero
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    a.galoisEval i (a.family.load p i) = 0 := by
  fin_cases i
  · change a.evalAlphaRoot (a.family.load p 0) = 0
    simpa only [addressedLoad] using
      a.evalAlphaRoot_addressedLoad_zero
  · change
      a.evalAlphaRoot
        (rotateEquiv.symm (a.family.load p 1)) = 0
    have hdiv :
        a.family.load p 0 ∣
          rotateEquiv.symm (a.family.load p 1) := by
      have hmap :=
        map_dvd rotateEquiv.symm.toRingHom
          (a.family.rotate_load_zero_associated_one p).dvd
      change
        rotateEquiv.symm
            (rotateEquiv (a.family.load p 0)) ∣
          rotateEquiv.symm (a.family.load p 1) at hmap
      rw [RingEquiv.symm_apply_apply] at hmap
      exact hmap
    exact map_eq_zero_of_dvd a.evalAlphaRoot
      (by simpa only [addressedLoad] using
        a.evalAlphaRoot_addressedLoad_zero)
      hdiv
  · change
      a.evalAlphaRoot
        (rotateEquiv (a.family.load p 2)) = 0
    exact map_eq_zero_of_dvd a.evalAlphaRoot
      (by simpa only [addressedLoad] using
        a.evalAlphaRoot_addressedLoad_zero)
      (a.family.rotate_load_two_associated_zero p).symm.dvd

/-- Ideal-membership form of the conjugate load-address theorem. -/
theorem ownLoad_mem_galoisKernel
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    a.family.load p i ∈ a.galoisKernel i :=
  a.galoisEval_ownLoad_zero i

/-- At a fixed Galois address, every other same-family load is excluded. -/
theorem galoisEval_otherLoad_ne_zero
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i j : Fin 3) (hij : i ≠ j) :
    a.galoisEval i (a.family.load p j) ≠ 0 := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro hother
  rcases a.family.loads_pairwiseCoprime p hij with
    ⟨u, v, huv⟩
  have hmap := congrArg (a.galoisEval i) huv
  rw [map_add, map_mul, map_mul,
    a.galoisEval_ownLoad_zero i, hother,
    mul_zero, mul_zero, add_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- Kernel-exclusion form for every distinct pair of load positions. -/
theorem otherLoad_not_mem_galoisKernel
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i j : Fin 3) (hij : i ≠ j) :
    a.family.load p j ∉ a.galoisKernel i :=
  a.galoisEval_otherLoad_ne_zero i j hij

/-- The three transported kernels are pairwise distinct, witnessed by the
same-family load in the first position. -/
theorem galoisKernels_pairwise_ne
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Pairwise (fun i j : Fin 3 => a.galoisKernel i ≠ a.galoisKernel j) := by
  intro i j hij heq
  exact a.otherLoad_not_mem_galoisKernel j i hij.symm
    (heq ▸ a.ownLoad_mem_galoisKernel i)

/-- Every conjugate evaluation remains onto `ZMod q`. -/
theorem galoisEval_surjective
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Function.Surjective (a.galoisEval i) := by
  fin_cases i
  · change Function.Surjective a.evalAlphaRoot
    exact a.evalAlphaRoot_surjective
  · intro z
    rcases a.evalAlphaRoot_surjective z with ⟨x, hx⟩
    refine ⟨rotateEquiv x, ?_⟩
    change
      a.evalAlphaRoot
        (rotateEquiv.symm (rotateEquiv x)) = z
    rw [RingEquiv.symm_apply_apply]
    exact hx
  · intro z
    rcases a.evalAlphaRoot_surjective z with ⟨x, hx⟩
    refine ⟨rotateEquiv.symm x, ?_⟩
    change
      a.evalAlphaRoot
        (rotateEquiv (rotateEquiv.symm x)) = z
    rw [RingEquiv.apply_symm_apply]
    exact hx

/-- Each of the three conjugate degree-one kernels is maximal. -/
theorem galoisKernel_isMaximal
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    (a.galoisKernel i).IsMaximal := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  exact RingHom.ker_isMaximal_of_surjective
    (a.galoisEval i) (a.galoisEval_surjective i)

/-- Every conjugate kernel contracts to the same rational prime `(q)`. -/
theorem galoisKernel_comap_intCast
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Ideal.comap (Int.castRingHom SevenRealCubicInt)
        (a.galoisKernel i) =
      Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change
    a.galoisEval i (z : SevenRealCubicInt) = 0 ↔
      (q : ℤ) ∣ z
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Each conjugate residue quotient has exactly `q` elements. -/
theorem galoisKernel_cardQuot
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Submodule.cardQuot (a.galoisKernel i) = q := by
  let : Fact (Nat.Prime q) := ⟨a.prime⟩
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card
        (SevenRealCubicInt ⧸ a.galoisKernel i) =
        Nat.card (ZMod q) :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective
          (a.galoisEval_surjective i)).toEquiv
    _ = q := Nat.card_zmod q

/-- Equivalently, every conjugate kernel has absolute ideal norm `q`. -/
theorem absNorm_galoisKernel
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Ideal.absNorm (a.galoisKernel i) = q := by
  rw [Ideal.absNorm_apply]
  exact a.galoisKernel_cardQuot i

/-- Distinct transported kernels are comaximal. -/
theorem galoisKernels_pairwise_isCoprime
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (a.galoisKernel i) (a.galoisKernel j)) := by
  intro i j hij
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      (a.galoisKernel_isMaximal i)
      (a.galoisKernel_isMaximal j)
      (a.galoisKernels_pairwise_ne hij))

/-- The rational principal ideal `(q)` is contained in every one of the
three conjugate kernels. -/
theorem span_prime_le_galoisKernel
    (a : p.QuotientPrimeGCDLoadAddress q)
    (i : Fin 3) :
    Ideal.span
        ({(q : SevenRealCubicInt)} :
          Set SevenRealCubicInt) ≤
      a.galoisKernel i := by
  rw [Ideal.span_singleton_le_iff_mem]
  change a.galoisEval i (q : SevenRealCubicInt) = 0
  simpa only [map_natCast] using ZMod.natCast_self q

/-- The product of the three pairwise-comaximal kernels is their
threefold intersection. -/
theorem galoisKernel_product_eq_inf
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisKernel 0 * a.galoisKernel 1 *
        a.galoisKernel 2 =
      (a.galoisKernel 0 ⊓ a.galoisKernel 1) ⊓
        a.galoisKernel 2 := by
  have h01 :
      IsCoprime (a.galoisKernel 0)
        (a.galoisKernel 1) :=
    a.galoisKernels_pairwise_isCoprime (by decide)
  have h02 :
      IsCoprime (a.galoisKernel 0)
        (a.galoisKernel 2) :=
    a.galoisKernels_pairwise_isCoprime (by decide)
  have h12 :
      IsCoprime (a.galoisKernel 1)
        (a.galoisKernel 2) :=
    a.galoisKernels_pairwise_isCoprime (by decide)
  calc
    a.galoisKernel 0 * a.galoisKernel 1 *
          a.galoisKernel 2 =
        (a.galoisKernel 0 * a.galoisKernel 1) ⊓
          a.galoisKernel 2 :=
      Ideal.mul_eq_inf_of_isCoprime (h02.mul_left h12)
    _ =
        (a.galoisKernel 0 ⊓ a.galoisKernel 1) ⊓
          a.galoisKernel 2 := by
      rw [Ideal.mul_eq_inf_of_isCoprime h01]

/-- The three-kernel product has absolute norm `q³`. -/
theorem absNorm_galoisKernel_product
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Ideal.absNorm
        (a.galoisKernel 0 * a.galoisKernel 1 *
          a.galoisKernel 2) =
      q ^ 3 := by
  rw [map_mul, map_mul, a.absNorm_galoisKernel,
    a.absNorm_galoisKernel, a.absNorm_galoisKernel]
  ring

/-- The rational principal ideal `(q)` also has absolute norm `q³`,
because the real cubic order has rank three. -/
theorem absNorm_span_natCast
    (q : ℕ) :
    Ideal.absNorm
        (Ideal.span
          ({(q : SevenRealCubicInt)} :
            Set SevenRealCubicInt)) =
      q ^ 3 := by
  rw [Ideal.absNorm_span_singleton,
    galoisAlgebraNorm_eq_norm]
  simp [SevenRealCubicInt.norm]

/-- Complete splitting of the addressed rational prime in the explicit
three degree-one Galois kernels. -/
theorem galoisKernel_product_eq_span_prime
    (a : p.QuotientPrimeGCDLoadAddress q) :
    a.galoisKernel 0 * a.galoisKernel 1 *
        a.galoisKernel 2 =
      Ideal.span
        ({(q : SevenRealCubicInt)} :
          Set SevenRealCubicInt) := by
  let P : Ideal SevenRealCubicInt :=
    a.galoisKernel 0 * a.galoisKernel 1 *
      a.galoisKernel 2
  let Q : Ideal SevenRealCubicInt :=
    Ideal.span
      ({(q : SevenRealCubicInt)} :
        Set SevenRealCubicInt)
  have hQP : Q ≤ P := by
    dsimp only [P, Q]
    rw [a.galoisKernel_product_eq_inf]
    exact le_inf
      (le_inf
        (a.span_prime_le_galoisKernel 0)
        (a.span_prime_le_galoisKernel 1))
      (a.span_prime_le_galoisKernel 2)
  have hdiv : P ∣ Q :=
    Ideal.dvd_iff_le.mpr hQP
  rcases hdiv with ⟨J, hJ⟩
  have hnormJ : Ideal.absNorm J = 1 := by
    have hnorm := congrArg Ideal.absNorm hJ
    rw [map_mul] at hnorm
    have hnormP : Ideal.absNorm P = q ^ 3 := by
      simpa only [P] using
        a.absNorm_galoisKernel_product
    have hnormQ : Ideal.absNorm Q = q ^ 3 := by
      simpa only [Q] using absNorm_span_natCast q
    rw [hnormQ, hnormP] at hnorm
    exact Nat.eq_of_mul_eq_mul_left
      (pow_pos a.prime.pos 3)
      (by simpa only [mul_one] using hnorm.symm)
  have hJtop : J = ⊤ :=
    Ideal.absNorm_eq_one_iff.mp hnormJ
  rw [hJtop, Ideal.mul_top] at hJ
  simpa only [P, Q] using hJ.symm

end RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

end

end DkMath.FLT.Seven
