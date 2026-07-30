/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadExactValuation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Coprime.Lemmas

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGlobalFactorization"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedFusionRow2LoadFamily

open SevenRealCubicInt
open Module

variable (family : RamifiedFusionRow2LoadFamily)
  (p : RamifiedSignedRootRoutingPacket)

/-- Canonical finite support of rational primes occurring in the selected
row-two routing cell. -/
def PrimeSupport :=
  {q : ℕ // q ∈ (family.cell p).primeFactors}

instance primeSupportFintype :
    Fintype (PrimeSupport family p) :=
  Finset.fintypeCoeSort _

namespace PrimeSupport

variable {family : RamifiedFusionRow2LoadFamily}
  {p : RamifiedSignedRootRoutingPacket}

/-- A member of the canonical prime support supplies the corresponding
explicit quotient-prime gcd-load address. -/
def address
    (s : PrimeSupport family p) :
    p.QuotientPrimeGCDLoadAddress s.1 where
  family := family
  prime := Nat.prime_of_mem_primeFactors s.2
  dividesCell := Nat.dvd_of_mem_primeFactors s.2

@[simp] theorem address_family
    (s : PrimeSupport family p) :
    s.address.family = family :=
  rfl

/-- Exact prime-ideal power contributed by one member of the canonical
rational-prime support. -/
def kernelPower
    (s : PrimeSupport family p) :
    Ideal SevenRealCubicInt :=
  s.address.evalKernel ^
    padicValNat s.1 (family.cell p)

/-- The addressed prime-ideal power divides the selected zeroth load
principal ideal at its full rational-prime exponent. -/
theorem kernelPower_dvd_span_load
    (s : PrimeSupport family p) :
    s.kernelPower ∣
      Ideal.span {family.load p 0} := by
  have h :=
    (s.address.evalKernel_pow_dvd_span_addressedLoad_iff_padicValNat
      (padicValNat s.1 (family.cell p))).mpr le_rfl
  simpa only [kernelPower,
    RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress.addressedLoad,
    address_family] using h

/-- Different rational primes in the canonical support select different
degree-one prime ideals. -/
theorem evalKernel_ne_of_ne
    {s t : PrimeSupport family p} (hst : s ≠ t) :
    s.address.evalKernel ≠ t.address.evalKernel := by
  have hst' : s.1 ≠ t.1 :=
    Subtype.coe_ne_coe.mpr hst
  have hprimeS : Nat.Prime s.1 :=
    Nat.prime_of_mem_primeFactors s.2
  have hprimeT : Nat.Prime t.1 :=
    Nat.prime_of_mem_primeFactors t.2
  have htmem :
      (t.1 : SevenRealCubicInt) ∈
        t.address.evalKernel := by
    change
      t.address.evalAlphaRoot
        (t.1 : SevenRealCubicInt) = 0
    simpa only [map_natCast] using
      ZMod.natCast_self t.1
  have htnot :
      (t.1 : SevenRealCubicInt) ∉
        s.address.evalKernel := by
    change
      s.address.evalAlphaRoot
        (t.1 : SevenRealCubicInt) ≠ 0
    have hnotdvd : ¬s.1 ∣ t.1 := by
      intro hdvd
      exact hst'
        ((Nat.prime_dvd_prime_iff_eq hprimeS hprimeT).mp hdvd)
    rw [map_natCast]
    exact
      (not_congr
        (ZMod.natCast_eq_zero_iff t.1 s.1)).mpr hnotdvd
  intro heq
  apply htnot
  rw [heq]
  exact htmem

/-- Kernel ideals belonging to different members of the rational-prime
support are comaximal. -/
theorem evalKernels_pairwise_isCoprime :
    Pairwise
      (fun s t : PrimeSupport family p =>
        IsCoprime s.address.evalKernel
          t.address.evalKernel) := by
  intro s t hst
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (Ideal.IsMaximal.coprime_of_ne
      s.address.evalKernel_isMaximal
      t.address.evalKernel_isMaximal
      (evalKernel_ne_of_ne hst))

/-- The exact kernel powers remain pairwise comaximal across distinct
rational primes. -/
theorem kernelPowers_pairwise_isCoprime :
    Pairwise
      (fun s t : PrimeSupport family p =>
        IsCoprime s.kernelPower t.kernelPower) := by
  intro s t hst
  exact (evalKernels_pairwise_isCoprime hst).pow

end PrimeSupport

/-- Product of all exact degree-one kernel powers supported by the selected
integer routing cell. -/
def globalLoadFactorIdeal :
    Ideal SevenRealCubicInt :=
  ∏ s : PrimeSupport family p, s.kernelPower

/-- Either selected row-two routing cell is nonzero. -/
theorem cell_ne_zero :
    family.cell p ≠ 0 := by
  cases family with
  | cell21 =>
      change p.routing.c21 ≠ 0
      intro hzero
      apply p.activeCells_not_seven_dvd.2.2.2.1
      rw [hzero]
      exact dvd_zero 7
  | cell22 =>
      change p.routing.c22 ≠ 0
      intro hzero
      apply p.activeCells_not_seven_dvd.2.2.2.2.1
      rw [hzero]
      exact dvd_zero 7

/-- The product of ordinary prime powers indexed by the canonical support
reconstructs the selected routing cell exactly. -/
theorem prod_primeSupport_primePow_eq_cell :
    (∏ s : PrimeSupport family p,
        s.1 ^ padicValNat s.1 (family.cell p)) =
      family.cell p := by
  calc
    (∏ s : PrimeSupport family p,
          s.1 ^ padicValNat s.1 (family.cell p)) =
        ∏ s : PrimeSupport family p,
          s.1 ^ (family.cell p).factorization s.1 := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [Nat.factorization_def _
        (Nat.prime_of_mem_primeFactors s.2)]
    _ = family.cell p := by
      simpa only [PrimeSupport] using
        (Nat.prod_pow_primeFactors_factorization
          (cell_ne_zero family p)).symm

/-- Pairwise comaximality combines the complete set of local kernel-power
divisibilities into one global product divisibility. -/
theorem globalLoadFactorIdeal_dvd_span_load :
    globalLoadFactorIdeal family p ∣
      Ideal.span {family.load p 0} := by
  apply Fintype.prod_dvd_of_coprime
    PrimeSupport.kernelPowers_pairwise_isCoprime
  intro s
  exact PrimeSupport.kernelPower_dvd_span_load s

private def globalCoordinateAddEquiv :
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

private def globalCoordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun globalCoordinateAddEquiv.toIntLinearEquiv

local instance globalModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis globalCoordinateBasis

local instance globalModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis globalCoordinateBasis

private theorem globalAlgebraNorm_eq_norm
    (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = norm x := by
  rw [Algebra.norm_eq_matrix_det globalCoordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    globalCoordinateBasis, globalCoordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

/-- Absolute norm of one exact prime-ideal power in the canonical support. -/
theorem PrimeSupport.absNorm_kernelPower
    (s : PrimeSupport family p) :
    Ideal.absNorm s.kernelPower =
      s.1 ^ padicValNat s.1 (family.cell p) := by
  rw [PrimeSupport.kernelPower, map_pow,
    s.address.absNorm_evalKernel]

/-- The global prime-ideal product has absolute norm equal to the selected
routing cell. -/
theorem absNorm_globalLoadFactorIdeal :
    Ideal.absNorm (globalLoadFactorIdeal family p) =
      family.cell p := by
  rw [globalLoadFactorIdeal, map_prod]
  simpa only [PrimeSupport.absNorm_kernelPower] using
    prod_primeSupport_primePow_eq_cell family p

/-- The selected zeroth load principal ideal has the same exact absolute
norm as its integer routing cell. -/
theorem absNorm_span_load :
    Ideal.absNorm
        (Ideal.span {family.load p 0}) =
      family.cell p := by
  rw [Ideal.absNorm_span_singleton,
    globalAlgebraNorm_eq_norm]
  cases family with
  | cell21 =>
      exact p.natAbs_norm_realPairLoad21 0
  | cell22 =>
      exact p.natAbs_norm_realPairLoad22 0

/-- Global exact factorization of the selected zeroth gcd load:
its principal ideal is the product, over every rational prime in the
selected cell, of the canonical degree-one kernel raised to the ordinary
`q`-adic exponent of that cell.

This is an ideal factorization statement.  It does not assert that the
individual kernel ideals are principal. -/
theorem globalLoadFactorIdeal_eq_span_load :
    globalLoadFactorIdeal family p =
      Ideal.span {family.load p 0} := by
  have hdiv :=
    globalLoadFactorIdeal_dvd_span_load family p
  rcases hdiv with ⟨J, hJ⟩
  have hnormJ : Ideal.absNorm J = 1 := by
    have hnorm := congrArg Ideal.absNorm hJ
    rw [map_mul, absNorm_span_load,
      absNorm_globalLoadFactorIdeal] at hnorm
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (cell_ne_zero family p))
      (by simpa only [mul_one] using hnorm.symm)
  have hJtop : J = ⊤ :=
    Ideal.absNorm_eq_one_iff.mp hnormJ
  rw [hJtop, Ideal.mul_top] at hJ
  exact hJ.symm

end RamifiedFusionRow2LoadFamily

end

end DkMath.FLT.Seven
