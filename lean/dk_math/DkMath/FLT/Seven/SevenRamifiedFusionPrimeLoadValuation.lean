/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadAddress
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadValuation"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

open SevenRealCubicInt
open Module
open UniqueFactorizationMonoid

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

private def coordinateAddEquiv :
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

private def coordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun coordinateAddEquiv.toIntLinearEquiv

local instance primeLoadModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis coordinateBasis

local instance primeLoadModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis coordinateBasis

/-- The coordinate determinant norm agrees with the generic algebra norm
used by ideal absolute norms. -/
private theorem algebraNorm_eq_norm (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = norm x := by
  rw [Algebra.norm_eq_matrix_det coordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    coordinateBasis, coordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

/-- The addressed routing cell is nonzero. -/
theorem addressedCell_ne_zero
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.family.cell p ≠ 0 := by
  cases hfamily : a.family with
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

/-- The addressed algebraic gcd load is nonzero. -/
theorem addressedLoad_ne_zero
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.addressedLoad ≠ 0 := by
  intro hzero
  have hnorm := a.natAbs_norm_addressedLoad
  rw [hzero] at hnorm
  norm_num [SevenRealCubicInt.norm] at hnorm
  exact a.addressedCell_ne_zero hnorm.symm

/-- The principal ideal of the addressed load is nonzero. -/
theorem span_addressedLoad_ne_bot
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    Ideal.span {a.addressedLoad} ≠ (⊥ : Ideal SevenRealCubicInt) := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
    a.addressedLoad_ne_zero

/-- Exact absolute ideal norm of the addressed-load principal ideal. -/
theorem absNorm_span_addressedLoad
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    Ideal.absNorm (Ideal.span {a.addressedLoad}) =
      a.family.cell p := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_norm]
  exact a.natAbs_norm_addressedLoad

/-- Exact absolute ideal norm of the explicit residue-field kernel. -/
theorem absNorm_evalKernel
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    Ideal.absNorm a.evalKernel = q := by
  rw [Ideal.absNorm_apply]
  exact a.evalKernel_cardQuot

/-- The explicit kernel is a nonzero prime ideal. -/
theorem evalKernel_ne_bot
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.evalKernel ≠ (⊥ : Ideal SevenRealCubicInt) := by
  intro hzero
  have hmem := a.addressedLoad_mem_evalKernel
  rw [hzero, Ideal.mem_bot] at hmem
  exact a.addressedLoad_ne_zero hmem

/-- Multiplicity of the explicit prime kernel in the principal ideal of the
addressed algebraic gcd load. -/
def evalKernelMultiplicity
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    ℕ :=
  (Associates.mk a.evalKernel).count
    (Associates.mk (Ideal.span {a.addressedLoad})).factors

/-- The explicit maximal kernel is prime. -/
theorem evalKernel_isPrime
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.evalKernel.IsPrime :=
  a.evalKernel_isMaximal.isPrime

private theorem evalKernel_prime
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    Prime a.evalKernel :=
  Ideal.prime_of_isPrime a.evalKernel_ne_bot a.evalKernel_isPrime

/-- Exact universal property of the ideal-theoretic kernel multiplicity:
the `k`-th kernel power divides the addressed-load principal ideal exactly
when `k` does not exceed the factor count. -/
theorem evalKernel_pow_dvd_span_addressedLoad_iff
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q)
    (k : ℕ) :
    a.evalKernel ^ k ∣ Ideal.span {a.addressedLoad} ↔
      k ≤ a.evalKernelMultiplicity := by
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact
    Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr a.span_addressedLoad_ne_bot)
      (Associates.irreducible_mk.mpr a.evalKernel_prime.irreducible)

/-- Element-membership form of the exact multiplicity universal property. -/
theorem addressedLoad_mem_evalKernel_pow_iff
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q)
    (k : ℕ) :
    a.addressedLoad ∈ a.evalKernel ^ k ↔
      k ≤ a.evalKernelMultiplicity := by
  rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le]
  exact a.evalKernel_pow_dvd_span_addressedLoad_iff k

/-- The selected kernel occurs at least once in the addressed load. -/
theorem one_le_evalKernelMultiplicity
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    1 ≤ a.evalKernelMultiplicity := by
  rw [← a.evalKernel_pow_dvd_span_addressedLoad_iff 1,
    pow_one, Ideal.dvd_iff_le]
  exact a.span_addressedLoad_le_evalKernel

/-- The kernel power at its exact factor count divides the addressed-load
principal ideal. -/
theorem evalKernel_pow_multiplicity_dvd_span_addressedLoad
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.evalKernel ^ a.evalKernelMultiplicity ∣
      Ideal.span {a.addressedLoad} :=
  (a.evalKernel_pow_dvd_span_addressedLoad_iff
    a.evalKernelMultiplicity).mpr le_rfl

/-- The next kernel power no longer divides the addressed-load principal
ideal. -/
theorem evalKernel_pow_multiplicity_succ_not_dvd_span_addressedLoad
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    ¬a.evalKernel ^ (a.evalKernelMultiplicity + 1) ∣
      Ideal.span {a.addressedLoad} := by
  rw [a.evalKernel_pow_dvd_span_addressedLoad_iff]
  omega

/-- Taking exact ideal norms of the maximal kernel power proves that the
corresponding rational-prime power divides the selected routing cell. -/
theorem prime_pow_evalKernelMultiplicity_dvd_addressedCell
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    q ^ a.evalKernelMultiplicity ∣ a.family.cell p := by
  have h :=
    map_dvd Ideal.absNorm
      a.evalKernel_pow_multiplicity_dvd_span_addressedLoad
  simpa only [map_pow, a.absNorm_evalKernel,
    a.absNorm_span_addressedLoad] using h

/-- The explicit prime-kernel multiplicity is bounded above by the ordinary
`q`-adic exponent of the addressed integer cell. -/
theorem evalKernelMultiplicity_le_padicValNat_addressedCell
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.evalKernelMultiplicity ≤
      padicValNat q (a.family.cell p) := by
  letI : Fact q.Prime := ⟨a.prime⟩
  exact
    (padicValNat_dvd_iff_le a.addressedCell_ne_zero).mp
      a.prime_pow_evalKernelMultiplicity_dvd_addressedCell

/-- Exact obstruction to upgrading the ideal multiplicity bound to equality:
the equality holds precisely when the next rational-prime power does not
still divide the integer cell.

This deliberately does not identify `(addressedLoad)` with `evalKernel`;
higher kernel multiplicity remains possible. -/
theorem evalKernelMultiplicity_eq_padicValNat_addressedCell_iff
    (a : RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress p q) :
    a.evalKernelMultiplicity =
        padicValNat q (a.family.cell p) ↔
      ¬q ^ (a.evalKernelMultiplicity + 1) ∣
        a.family.cell p := by
  letI : Fact q.Prime := ⟨a.prime⟩
  rw [padicValNat_dvd_iff_le a.addressedCell_ne_zero]
  constructor
  · intro heq hsucc
    omega
  · intro hnext
    have hle :=
      a.evalKernelMultiplicity_le_padicValNat_addressedCell
    omega

end RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

end

end DkMath.FLT.Seven
