/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.NumberTheory.CyclotomicQRProduct
import DkMath.NumberTheory.CyclotomicQRUniversalTransport
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportApiAudit"

/-! Phase-24 pins the smallest carrier and the exact quotient/anchor APIs.
The audit intentionally includes both the universal quotient operations and
the characteristic-zero comparison operations used by an injectivity proof. -/

#check AdjoinRoot
#check AdjoinRoot.root
#check AdjoinRoot.mk
#check AdjoinRoot.lift
#check AdjoinRoot.lift_mk
#check AdjoinRoot.lift_root
#check AdjoinRoot.lift_of
#check AdjoinRoot.lift_comp_of
#check AdjoinRoot.isRoot_root
#check AdjoinRoot.mk_eq_mk
#check AdjoinRoot.modByMonicHom
#check CyclotomicRing

#check Polynomial.cyclotomic.irreducible
#check Polynomial.isRoot_cyclotomic_iff
#check IsPrimitiveRoot.isRoot_cyclotomic
#check IsPrimitiveRoot.adjoinEquivRingOfIntegers
#check IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
#check IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
#check Polynomial.map_cyclotomic
#check Polynomial.eval₂_map
#check Polynomial.eval₂_at_apply
#check Polynomial.modByMonic
#check Polynomial.dvd_modByMonic_sub
#check Polynomial.modByMonic_eq_zero_iff_dvd
#check Polynomial.natDegree_modByMonic_lt
#check Polynomial.natDegree_cyclotomic
#check Polynomial.degree_cyclotomic
#check Polynomial.degree_sub_le
#check Polynomial.degree_map_eq_of_injective
#check Polynomial.map_injective
#check Polynomial.eq_zero_of_dvd_of_degree_lt
#check Polynomial.dvd_iff_isRoot
#check minpoly.dvd

#check MvPolynomial.map
#check MvPolynomial.eval
#check map_prod
#check Finset.prod_eq_zero_iff
#check IsPrimitiveRoot.pow_inj
#check ZMod.intCast_zmod_eq_zero_iff_dvd
#check CharP.cast_eq_zero_iff

namespace DkMath.NumberTheory.CyclotomicQRUniversalTransport

open Polynomial

noncomputable section

example {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [NeZero (p : L)] [Fact p.Prime]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (specializePrimitiveRoot ζ hζ) := by
  let f : Polynomial ℤ := Polynomial.cyclotomic p ℤ
  have hf : f.Monic := by
    exact Polynomial.cyclotomic.monic p ℤ
  have hf1 : f ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_cyclotomic, Polynomial.natDegree_one,
      Nat.totient_prime (Fact.out : Nat.Prime p)] at hdeg
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  intro x y hxy
  let r : Polynomial ℤ := AdjoinRoot.modByMonicHom hf x
  let s : Polynomial ℤ := AdjoinRoot.modByMonicHom hf y
  have hx : AdjoinRoot.mk f r = x := by
    exact AdjoinRoot.mk_leftInverse hf x
  have hy : AdjoinRoot.mk f s = y := by
    exact AdjoinRoot.mk_leftInverse hf y
  have hev : Polynomial.eval₂ (Int.castRingHom L) ζ r =
      Polynomial.eval₂ (Int.castRingHom L) ζ s := by
    rw [← hx, ← hy] at hxy
    simpa [r, s, f, specializePrimitiveRoot, specializeRoot] using hxy
  have hroot : Polynomial.aeval ζ
      ((r - s).map (Int.castRingHom ℚ)) = 0 := by
    change Polynomial.eval₂ (algebraMap ℚ L) ζ
      ((r - s).map (Int.castRingHom ℚ)) = 0
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ℚ L).comp (Int.castRingHom ℚ) =
        Int.castRingHom L := by
      ext z
      simp
    rw [hcomp]
    simpa [sub_eq_add_neg] using sub_eq_zero.mpr hev
  have hdiv_min : minpoly ℚ ζ ∣
      (r - s).map (Int.castRingHom ℚ) := by
    exact minpoly.dvd ℚ ζ hroot
  have hdiv : Polynomial.cyclotomic p ℚ ∣
      (r - s).map (Int.castRingHom ℚ) := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (Fact.out : Nat.Prime p).pos)] at hdiv_min
    exact hdiv_min
  have hrdeg : r.degree < f.degree := by
    induction x using AdjoinRoot.induction_on with
    | ih q =>
      change (q %ₘ f).degree < f.degree
      exact Polynomial.degree_modByMonic_lt q hf
  have hsdeg : s.degree < f.degree := by
    induction y using AdjoinRoot.induction_on with
    | ih q =>
      change (q %ₘ f).degree < f.degree
      exact Polynomial.degree_modByMonic_lt q hf
  have hmapdiv : (Polynomial.map (Int.castRingHom ℚ) f) ∣
      (r - s).map (Int.castRingHom ℚ) := by
    simpa [f, Polynomial.map_cyclotomic] using hdiv
  have hmapdeg : ((r - s).map (Int.castRingHom ℚ)).degree <
      (Polynomial.map (Int.castRingHom ℚ) f).degree := by
    rw [Polynomial.degree_map_eq_of_injective Int.cast_injective,
      Polynomial.degree_map_eq_of_injective Int.cast_injective]
    exact (Polynomial.degree_sub_le r s).trans_lt (max_lt hrdeg hsdeg)
  have hmapzero : (r - s).map (Int.castRingHom ℚ) = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hmapdiv hmapdeg
  have hzero : r - s = 0 := by
    apply (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    simpa using hmapzero
  calc
    x = AdjoinRoot.mk f r := hx.symm
    _ = AdjoinRoot.mk f s := by
      apply AdjoinRoot.mk_eq_mk.mpr
      rw [hzero]
      exact dvd_zero f
    _ = y := hy

end

end DkMath.NumberTheory.CyclotomicQRUniversalTransport
