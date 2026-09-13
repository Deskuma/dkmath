/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRProduct
import DkMath.NumberTheory.CyclotomicQRGaloisAction
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.AdjoinRoot

#print "file: DkMath.NumberTheory.CyclotomicQRUniversalTransport"

namespace DkMath.NumberTheory.CyclotomicQRUniversalTransport

open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction

noncomputable section

/-! ## The universal integral carrier -/

/-- The integral cyclotomic quotient carrying a universal primitive `p`-th
root. -/
abbrev universalCyclotomicCarrier (p : ℕ) :=
  AdjoinRoot (Polynomial.cyclotomic p ℤ)

/-- The universal cyclotomic root. -/
def zetaU (p : ℕ) : universalCyclotomicCarrier p :=
  AdjoinRoot.root (Polynomial.cyclotomic p ℤ)

/-- A QR/QNR root factor over the universal commutative ring. -/
def universalRootFactorPoly
    {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    MvPolynomial (Fin 2) (universalCyclotomicCarrier p) :=
  MvPolynomial.X 0 -
    MvPolynomial.C ((zetaU p) ^ a.val) * MvPolynomial.X 1

/-- The product of the universal quadratic-residue factors. -/
def universalQrFactorPoly
    (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 2) (universalCyclotomicCarrier p) :=
  (qrFinset p).prod (fun a => universalRootFactorPoly a)

/-- The product of the universal quadratic-nonresidue factors. -/
def universalQnrFactorPoly
    (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 2) (universalCyclotomicCarrier p) :=
  (qnrFinset p).prod (fun a => universalRootFactorPoly a)

/-- The universal QR/QNR sum corresponding to `Rpoly`. -/
def universalRpoly
    (p : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin 2) (universalCyclotomicCarrier p) :=
  universalQrFactorPoly p + universalQnrFactorPoly p

/-! ## Specialization maps -/

private theorem cyclotomic_eval₂_intCast_eq_zero
    {K : Type*} [CommRing K] [IsDomain K]
    {p : ℕ} [NeZero (p : K)] {ξ : K}
    (hξ : (Polynomial.cyclotomic p K).IsRoot ξ) :
    Polynomial.eval₂ (Int.castRingHom K) ξ
        (Polynomial.cyclotomic p ℤ) = 0 := by
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hξ

/-- The quotient specialization determined by a root of the cyclotomic
polynomial. -/
def specializeRoot
    {K : Type*} [CommRing K] [IsDomain K]
    (p : ℕ) [NeZero (p : K)] (ξ : K)
    (hξ : (Polynomial.cyclotomic p K).IsRoot ξ) :
    universalCyclotomicCarrier p →+* K :=
  AdjoinRoot.lift (Int.castRingHom K) ξ
    (cyclotomic_eval₂_intCast_eq_zero hξ)

@[simp]
theorem specializeRoot_zeta
    {K : Type*} [CommRing K] [IsDomain K]
    {p : ℕ} [NeZero (p : K)] (ξ : K)
    (hξ : (Polynomial.cyclotomic p K).IsRoot ξ) :
    specializeRoot p ξ hξ (zetaU p) = ξ := by
  exact AdjoinRoot.lift_root (cyclotomic_eval₂_intCast_eq_zero hξ)

/-- The specialization map associated with a primitive root. -/
def specializePrimitiveRoot
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [NeZero (p : K)]
    (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    universalCyclotomicCarrier p →+* K :=
  specializeRoot p ξ (hξ.isRoot_cyclotomic (Fact.out : Nat.Prime p).pos)

@[simp]
theorem specializePrimitiveRoot_zeta
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [NeZero (p : K)]
    (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    specializePrimitiveRoot ξ hξ (zetaU p) = ξ := by
  exact specializeRoot_zeta ξ (hξ.isRoot_cyclotomic (Fact.out : Nat.Prime p).pos)

/-! ## The characteristic-zero anchor -/

/-- The primitive-root specialization into a characteristic-zero field. -/
def charZeroAnchorMap
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime] (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    universalCyclotomicCarrier p →+* L := by
  letI : NeZero (p : L) := NeZero.of_faithfulSMul ℚ L p
  exact specializePrimitiveRoot ζ hζ

@[simp]
theorem charZeroAnchorMap_zeta
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime] {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    charZeroAnchorMap ζ hζ (zetaU p) = ζ := by
  letI : NeZero (p : L) := NeZero.of_faithfulSMul ℚ L p
  exact specializePrimitiveRoot_zeta ζ hζ

/-- The integral cyclotomic quotient is separated by every characteristic-zero
primitive-root specialization. -/
theorem specializePrimitiveRoot_injective
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [NeZero (p : L)] [Fact p.Prime]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (specializePrimitiveRoot ζ hζ) := by
  let f : Polynomial ℤ := Polynomial.cyclotomic p ℤ
  have hf : f.Monic := by
    exact Polynomial.cyclotomic.monic p ℤ
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

/-- Injectivity of the characteristic-zero anchor. -/
theorem charZeroAnchorMap_injective
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime] {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (charZeroAnchorMap ζ hζ) := by
  letI : NeZero (p : L) := NeZero.of_faithfulSMul ℚ L p
  exact specializePrimitiveRoot_injective hζ

/-! ## Specialization away from the cyclotomic prime -/

/-- A prime different from the characteristic remains nonzero as a scalar. -/
theorem neZero_primeCast_of_charPrime
    {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hpq : q ≠ p) : NeZero (p : K) := by
  refine ⟨?_⟩
  intro hzero
  have hdiv : q ∣ p := (CharP.cast_eq_zero_iff K q p).mp hzero
  have heq : q = p :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q)
      (Fact.out : Nat.Prime p)).mp hdiv
  exact hpq heq

/-- The universal carrier specialized at a primitive `p`-th root in
characteristic `q`, where `q` is a different prime. -/
def positiveCharSpecializeRoot
    {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hpq : q ≠ p) (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    universalCyclotomicCarrier p →+* K := by
  letI : NeZero (p : K) := neZero_primeCast_of_charPrime hpq
  exact specializePrimitiveRoot ξ hξ

@[simp]
theorem positiveCharSpecializeRoot_zeta
    {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hpq : q ≠ p) (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    positiveCharSpecializeRoot hpq ξ hξ (zetaU p) = ξ := by
  letI : NeZero (p : K) := neZero_primeCast_of_charPrime hpq
  exact specializePrimitiveRoot_zeta ξ hξ

/-! ## Functoriality of the QR/QNR factors -/

theorem map_universalRootFactorPoly
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime]
    (f : universalCyclotomicCarrier p →+* K) (ξ : K)
    (hf : f (zetaU p) = ξ) (a : ZMod p) :
    MvPolynomial.map f (universalRootFactorPoly a) =
      rootFactorPoly (p := p) ξ a := by
  rw [universalRootFactorPoly, rootFactorPoly]
  simp only [map_sub, MvPolynomial.map_X, map_mul, MvPolynomial.map_C,
    map_pow, hf]

theorem map_universalQrFactorPoly
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime]
    (f : universalCyclotomicCarrier p →+* K) (ξ : K)
    (hf : f (zetaU p) = ξ) :
    MvPolynomial.map f (universalQrFactorPoly p) =
      qrFactorPoly (p := p) ξ := by
  classical
  simp only [universalQrFactorPoly, map_prod]
  congr 1
  funext a
  exact map_universalRootFactorPoly f ξ hf a

theorem map_universalQnrFactorPoly
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime]
    (f : universalCyclotomicCarrier p →+* K) (ξ : K)
    (hf : f (zetaU p) = ξ) :
    MvPolynomial.map f (universalQnrFactorPoly p) =
      qnrFactorPoly (p := p) ξ := by
  classical
  simp only [universalQnrFactorPoly, map_prod]
  congr 1
  funext a
  exact map_universalRootFactorPoly f ξ hf a

theorem map_universalRpoly
    {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime]
    (f : universalCyclotomicCarrier p →+* K) (ξ : K)
    (hf : f (zetaU p) = ξ) :
    MvPolynomial.map f (universalRpoly p) =
      Rpoly (p := p) ξ := by
  rw [universalRpoly, map_add, map_universalQrFactorPoly f ξ hf,
    map_universalQnrFactorPoly f ξ hf, Rpoly]

theorem map_universalRpoly_positiveChar
    {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hpq : q ≠ p) (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    MvPolynomial.map (positiveCharSpecializeRoot hpq ξ hξ)
        (universalRpoly p) = Rpoly (p := p) ξ := by
  exact map_universalRpoly (positiveCharSpecializeRoot hpq ξ hξ) ξ
    (positiveCharSpecializeRoot_zeta hpq ξ hξ)

end

end DkMath.NumberTheory.CyclotomicQRUniversalTransport
