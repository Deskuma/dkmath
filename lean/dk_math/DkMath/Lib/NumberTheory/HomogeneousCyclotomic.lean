/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailCyclotomic
import Mathlib.Algebra.Polynomial.Homogenize

#print "file: DkMath.Lib.NumberTheory.HomogeneousCyclotomic"

/-!
# Homogeneous cyclotomic evaluation and its historical shifted spelling

[DkMath.Lib] GN-LIB-006b. The homogeneous evaluator is a polynomial value,
not an application-specific norm carrier. We retain the old CFBRC function
names in this neutral owner so existing users keep the exact same definitions.
There is no import of CFBRC, Zsigmondy or an FLT application.

The public Lib interface takes the two coordinates a,b directly. Its value
is the homogenization at (a,b); the historical shifted interface takes gap x
and anchor u, hence evaluates at (x+u,u). The bridges below record this
coordinate change without division or a nonzero-gap assumption.
-/

noncomputable section

namespace DkMath.CFBRC

/-- [DkMath.Lib] GN-LIB-006b: promoted from `DkMath.CFBRC.CyclotomicProduct`.
The historical name, public type and definition/proof body are preserved.
The mathematical owner now depends only on Mathlib and neutral Lib kernels.

 円分多項式 `Φ_m` の単変数評価器（係数は `ℤ` から射影）。 -/
@[simp] def cyclotomicEval {R : Type _} [CommRing R]
    (m : ℕ) (X : R) : R :=
  Polynomial.eval₂ (Int.castRingHom R) X (Polynomial.cyclotomic m ℤ)

/-- [DkMath.Lib] GN-LIB-006b: promoted from `DkMath.CFBRC.CyclotomicProduct`.
The historical name, public type and definition/proof body are preserved.
The mathematical owner now depends only on Mathlib and neutral Lib kernels.


shifted 版の局所評価器（`u=1` で plain eval に戻る形）。

整数円分多項式の元の次数 `natDegree (cyclotomic m ℤ)` で斉次化し、
座標 `(x+u,u)` へ評価する。合成数次数も含むため、斉次次数を常に `m-1` とは置かない。
-/
@[simp] def cyclotomicShiftedEval {R : Type _} [CommRing R]
    (m : ℕ) (x u : R) : R :=
  let pR : Polynomial R := (Polynomial.cyclotomic m ℤ).map (Int.castRingHom R)
  MvPolynomial.eval ![x + u, u] (pR.homogenize (Polynomial.cyclotomic m ℤ).natDegree)

/-- [DkMath.Lib] GN-LIB-006b: promoted from `DkMath.CFBRC.CyclotomicProduct`.
The historical name, public type and definition/proof body are preserved.
The mathematical owner now depends only on Mathlib and neutral Lib kernels.

 `u ≠ 0` のとき、局所 shifted evaluator は scaled plain evaluator に一致する。 -/
theorem cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow
    {R : Type _} [Field R] (m : ℕ) (x u : R) (hu : u ≠ 0) :
    cyclotomicShiftedEval m x u =
      cyclotomicEval m ((x + u) / u) * u ^ (Polynomial.cyclotomic m ℤ).natDegree := by
  have hmain := Polynomial.eval_homogenize
    (p := (Polynomial.cyclotomic m ℤ).map (Int.castRingHom R))
    (n := (Polynomial.cyclotomic m ℤ).natDegree)
    (hn := by
      simpa using
        (Polynomial.natDegree_map_le (p := Polynomial.cyclotomic m ℤ) (f := Int.castRingHom R)))
    (x := ![x + u, u]) hu
  unfold cyclotomicShiftedEval
  simp [cyclotomicEval, Polynomial.eval₂_eq_eval_map] at hmain ⊢
  simpa using hmain

end DkMath.CFBRC

namespace DkMath.Lib.NumberTheory

/-- [DkMath.Lib] Homogeneous evaluation at the actual coordinates a,b.
The shifted spelling is reused at gap a-b and anchor b. The following explicit
homogenization theorem identifies the value without inventing another carrier.
Zero coordinates, equal coordinates, and degree zero remain meaningful. -/
def homogeneousCyclotomicEval {R : Type*} [CommRing R] (n : ℕ) (a b : R) : R :=
  DkMath.CFBRC.cyclotomicShiftedEval n (a - b) b

/-- [DkMath.Lib] The direct-coordinate interface is definitionally the old
shifted function at (a-b,b). This is the compatibility boundary for old types. -/
theorem homogeneousCyclotomicEval_eq_shifted_sub
    {R : Type*} [CommRing R] (n : ℕ) (a b : R) :
    homogeneousCyclotomicEval n a b = DkMath.CFBRC.cyclotomicShiftedEval n (a - b) b := rfl

/-- [DkMath.Lib] A shifted input (x,u) means actual coordinates (x+u,u).
The proof uses only additive cancellation and does not require u or x nonzero. -/
theorem cyclotomicShiftedEval_eq_homogeneousCyclotomicEval
    {R : Type*} [CommRing R] (n : ℕ) (x u : R) :
    DkMath.CFBRC.cyclotomicShiftedEval n x u = homogeneousCyclotomicEval n (x + u) u := by
  simp only [homogeneousCyclotomicEval, add_sub_cancel_right]

/-- [DkMath.Lib] The Lib ordinary evaluator and its historical CFBRC spelling
are definitionally equal, in every commutative ring. -/
theorem cfbRC_cyclotomicEval_eq_lib
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    DkMath.CFBRC.cyclotomicEval n a = cyclotomicEval n a := rfl

/-- [DkMath.Lib] The direct-coordinate value is exactly Mathlib homogenization
of the mapped integer cyclotomic polynomial, at its original integer degree.
This polynomial equation supplies the semantic interpretation of the alias. -/
theorem homogeneousCyclotomicEval_eq_eval_homogenize
    {R : Type*} [CommRing R] (n : ℕ) (a b : R) :
    homogeneousCyclotomicEval n a b = MvPolynomial.eval ![a, b]
      (((Polynomial.cyclotomic n ℤ).map (Int.castRingHom R)).homogenize
        (Polynomial.cyclotomic n ℤ).natDegree) := by
  simp only [homogeneousCyclotomicEval, DkMath.CFBRC.cyclotomicShiftedEval, sub_add_cancel]

/-- [DkMath.Lib] Field dehomogenization is available only at nonzero b.
The exponent is the original cyclotomic degree; no gap is cancelled. -/
theorem homogeneousCyclotomicEval_eq_eval_div_mul_pow
    {R : Type*} [Field R] (n : ℕ) (a b : R) (hb : b ≠ 0) :
    homogeneousCyclotomicEval n a b =
      cyclotomicEval n (a / b) * b ^ (Polynomial.cyclotomic n ℤ).natDegree := by
  simpa only [homogeneousCyclotomicEval, sub_add_cancel, cfbRC_cyclotomicEval_eq_lib] using
    DkMath.CFBRC.cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow n (a - b) b hb

end DkMath.Lib.NumberTheory
