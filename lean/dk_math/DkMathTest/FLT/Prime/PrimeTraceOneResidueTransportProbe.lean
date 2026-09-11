/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaussNormalization

#print "file: DkMathTest.FLT.Prime.PrimeTraceOneResidueTransportProbe"

open DkMath.NumberTheory.CyclotomicQRGaussNormalization

/-! Signature regression for the positive-characteristic Gauss input.  The
probe deliberately leaves the primitive root abstract: construction of the
root and, separately, universal packet transport are the next obligations. -/

example {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : q ≠ p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    quadraticGauss ζ hζ ≠ 0 := by
  exact quadraticGauss_ne_zero_of_char_ne hp2 hq2 hpq ζ hζ

/-! The intended Phase-23 residue field is covered by the same generic
signature once an algebraic closure and a primitive root witness are supplied.
No such witness is smuggled into the packet API here. -/

example {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : q ≠ p)
    (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    quadraticGauss ξ hξ ≠ 0 :=
  quadraticGauss_ne_zero_of_char_ne hp2 hq2 hpq ξ hξ
