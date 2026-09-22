/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Basic
import DkMath.NumberTheory.CyclotomicQRProduct
import Mathlib.Analysis.Complex.Basic

#print "file: DkMath.CFBRC.CyclotomicNorm"

/-!
# CFBRC cyclotomic carrier and complex norm bridge

This module keeps the complete gap factor together with the homogeneous
cyclotomic shell.  It is the first norm-aware layer requested by the FLT7
generalization handoff:

```text
gap * GN
  = gap * homogeneous cyclotomic shell
  = power difference.
```

The root-product carrier is independent of any nonzero-gap cancellation.  Its
individual complex factors also carry the standard `Complex.normSq` norm.
-/

namespace DkMath.CFBRC

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.CyclotomicQRProduct

noncomputable section

/-- The complete nonzero-root cyclotomic product in gap/base coordinates. -/
def cyclotomicRootProduct
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (x u : K) : K :=
  (nonzeroResidues p).prod (fun a => rootFactor ζ a (x + u) u)

/-- The complete root product is the homogeneous cyclotomic shell. -/
theorem cyclotomicRootProduct_eq_shell
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct ζ x u = GTailCyclotomicShell p x u := by
  simpa [cyclotomicRootProduct, GTailCyclotomicShell] using
    nonzeroRoot_product_eq_shell ζ hζ (x + u) u

/-- The complete root product is exactly the one-gap `GTail` kernel. -/
theorem cyclotomicRootProduct_eq_GTail_one
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct ζ x u = GTail p 1 x u := by
  rw [cyclotomicRootProduct_eq_shell ζ hζ]
  exact (GTail_one_eq_GTailCyclotomicShell p x u).symm

/-- The complete root product is exactly the canonical `GN` kernel. -/
theorem cyclotomicRootProduct_eq_GN
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    cyclotomicRootProduct ζ x u = GN p x u := by
  exact cyclotomicRootProduct_eq_GTail_one ζ hζ x u

/--
The complete gap times the cyclotomic root product is the original power
difference.  This keeps the boundary factor that is lost when one looks only
at the cyclotomic quotient.
-/
theorem gap_mul_cyclotomicRootProduct_eq_sub_pow
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (x u : K) :
    x * cyclotomicRootProduct ζ x u = (x + u) ^ p - u ^ p := by
  rw [cyclotomicRootProduct_eq_GTail_one ζ hζ]
  rw [eq_sub_iff_add_eq]
  exact (add_pow_eq_mul_GTail_one_add_gap p x u).symm

/-- One complex cyclotomic factor paired with its conjugate is its norm square. -/
theorem complex_rootFactor_mul_conj_eq_normSq
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (a : ZMod p) (x u : ℂ) :
    rootFactor ζ a (x + u) u *
        Complex.conj (rootFactor ζ a (x + u) u) =
      Complex.normSq (rootFactor ζ a (x + u) u) := by
  exact Complex.mul_conj _

/-- The complex norm square of the full carrier is the norm square of `GN`. -/
theorem complex_normSq_cyclotomicRootProduct_eq_GN
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (x u : ℂ) :
    Complex.normSq (cyclotomicRootProduct ζ x u) =
      Complex.normSq (GN p x u) := by
  rw [cyclotomicRootProduct_eq_GN ζ hζ]

/--
The complex norm square also preserves the complete gap/product identity.
This is deliberately stated before any conjugate-pair half-product
compression.
-/
theorem complex_normSq_gap_mul_cyclotomicRootProduct_eq_sub_pow
    {p : ℕ} [Fact p.Prime]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (x u : ℂ) :
    Complex.normSq (x * cyclotomicRootProduct ζ x u) =
      Complex.normSq ((x + u) ^ p - u ^ p) := by
  rw [gap_mul_cyclotomicRootProduct_eq_sub_pow ζ hζ]

end

end DkMath.CFBRC
