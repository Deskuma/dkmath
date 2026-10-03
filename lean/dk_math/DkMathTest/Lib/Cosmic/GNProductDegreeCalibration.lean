/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNProductDegree
import DkMath.NumberTheory.GNDegreeFactorization
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace DkMathTest.GNProductDegree

open DkMath.CosmicFormula

/-- The canonical GN vocabulary is definitionally the public theorem's tail. -/
theorem canonical_composition {R : Type*} [CommSemiring R]
    (a b : ℕ) (x u : R) :
    GN (a * b) x u = GN a x u * GN b (x * GN a x u) (u ^ a) :=
  GN_mul_degree a b x u

/-- Zero gap is included for arbitrary degrees and every coefficient semiring. -/
theorem zero_gap {R : Type*} [CommSemiring R] (a b : ℕ) (u : R) :
    GN (a * b) 0 u = GN a 0 u * GN b (0 * GN a 0 u) (u ^ a) :=
  GN_mul_degree a b 0 u

example : GN (2 * 3) (0 : ℕ) 2 = 192 := by
  norm_num [GN, GTail, Finset.sum_range_succ]

example (b : ℕ) (x u : ℤ) :
    GN (0 * b) x u = GN 0 x u * GN b (x * GN 0 x u) (u ^ 0) :=
  GN_mul_degree 0 b x u

example (a : ℕ) (x u : ℕ) :
    GN (a * 0) x u = GN a x u * GN 0 (x * GN a x u) (u ^ a) :=
  GN_mul_degree a 0 x u

/-- The gap is a nonzero zero divisor, so cancellation in the target is invalid. -/
theorem zero_divisor_gap :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 ∧
      GN (2 * 3) (2 : ZMod 4) 1 =
        GN 2 2 1 * GN 3 (2 * GN 2 2 1) (1 ^ 2) := by
  refine ⟨by decide, by decide, GN_mul_degree 2 3 2 1⟩

example : GN (2 * 3) (2 : ZMod 4) 1 = 0 := by
  decide

/-- The original Nat endpoint and its original positive-gap signature remain usable. -/
example {a b x u : ℕ} (hx : 0 < x) :
    DkMath.CosmicFormulaBinom.GN (a * b) x u =
      DkMath.CosmicFormulaBinom.GN a x u *
        DkMath.CosmicFormulaBinom.GN b
          (x * DkMath.CosmicFormulaBinom.GN a x u) (u ^ a) :=
  DkMath.NumberTheory.GN_mul_degree hx

end DkMathTest.GNProductDegree
