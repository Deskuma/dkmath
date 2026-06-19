/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.Basic

#print "file: DkMath.Analysis.GapGN"

/-!
# Gap-normalized difference kernel

`gapGN d base delta` is the analysis-facing argument order for the existing
cosmic-formula kernel `GN d delta base`.

It records the exact factor left after extracting `delta` from
`(base + delta)^d - base^d`.
-/

namespace DkMath.Analysis

/--
The exact power-difference kernel with analysis-oriented argument order.

The existing cosmic-formula `GN` takes the boundary difference first and the
base second. The analysis layer presents the base before the observed change.
-/
abbrev gapGN {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) : R :=
  DkMath.CosmicFormulaBinom.GN d delta base

/-- `gapGN` is the existing cosmic-formula `GN` with its last two arguments swapped. -/
theorem gapGN_eq_GN {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) :
    gapGN d base delta = DkMath.CosmicFormulaBinom.GN d delta base := rfl

/--
Exact additive power decomposition.

This is the subtraction-free form of the gap correction identity and therefore
holds over every commutative semiring.
-/
theorem pow_add_eq_pow_add_delta_mul_gapGN
    {R : Type*} [CommSemiring R] (d : ℕ) (base delta : R) :
    (base + delta) ^ d = base ^ d + delta * gapGN d base delta := by
  simpa [gapGN, add_comm] using
    (DkMath.CosmicFormulaBinom.add_pow_gap_factor (R := R) d delta base)

/--
Exact factorization of a power difference.

No limit, approximation, derivative, or omitted higher-order term occurs.
-/
theorem pow_add_sub_pow_eq_delta_mul_gapGN
    {R : Type*} [CommRing R] (d : ℕ) (base delta : R) :
    (base + delta) ^ d - base ^ d = delta * gapGN d base delta := by
  rw [pow_add_eq_pow_add_delta_mul_gapGN]
  ring

end DkMath.Analysis
