/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CosmicFormula.SquareGnomon"

/-!
# Square Gnomon

A square Gnomon is the growth layer taking one square Core to the next square
while the primitive Gap unit is held fixed. Its canonical algebra is

    `Gnomon(x, u) = (x + u)^2 - x^2 = u * (2 * x + u)`.

For subtraction-free owners, the product `u * (2 * x + u)`, equivalently the
degree-two GN form, is primary. This is the argument-swapped degree-two
GN/GTail kernel:

    `Gnomon(x, u) = u * GN₂(u, x)`,

where the canonical GN is the GTail `r = 1` specialization
GTail 2 1 u x. The existing Cosmic Body and the Gnomon are dual degree-two
boundary products:

    `BodyN 2 x u = x * GN₂(x, u)`,
    `Gnomon(x, u) = u * GN₂(u, x)`.

With fixed `GapN 2 u = u^2`, the BodyN sequence grows by successive Gnomon
layers. Thus the intended semantics is Body growth with Gap preserved, not
Gap growth. For `u = 1`, the Body values are

    `0 --(+3)--> 3 --(+5)--> 8 --(+7)--> 15 ...`

while the same fixed Gap produces Big values

    `1 ----------> 4 ----------> 9 ----------> 16 ...`

This file is a future candidate for promotion or refactoring into a generic
DkMath.Lib.Gnomon-style owner after the API stabilizes; no promotion is
performed here. A future resolution refinement may subdivide one coarse
transition into finer Gnomon steps while preserving the same endpoint square
transition after normalization or projection. Raw fine coordinates scale by
the square of the resolution factor, and projection divides that scale back
out. In particular, raw local `Gap = v^2` cells must not be claimed to add
directly to the coarse `u^2` Gap.

The refinement frontier is intentionally only documented here. A coarse
transition `x^2` to `(x + u)^2` can later be telescoped through fine anchors
`x + (j / k) * u`. In integer visualization, scaling by k gives
`(k*x)^2 to (k*x + k)^2` with normalized projection by `k^2`. For example,
`1 to 4` corresponds at endpoint scale `k = 3 to 9 to 36`, with resolved chain
`9 to 16 to 25 to 36`; and 4 to 9 corresponds to
`36 to 49 to 64 to 81`, projecting to
`4 to 49/9 to 64/9 to 9`. No raw-gap invariance claim is made by these
examples.

The existing Collatz owner already contains the natural unit specialization
OddGnomonLayer and its unit-step telescoping band. This generic algebraic
owner deliberately does not import DkMath.Collatz.GnomonEvaluation or
duplicate that owner.
-/

namespace DkMath.CosmicFormula.SquareGnomon

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom

variable {R : Type*} [CommSemiring R]

/-- Degree-two GN kernel read in the Gnomon orientation. -/
abbrev squareGnomonKernel (x u : R) : R :=
  DkMath.CosmicFormula.GN R u x 2

/-- Square-growth Gnomon layer at anchor x with fixed unit u. -/
abbrev squareGnomon (x u : R) : R :=
  u * squareGnomonKernel x u

/-- The square Gnomon kernel is the canonical degree-two GN/GTail bridge. -/
theorem squareGnomonKernel_eq_GTail (x u : R) :
    squareGnomonKernel x u = DkMath.CosmicFormula.GTail 2 1 u x := by
  rfl

/-- The argument-swapped degree-two GN kernel has the explicit form 2*x + u. -/
theorem squareGnomonKernel_eq_two_mul_add (x u : R) :
    squareGnomonKernel x u = 2 * x + u := by
  rw [squareGnomonKernel_eq_GTail]
  rw [DkMath.CosmicFormula.GTail_one_eq_sum]
  norm_num [Finset.sum_range_succ]

/-- The square Gnomon has the subtraction-free normal form u * (2*x + u). -/
theorem squareGnomon_eq_mul_two_mul_add (x u : R) :
    squareGnomon x u = u * (2 * x + u) := by
  rw [squareGnomon, squareGnomonKernel_eq_two_mul_add]

/-- Adding a square Gnomon advances the Core to the next square. -/
theorem core_add_squareGnomon_eq_next_square (x u : R) :
    x ^ 2 + squareGnomon x u = (x + u) ^ 2 := by
  rw [squareGnomon_eq_mul_two_mul_add]
  ring

/--
The degree-two Body grows by the Gnomon at the new anchor while the Gap unit
remains fixed.
-/
theorem bodyN_two_add_squareGnomon (x u : R) :
    BodyN 2 (x + u) u =
      BodyN 2 x u + squareGnomon (x + u) u := by
  simp only [BodyN]
  rw [GN_eq_sum, GN_eq_sum, squareGnomon, squareGnomonKernel_eq_two_mul_add]
  norm_num [Finset.sum_range_succ]; ring

/-- The Big step exposes Body growth followed by the unchanged Gap. -/
theorem bigN_two_step_fixedGap (x u : R) :
    BigN 2 (x + u) u =
      (BodyN 2 x u + squareGnomon (x + u) u) + GapN 2 u := by
  calc
    BigN 2 (x + u) u = BodyN 2 (x + u) u + GapN 2 u :=
      DkMath.CosmicFormulaBinom.cosmic_id_csr 2 (x + u) u
    _ = (BodyN 2 x u + squareGnomon (x + u) u) + GapN 2 u := by
      rw [bodyN_two_add_squareGnomon]

/-- The Gnomon kernel grows by the fixed increment 2*u. -/
theorem squareGnomonKernel_step (x u : R) :
    squareGnomonKernel (x + u) u =
      squareGnomonKernel x u + 2 * u := by
  rw [squareGnomonKernel_eq_two_mul_add, squareGnomonKernel_eq_two_mul_add]
  ring

/-- The Gnomon area grows by 2*u^2. -/
theorem squareGnomon_step (x u : R) :
    squareGnomon (x + u) u =
      squareGnomon x u + 2 * u ^ 2 := by
  rw [squareGnomon_eq_mul_two_mul_add, squareGnomon_eq_mul_two_mul_add]
  ring

/-- The raw square Gnomon area obeys degree-two coordinate scaling. -/
theorem squareGnomon_scale (k x u : R) :
    squareGnomon (k * x) (k * u) = k ^ 2 * squareGnomon x u := by
  rw [squareGnomon_eq_mul_two_mul_add, squareGnomon_eq_mul_two_mul_add]
  ring

end DkMath.CosmicFormula.SquareGnomon
