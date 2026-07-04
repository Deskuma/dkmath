/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Pascal.WallisCosmicPetalBridge
import DkMath.Pascal.WallisLimitBridge

#print "file: DkMath.Pascal.WallisGrowthBridge"

/-!
# Wallis growth bridge

This module is the growth-facing layer after the finite Wallis-Cosmic bridge
and the limit-facing Wallis bridge.

The goal is not to use Stirling's approximation as the primary explanation.
Instead, the route is to expose the exact growth structure behind

`centralRatioQ m = 4^m / Nat.choose (2*m) m`.

The current exact bridge is:

```text
centralRatioQ m * mirrorOddRatioPartialQ m
  = wallisPartialQ m
  = cosmicPartialQ m
```

and the limit bridge proves:

```text
((cosmicPartialQ m : Q) : R) -> Real.pi / 2.
```

Thus the growth of `centralRatioQ` is encoded in the decay of the mirror
factor.  This module records that viewpoint as exact algebraic identities first.

## Roadmap toward the central-binomial growth law

1. Exact division identities:
   `centralRatioQ = wallisPartialQ / mirrorOddRatioPartialQ` and
   `centralRatioQ = cosmicPartialQ / mirrorOddRatioPartialQ`.

2. Mirror analysis:
   prove an exact or asymptotic description of
   `mirrorOddRatioPartialQ m`, ideally showing that it decays like
   a positive constant divided by `sqrt m`.

3. Squared central-ratio route:
   the informal target is
   `centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m`.
   This should be proved as a finite theorem before any asymptotic theorem.
   It comes from the expected telescoping relation
   `centralRatioQ m / mirrorOddRatioPartialQ m = 2*m + 1`.

4. Limit/asymptotic extraction:
   combine the squared identity with
   `wallisPartialQ -> Real.pi / 2` to derive
   `centralRatioQ m ~ sqrt (Real.pi * m)`.

5. Central binomial coefficient:
   since `centralRatioQ m = 4^m / Nat.choose (2*m) m`, invert the asymptotic
   to recover
   `Nat.choose (2*m) m ~ 4^m / sqrt (Real.pi * m)`.

## Current Mathlib survey

The local search found Mathlib's general asymptotic API
`Asymptotics.IsEquivalent`, `_ ~[l] _`, and the existing Wallis limit theorem
used in `WallisLimitBridge`.  It did not find a ready-to-use central-binomial
Stirling theorem under obvious names such as `centralBinomial`,
`Nat.choose`, `Wallis`, `Stirling`, `sqrt`, or `Asymptotics`.

So the next Lean-realistic step is to prove the finite squared identity and
then use `Asymptotics.IsEquivalent` / `Tendsto` tools explicitly.
-/

namespace DkMath.Pascal.WallisGrowthBridge

open Filter Topology
open DkMath.Pascal.WallisCosmicPetalBridge
open DkMath.Pascal.WallisLimitBridge

/-- The mirror half-product is nonzero. -/
theorem mirrorOddRatioPartialQ_ne_zero (m : ℕ) :
    mirrorOddRatioPartialQ m ≠ 0 :=
  (mirrorOddRatioPartialQ_pos m).ne'

/--
Exact growth decomposition through the cosmic gap product.

The central ratio grows precisely as the cosmic partial product divided by the
mirror term.  Since the cosmic partial product converges to `Real.pi / 2`, the
remaining growth problem is the decay rate of the mirror term.
-/
theorem centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
    (m : ℕ) :
    centralRatioQ m =
      cosmicPartialQ m / mirrorOddRatioPartialQ m := by
  calc
    centralRatioQ m =
        centralRatioQ m * mirrorOddRatioPartialQ m /
          mirrorOddRatioPartialQ m := by
      field_simp [mirrorOddRatioPartialQ_ne_zero m]
    _ = cosmicPartialQ m / mirrorOddRatioPartialQ m := by
      rw [centralRatioQ_mul_mirror_eq_cosmicPartialQ]

/--
Exact growth decomposition through the finite Wallis product.

This is the same identity as
`centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ`, but routed
through the Wallis partial product.
-/
theorem centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
    (m : ℕ) :
    centralRatioQ m =
      wallisPartialQ m / mirrorOddRatioPartialQ m := by
  calc
    centralRatioQ m =
        centralRatioQ m * mirrorOddRatioPartialQ m /
          mirrorOddRatioPartialQ m := by
      field_simp [mirrorOddRatioPartialQ_ne_zero m]
    _ = wallisPartialQ m / mirrorOddRatioPartialQ m := by
      rw [centralRatioQ_mul_mirror_eq_wallisPartialQ]

/--
Real version of the cosmic growth decomposition.

This is a coercion-facing theorem for later limit work.  It intentionally
does not claim any asymptotic estimate yet.
-/
theorem real_coe_centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) =
      ((cosmicPartialQ m : ℚ) : ℝ) /
        ((mirrorOddRatioPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast
    centralRatioQ_eq_cosmicPartialQ_div_mirrorOddRatioPartialQ m

/--
Real version of the Wallis growth decomposition.

This is the same exact decomposition, but with the finite Wallis product as
the numerator.  It is the form expected to combine most directly with
`real_coe_wallisPartialQ_eq_Wallis_W`.
-/
theorem real_coe_centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) =
      ((wallisPartialQ m : ℚ) : ℝ) /
        ((mirrorOddRatioPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast
    centralRatioQ_eq_wallisPartialQ_div_mirrorOddRatioPartialQ m

/-!
## Telescoping mirror ratio

The next finite target is the exact squared growth identity

```text
centralRatioQ m ^ 2 = (2*m + 1) * wallisPartialQ m.
```

The key is not an asymptotic theorem; it is the telescoping ratio between the
central half-product and the mirror half-product.  We prove it by recurrence,
which keeps the product cancellation explicit and avoids a brittle direct
`Finset.prod_div_distrib` proof.
-/

/-- One-step recurrence for the central ratio. -/
theorem centralRatioQ_succ_eq
    (m : ℕ) :
    centralRatioQ (m + 1) =
      centralRatioQ m * ((2 * m + 2 : ℚ) / (2 * m + 1 : ℚ)) := by
  rw [centralRatioQ_eq_centralOddRatioPartialQ (m + 1),
    centralRatioQ_eq_centralOddRatioPartialQ m]
  unfold centralOddRatioPartialQ evenCenterQ oddLeftQ
  rw [Finset.prod_range_succ]

/-- One-step recurrence for the mirror half-product. -/
theorem mirrorOddRatioPartialQ_succ_eq
    (m : ℕ) :
    mirrorOddRatioPartialQ (m + 1) =
      mirrorOddRatioPartialQ m * ((2 * m + 2 : ℚ) / (2 * m + 3 : ℚ)) := by
  unfold mirrorOddRatioPartialQ evenCenterQ oddRightQ
  rw [Finset.prod_range_succ]

/--
The quotient of the central ratio by the mirror factor telescopes to the
right odd boundary `2*m + 1`.
-/
theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one
    (m : ℕ) :
    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) := by
  induction m with
  | zero =>
      simp [centralRatioQ, mirrorOddRatioPartialQ]
  | succ m ih =>
      have hcentral :
          centralRatioQ m =
            (2 * m + 1 : ℚ) * mirrorOddRatioPartialQ m := by
        calc
          centralRatioQ m =
              (centralRatioQ m / mirrorOddRatioPartialQ m) *
                mirrorOddRatioPartialQ m := by
            field_simp [mirrorOddRatioPartialQ_ne_zero m]
          _ = (2 * m + 1 : ℚ) * mirrorOddRatioPartialQ m := by
            rw [ih]
      rw [centralRatioQ_succ_eq, mirrorOddRatioPartialQ_succ_eq, hcentral]
      field_simp [mirrorOddRatioPartialQ_ne_zero m]
      norm_num
      ring

/--
Searchable alias: the telescoping quotient reaches the predecessor-indexed
right odd boundary.
-/
theorem centralRatioQ_div_mirrorOddRatioPartialQ_eq_oddRightQ_pred
    (m : ℕ) :
    centralRatioQ m / mirrorOddRatioPartialQ m = (2 * m + 1 : ℚ) :=
  centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one m

/--
Finite squared central-ratio identity through the Wallis product.

This is the exact finite growth line behind the later asymptotic reading:
the square of the central ratio is a linear odd boundary times the Wallis
partial product.
-/
theorem centralRatioQ_sq_eq_odd_mul_wallisPartialQ
    (m : ℕ) :
    centralRatioQ m ^ 2 =
      (2 * m + 1 : ℚ) * wallisPartialQ m := by
  calc
    centralRatioQ m ^ 2 =
        (centralRatioQ m / mirrorOddRatioPartialQ m) *
          (centralRatioQ m * mirrorOddRatioPartialQ m) := by
      field_simp [mirrorOddRatioPartialQ_ne_zero m]
    _ = (2 * m + 1 : ℚ) * wallisPartialQ m := by
      rw [centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one,
        centralRatioQ_mul_mirror_eq_wallisPartialQ]

/--
Finite squared central-ratio identity through the cosmic gap product.
-/
theorem centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
    (m : ℕ) :
    centralRatioQ m ^ 2 =
      (2 * m + 1 : ℚ) * cosmicPartialQ m := by
  rw [← wallisPartialQ_eq_cosmicPartialQ]
  exact centralRatioQ_sq_eq_odd_mul_wallisPartialQ m

/--
Real-coercion form of the squared Wallis growth identity.
-/
theorem real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
      (2 * m + 1 : ℝ) * ((wallisPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_sq_eq_odd_mul_wallisPartialQ m

/--
Real-coercion form of the squared cosmic growth identity.
-/
theorem real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ
    (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 =
      (2 * m + 1 : ℝ) * ((cosmicPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_sq_eq_odd_mul_cosmicPartialQ m

/-!
TODO for the next asymptotic pass:

Prove

```lean
Filter.Tendsto
  (fun m : ℕ => (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
  Filter.atTop
  (nhds Real.pi)
```

from `real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ`,
`tendsto_wallisPartialQ_pi_div_two`, and
`(2*m+1)/m -> 2`.  This is no longer a finite algebra problem: it needs the
standard `atTop` handling for `m ≠ 0` and the real limit of `(2*m+1)/m`.
Keep it as a separate proof-complete checkpoint.
-/

end DkMath.Pascal.WallisGrowthBridge
