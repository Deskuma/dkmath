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
open Asymptotics
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
## Squared normalized growth limit

The finite identity above is strong enough to extract the first genuine
growth theorem without invoking Stirling's approximation:

```lean
Filter.Tendsto
  (fun m : ℕ => (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
  Filter.atTop
  (nhds Real.pi)
```

The proof is deliberately routed through the Wallis finite product:

```text
centralRatioQ m ^ 2 / m
  = ((2*m+1) / m) * wallisPartialQ m
  -> 2 * (pi / 2)
  = pi.
```

This keeps the growth reading independent from any Stirling theorem.  The
remaining square-root form should be a later asymptotic-equivalence layer.
-/

/-- Algebraic normalization of the odd boundary ratio away from `m = 0`. -/
theorem odd_boundary_div_nat_eq_two_add_inv
    {m : ℕ} (hm : m ≠ 0) :
    ((2 * m + 1 : ℝ) / (m : ℝ)) =
      2 + 1 / (m : ℝ) := by
  field_simp [Nat.cast_ne_zero.mpr hm]

/-- The normalized right odd boundary tends to `2`. -/
theorem tendsto_odd_boundary_div_nat_two :
    Filter.Tendsto
      (fun m : ℕ => ((2 * m + 1 : ℝ) / (m : ℝ)))
      Filter.atTop
      (nhds 2) := by
  have hlim :
      Filter.Tendsto
        (fun m : ℕ => 2 + 1 / (m : ℝ))
        Filter.atTop
        (nhds (2 + 0)) := by
    exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have hlim' :
      Filter.Tendsto
        (fun m : ℕ => 2 + 1 / (m : ℝ))
        Filter.atTop
        (nhds 2) := by
    simpa using hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (odd_boundary_div_nat_eq_two_add_inv (Nat.ne_of_gt hm)).symm

/--
Finite rewrite for the squared normalized central ratio.

The hypothesis only removes the endpoint `m = 0`; the limit theorem below
discharges it with `eventually_gt_atTop 0`.
-/
theorem real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
    {m : ℕ} (hm : m ≠ 0) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ) =
      ((2 * m + 1 : ℝ) / (m : ℝ)) *
        ((wallisPartialQ m : ℚ) : ℝ) := by
  rw [real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ]
  field_simp [Nat.cast_ne_zero.mpr hm]

/--
Finite rewrite for the squared normalized central ratio through the cosmic
partial product.
-/
theorem real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_cosmic
    {m : ℕ} (hm : m ≠ 0) :
    ((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ) =
      ((2 * m + 1 : ℝ) / (m : ℝ)) *
        ((cosmicPartialQ m : ℚ) : ℝ) := by
  rw [real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ]
  field_simp [Nat.cast_ne_zero.mpr hm]

/--
Squared normalized central-ratio growth.

This is the Wallis route to the first central-binomial growth surface:
`centralRatioQ m ^ 2 / m -> Real.pi`.  No Stirling approximation is used.
-/
theorem tendsto_real_centralRatioQ_sq_div_nat_pi :
    Filter.Tendsto
      (fun m : ℕ =>
        (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
      Filter.atTop
      (nhds Real.pi) := by
  have hprod :
      Filter.Tendsto
        (fun m : ℕ =>
          ((2 * m + 1 : ℝ) / (m : ℝ)) *
            ((wallisPartialQ m : ℚ) : ℝ))
        Filter.atTop
        (nhds (2 * (Real.pi / 2))) := by
    exact tendsto_odd_boundary_div_nat_two.mul tendsto_wallisPartialQ_pi_div_two
  have hprod_pi :
      Filter.Tendsto
        (fun m : ℕ =>
          ((2 * m + 1 : ℝ) / (m : ℝ)) *
            ((wallisPartialQ m : ℚ) : ℝ))
        Filter.atTop
        (nhds Real.pi) := by
    convert hprod using 1
    ring_nf
  refine hprod_pi.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact (real_centralRatioQ_sq_div_nat_eq_odd_div_nat_mul_wallis
    (Nat.ne_of_gt hm)).symm

/--
Cosmic-route alias for the same squared normalized growth theorem.

The proof above already factors through the Wallis product.  This name records
that the same surface is compatible with the cosmic partial product, via the
finite equality `wallisPartialQ_eq_cosmicPartialQ`.
-/
theorem tendsto_real_centralRatioQ_sq_div_nat_pi_cosmic_route :
    Filter.Tendsto
      (fun m : ℕ =>
        (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)))
      Filter.atTop
      (nhds Real.pi) :=
  tendsto_real_centralRatioQ_sq_div_nat_pi

/-!
## Square-root growth surface

The previous theorem proves the squared normalized limit.  The next surface is
the square-root reading

```text
centralRatioQ m ~ sqrt (Real.pi * m).
```

Rather than appealing to Stirling's approximation, we take the square root of
the already-proved Wallis growth surface.  The only extra bookkeeping is the
eventual positivity of `m` and of `centralRatioQ m`.
-/

/--
The square-root normalization of the squared central-ratio expression tends
to `1`.
-/
theorem tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one :
    Filter.Tendsto
      (fun m : ℕ =>
        Real.sqrt
          ((((centralRatioQ m : ℚ) : ℝ) ^ 2) /
            (Real.pi * (m : ℝ))))
      Filter.atTop
      (nhds 1) := by
  have hdiv :
      Filter.Tendsto
        (fun m : ℕ =>
          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi)
        Filter.atTop
        (nhds (Real.pi / Real.pi)) := by
    exact tendsto_real_centralRatioQ_sq_div_nat_pi.div_const Real.pi
  have hdiv_one :
      Filter.Tendsto
        (fun m : ℕ =>
          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi)
        Filter.atTop
        (nhds 1) := by
    simpa [div_self Real.pi_ne_zero] using hdiv
  have hsqrt :
      Filter.Tendsto
        (fun m : ℕ =>
          Real.sqrt
            ((((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi))
        Filter.atTop
        (nhds (Real.sqrt 1)) :=
    hdiv_one.sqrt
  have hsqrt_one :
      Filter.Tendsto
        (fun m : ℕ =>
          Real.sqrt
            ((((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi))
        Filter.atTop
        (nhds 1) := by
    simpa [Real.sqrt_one] using hsqrt
  refine hsqrt_one.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hm_ne, Real.pi_ne_zero]

/--
The central ratio divided by `sqrt (Real.pi * m)` tends to `1`.

This is the operational limit form of
`centralRatioQ m ~ sqrt (Real.pi * m)`.
-/
theorem tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one :
    Filter.Tendsto
      (fun m : ℕ =>
        ((centralRatioQ m : ℚ) : ℝ) /
          Real.sqrt (Real.pi * (m : ℝ)))
      Filter.atTop
      (nhds 1) := by
  refine tendsto_sqrt_centralRatioQ_sq_div_pi_mul_nat_one.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hc_pos : 0 < ((centralRatioQ m : ℚ) : ℝ) := by
    exact_mod_cast centralRatioQ_pos m
  rw [Real.sqrt_div (sq_nonneg ((centralRatioQ m : ℚ) : ℝ))
    (Real.pi * (m : ℝ))]
  rw [Real.sqrt_sq hc_pos.le]

/--
Central-ratio square-root asymptotic equivalence.

This is the Wallis-derived growth surface:
`centralRatioQ m` is asymptotic to `sqrt (Real.pi * m)`.
-/
theorem isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat :
    (fun m : ℕ => ((centralRatioQ m : ℚ) : ℝ)) ~[Filter.atTop]
      (fun m : ℕ => Real.sqrt (Real.pi * (m : ℝ))) := by
  exact isEquivalent_of_tendsto_one
    tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one

/-!
## Central binomial coefficient surface

The definition of `centralRatioQ` is

```text
centralRatioQ m = 4^m / Nat.choose (2*m) m.
```

After the square-root growth surface, the central-binomial form is obtained by
inverting this exact finite identity.  This is still a Wallis-derived route;
no Stirling theorem is used as an input.
-/

/--
Finite rational identity that inverts the definition of `centralRatioQ`.

This is the exact bridge from the central-ratio surface to the central
binomial coefficient surface.
-/
theorem nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ
    (m : ℕ) :
    (Nat.choose (2 * m) m : ℚ) =
      (4 : ℚ) ^ m / centralRatioQ m := by
  unfold centralRatioQ
  have hchoose_ne_Q : (Nat.choose (2 * m) m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
  field_simp [hchoose_ne_Q]
  norm_num [pow_mul]

/--
Finite real identity that inverts the definition of `centralRatioQ`.
-/
theorem real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
    (m : ℕ) :
    ((Nat.choose (2 * m) m : ℕ) : ℝ) =
      (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ) := by
  exact_mod_cast nat_choose_two_mul_self_cast_eq_pow_four_div_centralRatioQ m

/--
Central binomial coefficient asymptotic, derived from the Wallis growth
surface.

This is the usual central-binomial growth law in DkMath's orientation:
`choose (2*m) m ~ 4^m / sqrt (pi*m)`.
-/
theorem isEquivalent_real_centralBinomial_sqrt_pi_mul_nat :
    (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
      (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) := by
  have hfinite :
      (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) =ᶠ[Filter.atTop]
        (fun m : ℕ => (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ)) :=
    Eventually.of_forall real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ
  have hratio :
      (fun m : ℕ => (4 : ℝ) ^ m / ((centralRatioQ m : ℚ) : ℝ)) ~[Filter.atTop]
        (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) := by
    exact IsEquivalent.div IsEquivalent.refl isEquivalent_real_centralRatioQ_sqrt_pi_mul_nat
  exact hfinite.isEquivalent.trans hratio

/--
Searchable alias for the central-binomial asymptotic.

The longer name makes the denominator structure explicit:
`4^m / sqrt (pi*m)`.
-/
theorem isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat :
    (fun m : ℕ => ((Nat.choose (2 * m) m : ℕ) : ℝ)) ~[Filter.atTop]
      (fun m : ℕ => (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))) :=
  isEquivalent_real_centralBinomial_sqrt_pi_mul_nat

/--
Operational ratio form of the central-binomial growth law.

This is the same asymptotic statement as
`isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat`, but exposed
as a direct `Tendsto` theorem for downstream calculations.
-/
theorem tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one :
    Filter.Tendsto
      (fun m : ℕ =>
        ((Nat.choose (2 * m) m : ℕ) : ℝ) /
          ((4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))))
      Filter.atTop
      (nhds 1) := by
  have hden :
      ∀ᶠ m : ℕ in Filter.atTop,
        (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hprod_pos : 0 < Real.pi * (m : ℝ) :=
      mul_pos Real.pi_pos hm_pos
    exact div_ne_zero (pow_ne_zero m (by norm_num : (4 : ℝ) ≠ 0))
      (Real.sqrt_pos_of_pos hprod_pos).ne'
  exact (isEquivalent_iff_tendsto_one hden).mp
    isEquivalent_real_centralBinomial_four_pow_div_sqrt_pi_mul_nat

end DkMath.Pascal.WallisGrowthBridge
