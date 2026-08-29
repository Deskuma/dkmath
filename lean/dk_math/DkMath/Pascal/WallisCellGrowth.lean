/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DkMath.Pascal.WallisGrowthBridge

#print "file: DkMath.Pascal.WallisCellGrowth"

/-!
# Pascal cells from Wallis growth

This module turns the central Wallis--Cosmic growth theory into finite APIs
for Pascal cells.  It separates claims which have different meanings.

* `real_centralBinomial_eq_four_pow_div_sqrt_cosmic` is an exact real-valued
  readout of the central cell from the finite cosmic product.
* `centralOffsetGrowthQ` transports the central cell to an offset cell in an
  even row.
* `oddCellGrowthQ` adds the exact lift needed to cover odd rows.
* `pascalCellGrowthQ` computes an arbitrary Pascal cell over `ℚ`, using row
  symmetry so that only `min k (n-k)` local growth factors are multiplied.
* `centralBinomialWallisApproxR` and the even/odd variants expose midpoint
  approximations with certified finite absolute-error radii.

The last definition is an exact executable finite product.  No constant-time
complexity claim is made: its number of factors is the distance from the
nearest edge.  The square-root formula is likewise an exact theorem over
`ℝ`, not a floating-point implementation.
-/

namespace DkMath.Pascal.WallisCellGrowth

open Finset
open Filter Topology
open DkMath.Pascal.WallisCosmicPetalBridge
open DkMath.Pascal.WallisLimitBridge
open DkMath.Pascal.WallisGrowthBridge

/-!
## Exact central Cosmic readout
-/

/--
The exact real-valued central coefficient reconstructed from the finite
Cosmic gap product.
-/
noncomputable def centralBinomialCosmicR (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m /
    Real.sqrt ((2 * m + 1 : ℝ) * ((cosmicPartialQ m : ℚ) : ℝ))

/--
The central ratio is the positive square root of its finite Cosmic square.
-/
theorem real_centralRatioQ_eq_sqrt_odd_mul_cosmic (m : ℕ) :
    ((centralRatioQ m : ℚ) : ℝ) =
      Real.sqrt ((2 * m + 1 : ℝ) * ((cosmicPartialQ m : ℚ) : ℝ)) := by
  rw [← real_coe_centralRatioQ_sq_eq_odd_mul_cosmicPartialQ]
  exact (Real.sqrt_sq (by exact_mod_cast (centralRatioQ_pos m).le)).symm

/--
Exact finite Cosmic formula for the central Pascal cell.

Unlike the later asymptotic formula, the denominator contains the finite
product `cosmicPartialQ m`, so this identity has no remainder term.
-/
theorem real_centralBinomial_eq_four_pow_div_sqrt_cosmic (m : ℕ) :
    ((Nat.choose (2 * m) m : ℕ) : ℝ) = centralBinomialCosmicR m := by
  rw [real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ,
    real_centralRatioQ_eq_sqrt_odd_mul_cosmic]
  rfl

/-!
## Finite Wallis error interval

Mathlib's finite Wallis inequalities give a certified interval, not merely an
`IsEquivalent` statement.  The lower endpoint substitutes the upper Wallis
bound `π/2`; the upper endpoint substitutes the finite lower Wallis bound.
-/

/-- Lower endpoint for the central binomial coefficient's Wallis interval. -/
noncomputable def centralBinomialWallisLowerR (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m / Real.sqrt ((2 * m + 1 : ℝ) * (Real.pi / 2))

/-- Upper endpoint for the central binomial coefficient's Wallis interval. -/
noncomputable def centralBinomialWallisUpperR (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m /
    Real.sqrt
      ((2 * m + 1 : ℝ) *
        (((2 * m + 1 : ℝ) / (2 * m + 2 : ℝ)) * (Real.pi / 2)))

/-- The finite Cosmic product is bounded above by `π/2`. -/
theorem real_cosmicPartialQ_le_pi_div_two (m : ℕ) :
    ((cosmicPartialQ m : ℚ) : ℝ) ≤ Real.pi / 2 := by
  rw [← real_coe_wallisPartialQ_eq_cosmicPartialQ,
    real_coe_wallisPartialQ_eq_Wallis_W]
  exact Real.Wallis.W_le m

/-- The finite lower Wallis bound, expressed through the Cosmic product. -/
theorem real_wallis_lower_le_cosmicPartialQ (m : ℕ) :
    ((2 * m + 1 : ℝ) / (2 * m + 2 : ℝ)) * (Real.pi / 2) ≤
      ((cosmicPartialQ m : ℚ) : ℝ) := by
  rw [← real_coe_wallisPartialQ_eq_cosmicPartialQ,
    real_coe_wallisPartialQ_eq_Wallis_W]
  exact Real.Wallis.le_W m

/-!
## Quantitative Wallis remainder

The two finite Wallis inequalities immediately give a certified `O(1/m)`
remainder for the Cosmic product.  This is the first sharp quantitative layer:
it costs no additional product evaluation and is strong enough to transport a
finite error certificate to every centered cell.
-/

/-- The signed finite remainder from the Cosmic product to `π/2`. -/
noncomputable def wallisRemainderR (m : ℕ) : ℝ :=
  Real.pi / 2 - ((cosmicPartialQ m : ℚ) : ℝ)

/-- The Wallis remainder is nonnegative. -/
theorem wallisRemainderR_nonneg (m : ℕ) :
    0 ≤ wallisRemainderR m := by
  unfold wallisRemainderR
  linarith [real_cosmicPartialQ_le_pi_div_two m]

/--
Explicit `O(1/m)` upper bound for the finite Wallis remainder.

The denominator is written as `4*m+4`, avoiding any hidden asymptotic
notation and making the bound suitable for later numerical certification.
-/
theorem wallisRemainderR_le_pi_div_four_mul_add_four (m : ℕ) :
    wallisRemainderR m ≤ Real.pi / (4 * (m : ℝ) + 4) := by
  unfold wallisRemainderR
  have hlower := real_wallis_lower_le_cosmicPartialQ m
  have hrewrite :
      Real.pi / 2 -
          ((2 * m + 1 : ℝ) / (2 * m + 2 : ℝ)) * (Real.pi / 2) =
        Real.pi / (4 * (m : ℝ) + 4) := by
    field_simp
    ring
  rw [← hrewrite]
  linarith

/-!
## Low-operation asymptotic evaluator

This evaluator uses one real power and one square root; unlike the exact
Cosmic readout it does not multiply an `m`-term product.  Its correctness is
the already-proved Wallis asymptotic, exposed under a calculator-facing name.
-/

/-- The low-operation central-binomial approximation `4^m / √(πm)`. -/
noncomputable def centralBinomialFastApproxR (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m / Real.sqrt (Real.pi * (m : ℝ))

/-- The low-operation evaluator has asymptotic relative error zero. -/
theorem tendsto_real_centralBinomial_div_fastApprox_one :
    Filter.Tendsto
      (fun m : ℕ =>
        ((Nat.choose (2 * m) m : ℕ) : ℝ) / centralBinomialFastApproxR m)
      Filter.atTop (nhds 1) := by
  simpa [centralBinomialFastApproxR] using
    tendsto_real_centralBinomial_div_four_pow_div_sqrt_pi_mul_nat_one

/--
Exact finite correction identity for the low-operation evaluator.

The square of the ratio to `4^m/√(πm)` is completely determined by the
finite Wallis product.  This is the preferred starting point for sharper
remainder work, since it isolates the only finite correction factor before a
square-root estimate is attempted.
-/
theorem real_centralBinomial_sq_div_fastApprox_sq_eq_pi_mul_nat_div_wallis
    {m : ℕ} (hm : m ≠ 0) :
    (((Nat.choose (2 * m) m : ℕ) : ℝ) ^ 2 /
        (centralBinomialFastApproxR m) ^ 2) =
      (Real.pi * (m : ℝ)) /
        ((2 * m + 1 : ℝ) * ((wallisPartialQ m : ℚ) : ℝ)) := by
  rw [centralBinomialFastApproxR,
    real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ,
    div_pow,
    real_coe_centralRatioQ_sq_eq_odd_mul_wallisPartialQ]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hW : ((wallisPartialQ m : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (wallisPartialQ_pos m).ne'
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hm)
  have hsqrt : Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos Real.pi_pos hm_pos)).ne'
  field_simp [hmR, hW, hsqrt, Real.pi_ne_zero]
  rw [Real.sq_sqrt (mul_nonneg hm_pos.le Real.pi_pos.le)]

/-!
## First-correction recurrence

The following layer does not import Stirling.  It normalizes the exact
central-ratio square by `πm` and records its one-step recurrence.  The two
rational barriers below are local supersolution/subsolution inequalities for
that recurrence; both have first coefficient `1/4`.  A later tail-comparison
lemma can therefore extract the normalized correction `+1/(4m)`, which in
turn gives the binomial correction `-1/(8m)` after taking a square root and
inverting.
-/

/-- The normalized central-ratio square `R_m²/(πm)`. -/
noncomputable def normalizedCentralSquareR (m : ℕ) : ℝ :=
  (((centralRatioQ m : ℚ) : ℝ) ^ 2) /
    (Real.pi * (m : ℝ))

/-- The exact rational step factor in the normalized-square recurrence. -/
noncomputable def normalizedCentralSquareStepR (m : ℕ) : ℝ :=
  4 * (m : ℝ) * (m + 1 : ℝ) / (2 * m + 1 : ℝ) ^ 2

/-- Exact recurrence forced by the finite central-ratio identity. -/
theorem normalizedCentralSquareR_succ_eq_mul_step
    {m : ℕ} (hm : m ≠ 0) :
    normalizedCentralSquareR (m + 1) =
      normalizedCentralSquareR m * normalizedCentralSquareStepR m := by
  have hratioQ := centralRatioQ_succ_eq m
  have hratio :
      ((centralRatioQ (m + 1) : ℚ) : ℝ) =
        ((centralRatioQ m : ℚ) : ℝ) *
          ((2 * m + 2 : ℚ) / (2 * m + 1 : ℚ) : ℝ) := by
    exact_mod_cast hratioQ
  push_cast at hratio
  rw [normalizedCentralSquareR, normalizedCentralSquareR,
    normalizedCentralSquareStepR, hratio]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp [hmR, Real.pi_ne_zero]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Upper rational barrier for the normalized-square recurrence. -/
noncomputable def normalizedSquareUpperBarrierR (m : ℕ) : ℝ :=
  1 + 1 / (4 * (m : ℝ) - 1)

/-- Lower rational barrier for the normalized-square recurrence. -/
noncomputable def normalizedSquareLowerBarrierR (m : ℕ) : ℝ :=
  1 + 1 / (4 * (m : ℝ) + 1)

/-- The upper barrier is a local supersolution. -/
theorem normalizedSquareUpperBarrier_step_le
    {m : ℕ} (hm : m ≠ 0) :
    normalizedSquareUpperBarrierR (m + 1) /
        normalizedCentralSquareStepR m ≤
      normalizedSquareUpperBarrierR m := by
  unfold normalizedSquareUpperBarrierR normalizedCentralSquareStepR
  push_cast
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  have hden : (0 : ℝ) < 4 * (m : ℝ) - 1 := by nlinarith
  have hden_next : (0 : ℝ) < 4 * (m + 1 : ℝ) - 1 := by
    nlinarith
  field_simp [ne_of_gt hmR, ne_of_gt hden, ne_of_gt hden_next]
  ring_nf
  nlinarith [sq_nonneg (4 * (m : ℝ) - 1)]

/-- The lower barrier is a local subsolution. -/
theorem normalizedSquareLowerBarrier_step_ge
    {m : ℕ} (hm : m ≠ 0) :
    normalizedSquareLowerBarrierR m ≤
      normalizedSquareLowerBarrierR (m + 1) /
        normalizedCentralSquareStepR m := by
  unfold normalizedSquareLowerBarrierR normalizedCentralSquareStepR
  push_cast
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  field_simp [ne_of_gt (show (0 : ℝ) < 4 * (m : ℝ) + 1 by positivity),
    ne_of_gt (show (0 : ℝ) < 4 * (m + 1 : ℝ) + 1 by positivity),
    ne_of_gt (show (0 : ℝ) < 2 * (m : ℝ) + 1 by positivity)]
  ring_nf
  nlinarith [sq_nonneg (2 * (m : ℝ) + 1)]

/-- The upper barrier has first coefficient `1/4`. -/
theorem tendsto_nat_mul_upperBarrier_sub_one :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        (normalizedSquareUpperBarrierR m - 1))
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  have hden : Filter.Tendsto
      (fun m : ℕ => 4 - 1 / (m : ℝ)) Filter.atTop (nhds (4 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_atTop_nhds_zero_nat :
        Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ))
          Filter.atTop (nhds 0)))
  have hratio : Filter.Tendsto
      (fun m : ℕ => 1 / (4 - 1 / (m : ℝ))) Filter.atTop
        (nhds (1 / 4 : ℝ)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    have hh := hconst.div hden (by norm_num : (4 : ℝ) ≠ 0)
    refine hh.congr' ?_
    filter_upwards [] with m
    rfl
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  unfold normalizedSquareUpperBarrierR
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hmR]
  ring

/-- The lower barrier has the same first coefficient `1/4`. -/
theorem tendsto_nat_mul_lowerBarrier_sub_one :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        (normalizedSquareLowerBarrierR m - 1))
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  have hden : Filter.Tendsto
      (fun m : ℕ => 4 + 1 / (m : ℝ)) Filter.atTop (nhds (4 : ℝ)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat :
        Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ))
          Filter.atTop (nhds 0)))
  have hratio : Filter.Tendsto
      (fun m : ℕ => 1 / (4 + 1 / (m : ℝ))) Filter.atTop
        (nhds (1 / 4 : ℝ)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    have hh := hconst.div hden (by norm_num : (4 : ℝ) ≠ 0)
    refine hh.congr' ?_
    filter_upwards [] with m
    rfl
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  unfold normalizedSquareLowerBarrierR
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hmR]
  ring

/-!
The preceding two limits are the coefficient calculation for the rational
barriers themselves.  The next lemma isolates the only remaining comparison
step: once the exact normalized-square sequence is placed between those two
barriers, the coefficient `1/4` follows by an order squeeze.  This keeps the
analytic tail comparison explicit instead of hiding it in an asymptotic
notation.
-/

theorem tendsto_mul_sub_one_of_normalizedSquare_barriers
    (S : ℕ → ℝ)
    (hlower : ∀ {m : ℕ}, m ≠ 0 →
      normalizedSquareLowerBarrierR m ≤ S m)
    (hupper : ∀ {m : ℕ}, m ≠ 0 →
      S m ≤ normalizedSquareUpperBarrierR m) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) * (S m - 1))
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  apply Filter.Tendsto.squeeze'
    tendsto_nat_mul_lowerBarrier_sub_one
    tendsto_nat_mul_upperBarrier_sub_one
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h := hlower (Nat.ne_of_gt hm)
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h := hupper (Nat.ne_of_gt hm)
    nlinarith

/-!
For the actual sequence, the uncorrected limit is already available from the
Wallis growth bridge.  The following identity records that this limit is the
same normalized quantity used by the barrier argument.
-/

theorem tendsto_normalizedCentralSquareR_one :
    Filter.Tendsto normalizedCentralSquareR Filter.atTop (nhds 1) := by
  have hdiv := tendsto_real_centralRatioQ_sq_div_nat_pi.div_const Real.pi
  have hdiv_one :
      Filter.Tendsto
        (fun m : ℕ =>
          (((centralRatioQ m : ℚ) : ℝ) ^ 2 / (m : ℝ)) / Real.pi)
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa [div_self Real.pi_ne_zero] using hdiv
  refine hdiv_one.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  unfold normalizedCentralSquareR
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hmR, Real.pi_ne_zero]

/-!
Square-root transport turns the normalized-square coefficient `1/4` into the
central-ratio coefficient `1/8`.  The proof is the exact identity
`u - 1 = (u^2 - 1)/(u + 1)` on the eventual positive tail; no Taylor
expansion is used.
-/

theorem tendsto_nat_mul_centralRatio_normalized_sub_one_of_square_correction
    (hcorr :
      Filter.Tendsto
        (fun m : ℕ => (m : ℝ) *
          (normalizedCentralSquareR m - 1))
        Filter.atTop (nhds (1 / 4 : ℝ))) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        ((((centralRatioQ m : ℚ) : ℝ) /
          Real.sqrt (Real.pi * (m : ℝ))) - 1))
      Filter.atTop (nhds (1 / 8 : ℝ)) := by
  let u : ℕ → ℝ := fun m =>
    ((centralRatioQ m : ℚ) : ℝ) /
      Real.sqrt (Real.pi * (m : ℝ))
  have hu : Filter.Tendsto u Filter.atTop (nhds 1) := by
    simpa [u] using tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
  have hden : Filter.Tendsto (fun m => u m + 1) Filter.atTop
      (nhds (2 : ℝ)) := by
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
        (nhds 1) := tendsto_const_nhds
    convert hu.add hone using 1
    all_goals norm_num
  have hquot := hcorr.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hquot' : Filter.Tendsto
      (fun m : ℕ =>
        ((m : ℝ) * (normalizedCentralSquareR m - 1)) /
          (u m + 1))
      Filter.atTop (nhds (1 / 8 : ℝ)) := by
    convert hquot using 1
    · ext m
      simp only [Pi.div_apply]
    · norm_num
  refine hquot'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt : Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 := by
    exact (Real.sqrt_pos.2 (mul_pos Real.pi_pos
      (by exact_mod_cast hm))).ne'
  have hu_sq : normalizedCentralSquareR m = (u m) ^ 2 := by
    unfold normalizedCentralSquareR u
    rw [div_pow]
    rw [Real.sq_sqrt (mul_nonneg Real.pi_pos.le
      (by exact_mod_cast (Nat.zero_le m)))]
  rw [hu_sq]
  have hcr_pos : 0 < ((centralRatioQ m : ℚ) : ℝ) := by
    exact_mod_cast centralRatioQ_pos m
  have hu_pos : 0 < u m := by
    dsimp [u]
    exact div_pos hcr_pos (Real.sqrt_pos.2
      (mul_pos Real.pi_pos (by exact_mod_cast hm)))
  have hsum : u m + 1 ≠ 0 := ne_of_gt (by linarith)
  dsimp [u]
  field_simp [hsqrt, hsum]
  ring

/-!
Finally invert the central ratio.  Since the central binomial coefficient is
`4^m / centralRatioQ m`, the `+1/8` ratio correction becomes the desired
`-1/8` correction for `4^m / √(πm)`.  The statement is conditional only on
the square-correction input above; all inversion and sign changes are exact.
-/

theorem tendsto_nat_mul_centralBinomial_fast_relative_sub_one_of_square_correction
    (hcorr :
      Filter.Tendsto
        (fun m : ℕ => (m : ℝ) *
          (normalizedCentralSquareR m - 1))
        Filter.atTop (nhds (1 / 4 : ℝ))) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        ((((Nat.choose (2 * m) m : ℕ) : ℝ) /
          centralBinomialFastApproxR m) - 1))
      Filter.atTop (nhds (-1 / 8 : ℝ)) := by
  let u : ℕ → ℝ := fun m =>
    ((centralRatioQ m : ℚ) : ℝ) /
      Real.sqrt (Real.pi * (m : ℝ))
  have hu : Filter.Tendsto u Filter.atTop (nhds 1) := by
    simpa [u] using tendsto_real_centralRatioQ_div_sqrt_pi_mul_nat_one
  have hratio :=
    tendsto_nat_mul_centralRatio_normalized_sub_one_of_square_correction hcorr
  have hneg := hratio.neg
  have hinv := hneg.div hu (by norm_num : (1 : ℝ) ≠ 0)
  have hinv' : Filter.Tendsto
      (fun m : ℕ =>
        (-(m : ℝ) * (u m - 1)) / u m)
      Filter.atTop (nhds (-1 / 8 : ℝ)) := by
    convert hinv using 1
    · ext m
      dsimp [u]
      ring
    · norm_num
  refine hinv'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hcr_pos : 0 < ((centralRatioQ m : ℚ) : ℝ) := by
    exact_mod_cast centralRatioQ_pos m
  have hsqrt : Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 := by
    exact (Real.sqrt_pos.2 (mul_pos Real.pi_pos
      (by exact_mod_cast hm))).ne'
  have hu_pos : 0 < u m := by
    dsimp [u]
    exact div_pos hcr_pos (Real.sqrt_pos.2
      (mul_pos Real.pi_pos (by exact_mod_cast hm)))
  have hu_ne : u m ≠ 0 := hu_pos.ne'
  have hchoose := real_nat_choose_two_mul_self_eq_pow_four_div_centralRatioQ m
  unfold centralBinomialFastApproxR
  rw [hchoose]
  dsimp [u]
  field_simp [hmR, hsqrt, hu_ne]
  ring

/-!
Public boundary theorem for the first Wallis correction.  Supplying global
lower/upper barrier comparison for the exact normalized-square sequence now
closes the entire coefficient chain in one call.
-/

theorem tendsto_nat_mul_centralBinomial_fast_relative_sub_one_of_barriers
    (hlower : ∀ {m : ℕ}, m ≠ 0 →
      normalizedSquareLowerBarrierR m ≤ normalizedCentralSquareR m)
    (hupper : ∀ {m : ℕ}, m ≠ 0 →
      normalizedCentralSquareR m ≤ normalizedSquareUpperBarrierR m) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        ((((Nat.choose (2 * m) m : ℕ) : ℝ) /
          centralBinomialFastApproxR m) - 1))
      Filter.atTop (nhds (-1 / 8 : ℝ)) := by
  exact tendsto_nat_mul_centralBinomial_fast_relative_sub_one_of_square_correction
    (tendsto_mul_sub_one_of_normalizedSquare_barriers
      normalizedCentralSquareR hlower hupper)

/-!
## Executable certification boundary

The interval test is itself an executable branch once a numerical real
backend is supplied.  The theorem below packages the successful branch as a
single exact-rounding function; the failed branch deliberately returns no
claim.
-/

/-- Certified central-cell readout when the Wallis interval has width `< 1`. -/
noncomputable def certifiedCentralBinomialNat (m : ℕ) : ℕ :=
  if centralBinomialWallisUpperR m < centralBinomialWallisLowerR m + 1 then
    Nat.ceil (centralBinomialWallisLowerR m)
  else 0

/-- Certified finite lower bound for the central Pascal cell. -/
theorem centralBinomialWallisLowerR_le_choose (m : ℕ) :
    centralBinomialWallisLowerR m ≤
      ((Nat.choose (2 * m) m : ℕ) : ℝ) := by
  rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic]
  unfold centralBinomialWallisLowerR centralBinomialCosmicR
  apply div_le_div_of_nonneg_left (by positivity)
  · apply Real.sqrt_pos.2
    exact mul_pos (by positivity) (by exact_mod_cast cosmicPartialQ_pos m)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (real_cosmicPartialQ_le_pi_div_two m) (by positivity)

/-- Certified finite upper bound for the central Pascal cell. -/
theorem choose_le_centralBinomialWallisUpperR (m : ℕ) :
    ((Nat.choose (2 * m) m : ℕ) : ℝ) ≤
      centralBinomialWallisUpperR m := by
  rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic]
  unfold centralBinomialWallisUpperR centralBinomialCosmicR
  apply div_le_div_of_nonneg_left (by positivity)
  · apply Real.sqrt_pos.2
    positivity
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (real_wallis_lower_le_cosmicPartialQ m) (by positivity)

/-- The central coefficient belongs to its explicit finite Wallis interval. -/
theorem centralBinomial_mem_wallisInterval (m : ℕ) :
    ((Nat.choose (2 * m) m : ℕ) : ℝ) ∈
      Set.Icc (centralBinomialWallisLowerR m) (centralBinomialWallisUpperR m) :=
  ⟨centralBinomialWallisLowerR_le_choose m,
    choose_le_centralBinomialWallisUpperR m⟩

/-- Midpoint of the certified finite Wallis interval. -/
noncomputable def centralBinomialWallisApproxR (m : ℕ) : ℝ :=
  (centralBinomialWallisLowerR m + centralBinomialWallisUpperR m) / 2

/-- Half-width of the certified finite Wallis interval. -/
noncomputable def centralBinomialWallisErrorR (m : ℕ) : ℝ :=
  (centralBinomialWallisUpperR m - centralBinomialWallisLowerR m) / 2

/-- The explicit Wallis error radius is nonnegative. -/
theorem centralBinomialWallisErrorR_nonneg (m : ℕ) :
    0 ≤ centralBinomialWallisErrorR m := by
  unfold centralBinomialWallisErrorR
  have hlower := centralBinomialWallisLowerR_le_choose m
  have hupper := choose_le_centralBinomialWallisUpperR m
  linarith

/--
Finite absolute-error guarantee for the midpoint Wallis approximation.
-/
theorem abs_choose_sub_centralBinomialWallisApproxR_le_error (m : ℕ) :
    |((Nat.choose (2 * m) m : ℕ) : ℝ) - centralBinomialWallisApproxR m| ≤
      centralBinomialWallisErrorR m := by
  rw [abs_le]
  unfold centralBinomialWallisApproxR centralBinomialWallisErrorR
  have hlower := centralBinomialWallisLowerR_le_choose m
  have hupper := choose_le_centralBinomialWallisUpperR m
  constructor <;> linarith

/--
A sound round-to-exact criterion for the finite Wallis interval.

The condition is deliberately explicit.  The basic Wallis interval need not
be narrower than one for large `m`; a later sharper remainder expansion can
discharge this premise on a useful range without changing the API.
-/
theorem ceil_centralBinomialWallisLowerR_eq_choose_of_width_lt_one
    (m : ℕ)
    (hwidth : centralBinomialWallisUpperR m <
      centralBinomialWallisLowerR m + 1) :
    Nat.ceil (centralBinomialWallisLowerR m) = Nat.choose (2 * m) m := by
  have hchoose_pos : Nat.choose (2 * m) m ≠ 0 :=
    (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
  apply (Nat.ceil_eq_iff hchoose_pos).2
  constructor
  · have hupper := choose_le_centralBinomialWallisUpperR m
    have hpred_cast :
        (((Nat.choose (2 * m) m) - 1 : ℕ) : ℝ) =
          ((Nat.choose (2 * m) m : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hchoose_pos)]
      norm_num
    rw [hpred_cast]
    exact (sub_lt_iff_lt_add).2 (hupper.trans_lt hwidth)
  · exact centralBinomialWallisLowerR_le_choose m

/-- Successful branch of `certifiedCentralBinomialNat` is exact. -/
theorem certifiedCentralBinomialNat_eq_choose_of_width_lt_one
    (m : ℕ)
    (hwidth : centralBinomialWallisUpperR m <
      centralBinomialWallisLowerR m + 1) :
    certifiedCentralBinomialNat m = Nat.choose (2 * m) m := by
  rw [certifiedCentralBinomialNat, if_pos hwidth]
  exact ceil_centralBinomialWallisLowerR_eq_choose_of_width_lt_one m hwidth

/-!
## Central-to-offset transport in an even row
-/

/-- The local multiplier taking offset `j` to offset `j + 1` in row `2*m`. -/
def centralOffsetFactorQ (m j : ℕ) : ℚ :=
  ((m - j : ℕ) : ℚ) / ((m + j + 1 : ℕ) : ℚ)

/--
The finite growth product from the central cell `(2*m, m)` to the cell
`(2*m, m+r)` on its right.
-/
def centralOffsetGrowthQ (m r : ℕ) : ℚ :=
  ∏ j ∈ Finset.range r, centralOffsetFactorQ m j

@[simp]
theorem centralOffsetGrowthQ_zero (m : ℕ) :
    centralOffsetGrowthQ m 0 = 1 := by
  simp [centralOffsetGrowthQ]

theorem centralOffsetGrowthQ_succ (m r : ℕ) :
    centralOffsetGrowthQ m (r + 1) =
      centralOffsetGrowthQ m r * centralOffsetFactorQ m r := by
  unfold centralOffsetGrowthQ
  rw [Finset.prod_range_succ]

/--
Exact one-step transport between adjacent cells of row `2*m`, while the
offset remains within the row.
-/
theorem cast_choose_even_center_add_succ (m r : ℕ) (hr : r < m) :
    (Nat.choose (2 * m) (m + (r + 1)) : ℚ) =
      (Nat.choose (2 * m) (m + r) : ℚ) * centralOffsetFactorQ m r := by
  have hden : ((m + r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  unfold centralOffsetFactorQ
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).2
  have hsub : 2 * m - (m + r) = m - r := by omega
  have hstep := Nat.choose_succ_right_eq (2 * m) (m + r)
  rw [hsub] at hstep
  exact_mod_cast hstep

/--
Exact central-to-offset factorization in an even row.

The bound `r ≤ m` ensures that `(m+r)` is a cell of row `2*m` and that every
local numerator in the transport is the intended positive natural factor.
-/
theorem cast_choose_even_center_add_eq_central_mul_offset
    (m r : ℕ) (hr : r ≤ m) :
    (Nat.choose (2 * m) (m + r) : ℚ) =
      (Nat.choose (2 * m) m : ℚ) * centralOffsetGrowthQ m r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrlt : r < m := by omega
      rw [cast_choose_even_center_add_succ m r hrlt,
        centralOffsetGrowthQ_succ, ih (by omega)]
      ring

/-- The symmetric left-offset form of the same even-row transport. -/
theorem cast_choose_even_center_sub_eq_central_mul_offset
    (m r : ℕ) (hr : r ≤ m) :
    (Nat.choose (2 * m) (m - r) : ℚ) =
      (Nat.choose (2 * m) m : ℚ) * centralOffsetGrowthQ m r := by
  have hright : m + r ≤ 2 * m := by omega
  have hsub : 2 * m - (m + r) = m - r := by omega
  rw [← hsub, Nat.choose_symm hright]
  exact cast_choose_even_center_add_eq_central_mul_offset m r hr

/-- Every in-range central offset growth product is nonnegative. -/
theorem centralOffsetGrowthQ_nonneg (m r : ℕ) :
    0 ≤ centralOffsetGrowthQ m r := by
  unfold centralOffsetGrowthQ centralOffsetFactorQ
  exact Finset.prod_nonneg fun j _ => div_nonneg (by positivity) (by positivity)

/--
Exact real Cosmic formula for an arbitrary right-offset cell in an even row.
-/
theorem real_choose_even_center_add_eq_cosmic_mul_offset
    (m r : ℕ) (hr : r ≤ m) :
    ((Nat.choose (2 * m) (m + r) : ℕ) : ℝ) =
      centralBinomialCosmicR m * (centralOffsetGrowthQ m r : ℝ) := by
  calc
    ((Nat.choose (2 * m) (m + r) : ℕ) : ℝ) =
        ((Nat.choose (2 * m) m : ℕ) : ℝ) *
          (centralOffsetGrowthQ m r : ℝ) := by
      exact_mod_cast cast_choose_even_center_add_eq_central_mul_offset m r hr
    _ = centralBinomialCosmicR m * (centralOffsetGrowthQ m r : ℝ) := by
      rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic]

/-!
## Finite-error approximation for offset cells

Multiplying the central interval by the exact nonnegative offset product
transports both its midpoint approximation and its error radius.
-/

/-- Wallis midpoint approximation for `(2*m, m+r)`. -/
noncomputable def evenCellWallisApproxR (m r : ℕ) : ℝ :=
  centralBinomialWallisApproxR m * (centralOffsetGrowthQ m r : ℝ)

/-- Certified absolute-error radius for the offset midpoint approximation. -/
noncomputable def evenCellWallisErrorR (m r : ℕ) : ℝ :=
  centralBinomialWallisErrorR m * (centralOffsetGrowthQ m r : ℝ)

/--
Finite absolute-error guarantee for every right-offset cell in an even row.
The symmetric left-offset cell has the same value by
`cast_choose_even_center_sub_eq_central_mul_offset`.
-/
theorem abs_choose_even_center_add_sub_wallisApprox_le_error
    (m r : ℕ) (hr : r ≤ m) :
    |((Nat.choose (2 * m) (m + r) : ℕ) : ℝ) - evenCellWallisApproxR m r| ≤
      evenCellWallisErrorR m r := by
  rw [real_choose_even_center_add_eq_cosmic_mul_offset m r hr]
  unfold evenCellWallisApproxR evenCellWallisErrorR
  have hoffset : (0 : ℝ) ≤ (centralOffsetGrowthQ m r : ℝ) := by
    exact_mod_cast centralOffsetGrowthQ_nonneg m r
  have hcentral := abs_choose_sub_centralBinomialWallisApproxR_le_error m
  rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic] at hcentral
  rw [← sub_mul, abs_mul, abs_of_nonneg hoffset]
  exact mul_le_mul_of_nonneg_right hcentral hoffset

/-!
## Odd rows

An odd row is obtained from the preceding even row by one exact local lift.
Together with symmetry, the following APIs cover every cell of every odd row.
-/

/-- Local lift from `(2*m, s)` to `(2*m+1, s)`. -/
def oddRowLiftFactorQ (m s : ℕ) : ℚ :=
  ((2 * m + 1 : ℕ) : ℚ) / ((2 * m + 1 - s : ℕ) : ℚ)

/-- Total factor from the even central cell to the left-half odd-row cell. -/
def oddCellGrowthQ (m s : ℕ) : ℚ :=
  centralOffsetGrowthQ m (m - s) * oddRowLiftFactorQ m s

/-- Exact one-step lift from an even row to the next odd row. -/
theorem cast_choose_odd_eq_even_mul_lift (m s : ℕ) (hs : s ≤ m) :
    (Nat.choose (2 * m + 1) s : ℚ) =
      (Nat.choose (2 * m) s : ℚ) * oddRowLiftFactorQ m s := by
  have hden_nat : 0 < 2 * m + 1 - s := by omega
  have hden : ((2 * m + 1 - s : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hden_nat.ne'
  unfold oddRowLiftFactorQ
  rw [← mul_div_assoc]
  apply (eq_div_iff hden).2
  exact_mod_cast (Nat.choose_mul_succ_eq (2 * m) s).symm

/--
Exact factorization of every left-half odd-row cell through the preceding
even central cell.
-/
theorem cast_choose_odd_eq_central_mul_growth (m s : ℕ) (hs : s ≤ m) :
    (Nat.choose (2 * m + 1) s : ℚ) =
      (Nat.choose (2 * m) m : ℚ) * oddCellGrowthQ m s := by
  have heven := cast_choose_even_center_sub_eq_central_mul_offset m (m - s) (by omega)
  rw [Nat.sub_sub_self hs] at heven
  rw [cast_choose_odd_eq_even_mul_lift m s hs, heven]
  unfold oddCellGrowthQ
  ring

/-- The odd-row growth multiplier is nonnegative. -/
theorem oddCellGrowthQ_nonneg (m s : ℕ) :
    0 ≤ oddCellGrowthQ m s := by
  unfold oddCellGrowthQ oddRowLiftFactorQ
  exact mul_nonneg (centralOffsetGrowthQ_nonneg m (m - s))
    (div_nonneg (by positivity) (by positivity))

/-- Exact Cosmic readout for every left-half odd-row cell. -/
theorem real_choose_odd_eq_cosmic_mul_growth (m s : ℕ) (hs : s ≤ m) :
    ((Nat.choose (2 * m + 1) s : ℕ) : ℝ) =
      centralBinomialCosmicR m * (oddCellGrowthQ m s : ℝ) := by
  calc
    ((Nat.choose (2 * m + 1) s : ℕ) : ℝ) =
        ((Nat.choose (2 * m) m : ℕ) : ℝ) * (oddCellGrowthQ m s : ℝ) := by
      exact_mod_cast cast_choose_odd_eq_central_mul_growth m s hs
    _ = centralBinomialCosmicR m * (oddCellGrowthQ m s : ℝ) := by
      rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic]

/-- Wallis midpoint approximation for a left-half odd-row cell. -/
noncomputable def oddCellWallisApproxR (m s : ℕ) : ℝ :=
  centralBinomialWallisApproxR m * (oddCellGrowthQ m s : ℝ)

/-- Certified absolute-error radius for an odd-row approximation. -/
noncomputable def oddCellWallisErrorR (m s : ℕ) : ℝ :=
  centralBinomialWallisErrorR m * (oddCellGrowthQ m s : ℝ)

/-- Finite absolute-error guarantee for every left-half odd-row cell. -/
theorem abs_choose_odd_sub_wallisApprox_le_error
    (m s : ℕ) (hs : s ≤ m) :
    |((Nat.choose (2 * m + 1) s : ℕ) : ℝ) - oddCellWallisApproxR m s| ≤
      oddCellWallisErrorR m s := by
  rw [real_choose_odd_eq_cosmic_mul_growth m s hs]
  unfold oddCellWallisApproxR oddCellWallisErrorR
  have hgrowth : (0 : ℝ) ≤ (oddCellGrowthQ m s : ℝ) := by
    exact_mod_cast oddCellGrowthQ_nonneg m s
  have hcentral := abs_choose_sub_centralBinomialWallisApproxR_le_error m
  rw [real_centralBinomial_eq_four_pow_div_sqrt_cosmic] at hcentral
  rw [← sub_mul, abs_mul, abs_of_nonneg hgrowth]
  exact mul_le_mul_of_nonneg_right hcentral hgrowth

/--
Right-half odd-row error guarantee, obtained by Pascal symmetry.  Thus the
left and right statements together cover the complete odd row.
-/
theorem abs_choose_odd_symmetric_sub_wallisApprox_le_error
    (m s : ℕ) (hs : s ≤ m) :
    |((Nat.choose (2 * m + 1) (2 * m + 1 - s) : ℕ) : ℝ) -
        oddCellWallisApproxR m s| ≤ oddCellWallisErrorR m s := by
  rw [Nat.choose_symm (by omega : s ≤ 2 * m + 1)]
  exact abs_choose_odd_sub_wallisApprox_le_error m s hs

/-!
## Executable natural-number path

The rational evaluator is ideal for algebraic transport, but an implementation
that is intended to produce a big integer should avoid rational normalization.
The following recurrence performs one natural multiplication and one exact
natural division per edge step.  Its correctness is proved from
`Nat.choose_succ_right_eq`.
-/

/-- Edge-to-column recurrence used by the optimized natural evaluator. -/
def pascalCellGrowthNatFastAux (n j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | j + 1 =>
      pascalCellGrowthNatFastAux n j * (n - j) / (j + 1)

theorem pascalCellGrowthNatFastAux_eq_choose (n j : ℕ) :
    pascalCellGrowthNatFastAux n j = Nat.choose n j := by
  induction j with
  | zero => simp [pascalCellGrowthNatFastAux]
  | succ j ih =>
      unfold pascalCellGrowthNatFastAux
      rw [ih]
      apply Nat.div_eq_of_eq_mul_left (Nat.zero_lt_succ j)
      simpa [mul_comm] using (Nat.choose_succ_right_eq n j).symm

/--
Optimized exact big-int evaluator for an arbitrary Pascal cell.

Only `min k (n-k)` recurrence steps are performed, and no `ℚ` values are
constructed.  Out-of-range columns return zero.
-/
def pascalCellGrowthNatFast (n k : ℕ) : ℕ :=
  if k ≤ n then pascalCellGrowthNatFastAux n (min k (n - k)) else 0

theorem pascalCellGrowthNatFast_eq_choose (n k : ℕ) :
    pascalCellGrowthNatFast n k = Nat.choose n k := by
  by_cases hk : k ≤ n
  · rw [pascalCellGrowthNatFast, if_pos hk,
      pascalCellGrowthNatFastAux_eq_choose]
    rcases le_total k (n - k) with hleft | hright
    · rw [min_eq_left hleft]
    · rw [min_eq_right hright, Nat.choose_symm hk]
  · rw [pascalCellGrowthNatFast, if_neg hk]
    norm_num [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

/-!
## Arbitrary Pascal-cell growth evaluator
-/

/-- The local edge-to-center growth factor from column `j` to `j + 1`. -/
def pascalGrowthFactorQ (n j : ℕ) : ℚ :=
  ((n - j : ℕ) : ℚ) / ((j + 1 : ℕ) : ℚ)

/-- Product of the first `k` local Pascal growth factors in row `n`. -/
def pascalPrefixGrowthQ (n k : ℕ) : ℚ :=
  ∏ j ∈ Finset.range k, pascalGrowthFactorQ n j

/--
The prefix growth product is exactly the corresponding binomial coefficient.
This theorem remains true for `k > n`: the product then contains a zero
factor, matching `Nat.choose n k = 0`.
-/
theorem pascalPrefixGrowthQ_eq_cast_choose (n k : ℕ) :
    pascalPrefixGrowthQ n k = (Nat.choose n k : ℚ) := by
  unfold pascalPrefixGrowthQ pascalGrowthFactorQ
  rw [Finset.prod_div_distrib]
  change
    (∏ j ∈ Finset.range k, ((n - j : ℕ) : ℚ)) /
        (∏ j ∈ Finset.range k, ((j + 1 : ℕ) : ℚ)) =
      (Nat.choose n k : ℚ)
  rw [← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range,
    Finset.prod_range_add_one_eq_factorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/--
Exact arbitrary-cell evaluator.  For an in-range cell it uses the shorter of
the left-edge and right-edge growth paths.  Out-of-range columns return `0`,
matching `Nat.choose`.
-/
def pascalCellGrowthQ (n k : ℕ) : ℚ :=
  if k ≤ n then pascalPrefixGrowthQ n (min k (n - k)) else 0

/-- The symmetry-shortened growth index never exceeds half the row. -/
theorem pascalCellGrowthQ_index_le_half (n k : ℕ) :
    min k (n - k) ≤ n / 2 := by
  omega

/-- The arbitrary-cell growth evaluator is exactly `Nat.choose`. -/
theorem pascalCellGrowthQ_eq_cast_choose (n k : ℕ) :
    pascalCellGrowthQ n k = (Nat.choose n k : ℚ) := by
  by_cases hk : k ≤ n
  · rw [pascalCellGrowthQ, if_pos hk, pascalPrefixGrowthQ_eq_cast_choose]
    rcases le_total k (n - k) with hleft | hright
    · rw [min_eq_left hleft]
    · rw [min_eq_right hright, Nat.choose_symm hk]
  · rw [pascalCellGrowthQ, if_neg hk]
    norm_num [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

/--
Natural-number readout of the rational growth evaluator.  Exactness proves
that its denominator is one; `Rat.num` therefore recovers the Pascal cell.
-/
def pascalCellGrowthNat (n k : ℕ) : ℕ :=
  Int.natAbs (pascalCellGrowthQ n k).num

theorem pascalCellGrowthNat_eq_choose (n k : ℕ) :
    pascalCellGrowthNat n k = Nat.choose n k := by
  rw [pascalCellGrowthNat, pascalCellGrowthQ_eq_cast_choose]
  simp

end DkMath.Pascal.WallisCellGrowth
