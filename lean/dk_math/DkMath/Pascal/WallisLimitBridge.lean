/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Analysis.DkLimit
import DkMath.Pascal.WallisCosmicPetalBridge

#print "file: DkMath.Pascal.WallisLimitBridge"

/-!
# Wallis limit bridge

This module is the limit-facing layer for the finite Wallis-Cosmic Petal
bridge.  The finite algebraic API remains in
`DkMath.Pascal.WallisCosmicPetalBridge`.

The following three real sequences are pointwise equal:

* `fun m => ((wallisPartialQ m : ℚ) : ℝ)`;
* `fun m => ((cosmicPartialQ m : ℚ) : ℝ)`;
* `fun m => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ))`.

Mathlib's Wallis theorem then sends each of them to `Real.pi / 2`.
-/

namespace DkMath.Pascal.WallisLimitBridge

open scoped BigOperators
open Filter Topology
open DkMath.Pascal.WallisCosmicPetalBridge

/--
The finite rational Wallis partial product, after coercion to `ℝ`, is
Mathlib's Wallis product `Real.Wallis.W`.
-/
theorem real_coe_wallisPartialQ_eq_Wallis_W (m : ℕ) :
    ((wallisPartialQ m : ℚ) : ℝ) = Real.Wallis.W m := by
  unfold wallisPartialQ Real.Wallis.W wallisFactorQ evenCenterQ oddLeftQ oddRightQ
  rw [Rat.cast_prod]
  exact Finset.prod_congr rfl fun k _ => by
    norm_num
    field_simp

/-- The finite Wallis and cosmic partial products are pointwise equal over `ℝ`. -/
theorem real_coe_wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
    ((wallisPartialQ m : ℚ) : ℝ) =
      ((cosmicPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m

/--
The proof-note central-ratio expression is pointwise equal to the finite
Wallis product over `ℝ`.
-/
theorem real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ (m : ℕ) :
    (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
      ((wallisPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_mul_mirror_eq_wallisPartialQ m

/--
The proof-note central-ratio expression is pointwise equal to the finite
cosmic gap product over `ℝ`.
-/
theorem real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ (m : ℕ) :
    (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)) =
      ((cosmicPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast centralRatioQ_mul_mirror_eq_cosmicPartialQ m

/--
The real coercion of the finite rational Wallis partial products tends to
`Real.pi / 2`, by Mathlib's Wallis product theorem.
-/
theorem tendsto_real_coe_wallisPartialQ_nhds_pi_div_two :
    Tendsto (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ)) atTop (𝓝 (Real.pi / 2)) := by
  exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr' <|
    Eventually.of_forall fun m => (real_coe_wallisPartialQ_eq_Wallis_W m).symm

/--
The rational Wallis partial products tend to `Real.pi / 2` after coercion to `ℝ`.
-/
theorem tendsto_wallisPartialQ_pi_div_two :
    Filter.Tendsto
      (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ))
      Filter.atTop
      (nhds (Real.pi / 2)) :=
  tendsto_real_coe_wallisPartialQ_nhds_pi_div_two

/--
The rational cosmic partial products tend to `Real.pi / 2` after coercion to `ℝ`.
-/
theorem tendsto_cosmicPartialQ_pi_div_two :
    Filter.Tendsto
      (fun m : ℕ => ((cosmicPartialQ m : ℚ) : ℝ))
      Filter.atTop
      (nhds (Real.pi / 2)) := by
  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
    Eventually.of_forall real_coe_wallisPartialQ_eq_cosmicPartialQ

/--
The proof-note expression
`centralRatioQ m * mirrorOddRatioPartialQ m` tends to `Real.pi / 2`.

This is the main public central-ratio route: pointwise, it is the finite
cosmic gap product, and the cosmic partial products share the Wallis limit.
-/
theorem tendsto_centralRatioQ_mul_mirror_pi_div_two :
    Filter.Tendsto
      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
      Filter.atTop
      (nhds (Real.pi / 2)) := by
  exact tendsto_cosmicPartialQ_pi_div_two.congr' <|
    Eventually.of_forall fun m =>
      (real_coe_centralRatioQ_mul_mirror_eq_cosmicPartialQ m).symm

/--
The same proof-note expression tends to `Real.pi / 2`, routed through the
finite Wallis product stage instead of the cosmic gap product.
-/
theorem tendsto_centralRatioQ_mul_mirror_via_wallis_pi_div_two :
    Filter.Tendsto
      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
      Filter.atTop
      (nhds (Real.pi / 2)) := by
  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
    Eventually.of_forall fun m =>
      (real_coe_centralRatioQ_mul_mirror_eq_wallisPartialQ m).symm

/--
DkMath-named alias for the Wallis partial product convergence.
-/
theorem dkTendsto_wallisPartialQ_pi_div_two :
    DkMath.Analysis.DkTendstoAtTop
      (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ))
      (Real.pi / 2) :=
  tendsto_wallisPartialQ_pi_div_two

/--
DkMath-named alias for the cosmic partial product convergence.
-/
theorem dkTendsto_cosmicPartialQ_pi_div_two :
    DkMath.Analysis.DkTendstoAtTop
      (fun m : ℕ => ((cosmicPartialQ m : ℚ) : ℝ))
      (Real.pi / 2) :=
  tendsto_cosmicPartialQ_pi_div_two

/--
DkMath-named alias for convergence of the proof-note central-ratio expression.
-/
theorem dkTendsto_centralRatioQ_mul_mirror_pi_div_two :
    DkMath.Analysis.DkTendstoAtTop
      (fun m : ℕ => (((centralRatioQ m * mirrorOddRatioPartialQ m : ℚ) : ℝ)))
      (Real.pi / 2) :=
  tendsto_centralRatioQ_mul_mirror_pi_div_two

end DkMath.Pascal.WallisLimitBridge
