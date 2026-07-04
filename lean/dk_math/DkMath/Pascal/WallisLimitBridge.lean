/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Pascal.WallisCosmicPetalBridge

#print "file: DkMath.Pascal.WallisLimitBridge"

/-!
# Wallis limit bridge

This module is the limit-facing layer for the finite Wallis-Cosmic Petal
bridge.  The finite algebraic API remains in
`DkMath.Pascal.WallisCosmicPetalBridge`.
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

/--
The real coercion of the finite rational Wallis partial products tends to
`Real.pi / 2`, by Mathlib's Wallis product theorem.
-/
theorem tendsto_real_coe_wallisPartialQ_nhds_pi_div_two :
    Tendsto (fun m : ℕ => ((wallisPartialQ m : ℚ) : ℝ)) atTop (𝓝 (Real.pi / 2)) := by
  exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr' <|
    Eventually.of_forall fun m => (real_coe_wallisPartialQ_eq_Wallis_W m).symm

end DkMath.Pascal.WallisLimitBridge
