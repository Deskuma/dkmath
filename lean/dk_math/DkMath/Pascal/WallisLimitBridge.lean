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

/--
The explicit ordered Wallis-factor product, after coercion to `ℝ`, is
Mathlib's Wallis product `Real.Wallis.W`.
-/
theorem real_coe_prod_wallisFactorQ_eq_Wallis_W (m : ℕ) :
    ((∏ k ∈ Finset.range m, wallisFactorQ k : ℚ) : ℝ) =
      Real.Wallis.W m := by
  rw [← real_coe_wallisPartialQ_eq_Wallis_W]
  rfl

/-- The finite Wallis and cosmic partial products are pointwise equal over `ℝ`. -/
theorem real_coe_wallisPartialQ_eq_cosmicPartialQ (m : ℕ) :
    ((wallisPartialQ m : ℚ) : ℝ) =
      ((cosmicPartialQ m : ℚ) : ℝ) := by
  exact_mod_cast wallisPartialQ_eq_cosmicPartialQ m

/--
The explicit ordered cosmic-factor product, after coercion to `ℝ`, is also
Mathlib's Wallis product `Real.Wallis.W`.
-/
theorem real_coe_prod_cosmicFactorQ_eq_Wallis_W (m : ℕ) :
    ((∏ k ∈ Finset.range m, cosmicFactorQ k : ℚ) : ℝ) =
      Real.Wallis.W m := by
  rw [← real_coe_wallisPartialQ_eq_Wallis_W]
  exact_mod_cast (wallisPartialQ_eq_cosmicPartialQ m).symm

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

/-!
## Conditional infinite-product surface

Mathlib's plain `HasProd` uses the unconditional summation filter by default.
That is stronger than the classical Wallis statement used here, which is a
limit of ordered partial products over `Finset.range m`.

For this module, the Lean-faithful infinite-product API is therefore

`HasProd f L (SummationFilter.conditional ℕ)`.

On `ℕ`, this conditional filter is definitionally the `range m` exhaustion
filter.  The lemmas below are deliberately stated with
`SummationFilter.conditional ℕ` to avoid accidentally claiming unordered
unconditional multipliability.

TODO: If a later layer really needs unconditional `HasProd`, prove it from a
separate absolute/log-product summability argument.  Do not silently replace
the conditional statements below by default `HasProd` statements.
-/

/--
For products indexed by `ℕ`, `SummationFilter.conditional ℕ` is exactly the
classical ordered partial-product filter over `Finset.range m`.
-/
theorem hasProd_conditional_nat_iff
    {M : Type*} [CommMonoid M] [TopologicalSpace M]
    {f : ℕ → M} {a : M} :
    HasProd f a (SummationFilter.conditional ℕ) ↔
      Tendsto (fun m : ℕ => ∏ k ∈ Finset.range m, f k) atTop (𝓝 a) := by
  rw [HasProd, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/--
The real Wallis factors have ordered infinite product `Real.pi / 2`.

This is the `HasProd`-surface version of
`tendsto_wallisPartialQ_pi_div_two`, with the conditional `ℕ` filter made
explicit.
-/
theorem hasProd_conditional_real_coe_wallisFactorQ_pi_div_two :
    HasProd
      (fun k : ℕ => ((wallisFactorQ k : ℚ) : ℝ))
      (Real.pi / 2)
      (SummationFilter.conditional ℕ) := by
  rw [hasProd_conditional_nat_iff]
  exact tendsto_wallisPartialQ_pi_div_two.congr' <|
    Eventually.of_forall fun m => by
      unfold wallisPartialQ
      rw [Rat.cast_prod]

/--
The real cosmic factors have ordered infinite product `Real.pi / 2`.

This is the infinite-product form of the cosmic gap product route:
finite cosmic partial products are pointwise the Wallis partial products, and
the Wallis partial products converge to `Real.pi / 2`.
-/
theorem hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two :
    HasProd
      (fun k : ℕ => ((cosmicFactorQ k : ℚ) : ℝ))
      (Real.pi / 2)
      (SummationFilter.conditional ℕ) := by
  rw [hasProd_conditional_nat_iff]
  exact tendsto_cosmicPartialQ_pi_div_two.congr' <|
    Eventually.of_forall fun m => by
      unfold cosmicPartialQ
      rw [Rat.cast_prod]

/--
The ordered infinite product of the cosmic gap ratios
`1 + 1 / N_k` is `Real.pi / 2`.

This is the semantic Wallis-Cosmic statement: the local factor is not merely a
Wallis factor, but the cosmic gap ratio coming from
`N_k = (2*k+1)*(2*k+3)`.
-/
theorem hasProd_conditional_real_cosmic_gap_ratio_pi_div_two :
    HasProd
      (fun k : ℕ => ((1 + 1 / cosmicBodyQ k : ℚ) : ℝ))
      (Real.pi / 2)
      (SummationFilter.conditional ℕ) := by
  exact hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two.congr_fun
    (fun k => by
      exact_mod_cast (cosmicFactorQ_eq_one_add_inv_body k).symm)

/--
The conditional `tprod` of the real cosmic factors is `Real.pi / 2`.

This is a value-level alias for callers that want `tprod` rather than
`HasProd`.
-/
theorem tprod_conditional_real_coe_cosmicFactorQ_eq_pi_div_two :
    (∏'[SummationFilter.conditional ℕ] k : ℕ, ((cosmicFactorQ k : ℚ) : ℝ)) =
      Real.pi / 2 :=
  hasProd_conditional_real_coe_cosmicFactorQ_pi_div_two.tprod_eq

/--
The conditional `tprod` of the real cosmic gap ratios
`1 + 1 / N_k` is `Real.pi / 2`.
-/
theorem tprod_conditional_real_cosmic_gap_ratio_eq_pi_div_two :
    (∏'[SummationFilter.conditional ℕ] k : ℕ,
      ((1 + 1 / cosmicBodyQ k : ℚ) : ℝ)) =
      Real.pi / 2 :=
  hasProd_conditional_real_cosmic_gap_ratio_pi_div_two.tprod_eq

end DkMath.Pascal.WallisLimitBridge
