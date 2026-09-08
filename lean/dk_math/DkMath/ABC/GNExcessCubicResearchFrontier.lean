/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicRealizedBoundary
import DkMath.ABC.GNExcessCubicRealizedDyadic
import DkMath.ABC.GNExcessCubicSevenDepthIncidence

#print "file: DkMath.ABC.GNExcessCubicResearchFrontier"

/-!
# LUNA-022: ABC–GN cubic research-frontier capstone

This module is a composition checkpoint and deliberately contains no new
substantial arithmetic proof.

PRODUCTION-PROVED:
  deterministic reduction through realized dyadic shell counts.

OPEN:
  a nontrivial upper bound for
  `GNExcessCubicRealizedLargeModulusShellCount X D`.

NOT CLAIMED:
  ABC, density, relative-height exclusion, or shell sparsity.

The existing endpoint theorem says that every represented dyadic index `k`
satisfies `X + 1 < 2^(k+1)` and `2^k ≤ 3*(X+1)^2`.  The finite incidence
ledger already records shell-card domination by witness cards, the exact
modulus/complement/pair/Pell fiber decompositions, the exceptional-three and
paired orientation refinements, and the LUNA-021 seven-state partitions.
None of these identities is a state-count estimate.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## End-to-end provider-free capstone -/

theorem exp_GNExcessMassAt_sum_cubic_three_eighths_le_of_dyadicShellCardBounds
    {X : ℕ} (B : ℕ → ℝ)
    (hB : ∀ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
      (GNExcessCubicRealizedLargeModulusShellCount X (2 ^ k) : ℝ) ≤ B k) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp ((3 / 8 : ℝ) * GNExcessMassAt
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X
            (3 / 8 : ℝ) +
        ∑ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
          B k * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (3 / 8 : ℝ) := by
  have hbridge :=
    exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment
      (X := X)
  have hmoment :=
    GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds
      (X := X) B hB
  exact hbridge.trans (add_le_add (le_refl _) hmoment)

end DkMath.ABC
