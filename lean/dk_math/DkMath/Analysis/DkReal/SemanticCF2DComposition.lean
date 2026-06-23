/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.SemanticCF2DRefinement

#print "file: DkMath.Analysis.DkReal.SemanticCF2DComposition"

/-!
# Finite composition of dyadic boundary corrections

At every real phase parameter, normalization satisfies

`phaseNormalization t ^ 2 * phaseDepth t = 1`.

This module restricts that identity to a finite dyadic mesh and composes it
multiplicatively. The resulting theorem is a finite cancellation law. It
does not assert that this product is the canonical refinement limit, and it
does not introduce an infinite product, logarithmic sum, or Gaussian weight.
-/

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/-- All dyadic phase-node indices at level `n`, including both endpoints. -/
def dyadicPhaseNodeIndices (n : ℕ) : Finset ℕ :=
  Finset.range (dyadicPhaseDenom n + 1)

/-- Product of the sampled phase depths over the complete finite mesh. -/
def dyadicPhaseDepthProduct (n : ℕ) : ℝ :=
  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseDepth n k

/-- Product of the sampled boundary normalizations over the complete mesh. -/
def dyadicPhaseNormalizationProduct (n : ℕ) : ℝ :=
  ∏ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseNormalization n k

/-- Pointwise dyadic normalization cancels the corresponding sampled depth. -/
theorem dyadicPhaseNormalization_sq_mul_depth (n k : ℕ) :
    dyadicPhaseNormalization n k ^ 2 * dyadicPhaseDepth n k = 1 := by
  exact phaseNormalization_sq_mul_phaseDepth (dyadicPhaseNode n k)

/--
The squared finite normalization product exactly cancels the finite depth
product on the same dyadic mesh.
-/
theorem dyadicPhaseNormalizationProduct_sq_mul_depthProduct (n : ℕ) :
    dyadicPhaseNormalizationProduct n ^ 2 *
        dyadicPhaseDepthProduct n = 1 := by
  rw [dyadicPhaseNormalizationProduct, dyadicPhaseDepthProduct,
    ← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  simp [dyadicPhaseNormalization_sq_mul_depth]

/-- The finite normalization product is strictly positive. -/
theorem dyadicPhaseNormalizationProduct_pos (n : ℕ) :
    0 < dyadicPhaseNormalizationProduct n := by
  apply Finset.prod_pos
  intro k hk
  exact phaseNormalization_pos (dyadicPhaseNode n k)

/-- The finite depth product is strictly positive. -/
theorem dyadicPhaseDepthProduct_pos (n : ℕ) :
    0 < dyadicPhaseDepthProduct n := by
  apply Finset.prod_pos
  intro k hk
  exact phaseDepth_pos (dyadicPhaseNode n k)

end

end DkMath.Analysis.DkNNRealQ
