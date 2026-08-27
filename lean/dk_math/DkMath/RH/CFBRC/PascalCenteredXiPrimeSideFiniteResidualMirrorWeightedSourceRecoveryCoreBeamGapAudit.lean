/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedSourceRecoveryAudit
import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import DkMath.CosmicFormula.CoreBeamGap
import Mathlib.Tactic

/-!
# CS38 amendment: Core--Beam--Gap completion lens

This module adds the structural completion lens to the finite CS38 source
ledger.  The reusable algebra stays in `DkMath.CosmicFormula.CoreBeamGap`;
the RH-specific audit remains here and does not identify the rectangle
remainder with a Core--Beam--Gap term without an exact source bridge.

The prime-mirror offset already supplies one exact quadratic completion:
the square mass is the interaction Big plus the nonnegative square of the
mirror displacement.  This is a finite structural fact, not a sign provider
for the CS38 rectangle difference and not a limiting statement.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.CosmicFormula.CoreBeamGap
open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.CosmicFormula.ThreeElement
open DkMath.RH.CFBRCProjection

/-! ## Core library bridge: the quadratic three-layer identity -/

theorem coreBeamGap_degree_two_complete
    (x δ : ℝ) :
    Big 2 x δ = Core 2 x + Beam 2 x δ + Gap 2 δ := by
  exact big_eq_core_beam_gap (d := 2) (by norm_num) x δ

theorem coreBeamGap_degree_two_beam_eq
    (x δ : ℝ) :
    Beam 2 x δ = 2 * x * δ := by
  simp [Beam]

/-! ## Exact finite mirror completion -/

theorem primeMirrorOffsetState_squareMass_eq_interaction_add_completionGap
    (n : ℕ) (δ : ℝ) :
    squareMass
        (primeMirrorOffsetState n δ).core
        (primeMirrorOffsetState n δ).beam =
      cf2dInteractionBeam (primeMirrorOffsetState n δ) +
        primeMirrorOffsetGap n δ := by
  rw [primeMirrorOffsetState_squareMass_eq_two_add_gap,
    primeMirrorOffsetState_interaction_eq_two]

theorem primeMirrorOffsetCompletionGap_nonneg
    (n : ℕ) (δ : ℝ) :
    0 ≤ primeMirrorOffsetGap n δ := by
  exact primeMirrorOffsetGap_nonneg n δ

theorem primeMirrorOffsetCompletionGap_eq_zero_iff_re_eq_half
    {n : ℕ} (hn : 1 < n) (s : ℂ) :
    primeMirrorOffsetGapAt n s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  exact primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half hn s

/-! ## Bonus: the balanced quadratic witness -/

theorem coreBeamGap_balanced_quadratic_witness :
    Core 2 (1 / 2 : ℝ) = 1 / 4 ∧
      (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 ∧
      Gap 2 (1 / 2 : ℝ) = 1 / 4 ∧
      Big 2 (1 / 2 : ℝ) (1 / 2 : ℝ) = 1 := by
  norm_num [Core, Gap, Big]

/-! ## CS38 amendment frontier -/

inductive PascalCenteredXiPrimeSideFiniteResidualCoreBeamGapBridgeGap : Prop
  | no_exact_source_identification_of_rectangle_remainder

end DkMath.RH.CFBRCProjection
