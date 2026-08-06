/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.ThreeElement.MagicCore

#print "file: DkMathTest.CosmicFormula.ThreeElement.MagicCore"

namespace DkMathTest.CosmicFormula.ThreeElement.MagicCore

open DkMath.CosmicFormula.ThreeElement

example {B : ℝ} (hB : 0 ≤ B) :
    coreTerm (Real.sqrt B) = B := by
  exact core_sqrt_realizes hB

example {B : ℝ} (hB : 0 ≤ B) :
    gapTerm (Real.sqrt B) = B := by
  exact gap_sqrt_realizes hB

example {B : ℝ} (hB : 0 ≤ B) :
    interactionBeam
      (Real.sqrt (B / 2))
      (Real.sqrt (B / 2)) = B := by
  exact symmetric_interaction_sqrt_realizes hB

example (B : ℝ) (hB : 0 ≤ B) :
    SymmetricMagicCoreRealization B :=
  symmetricMagicCoreRealization B hB

example (B : ℝ) (hB : 0 ≤ B) :
    (symmetricMagicCoreRealization B hB).coreRoot = Real.sqrt B := by
  rfl

example (B : ℝ) (hB : 0 ≤ B) :
    (symmetricMagicCoreRealization B hB).interactionRoot =
      Real.sqrt (B / 2) := by
  rfl

example (B : ℝ) (hB : 0 ≤ B) :
    (symmetricMagicCoreRealization B hB).gapRoot = Real.sqrt B := by
  rfl

#print axioms DkMath.CosmicFormula.ThreeElement.core_sqrt_realizes
#print axioms DkMath.CosmicFormula.ThreeElement.gap_sqrt_realizes
#print axioms DkMath.CosmicFormula.ThreeElement.symmetric_interaction_sqrt_realizes
#print axioms DkMath.CosmicFormula.ThreeElement.symmetricMagicCoreRealization

end DkMathTest.CosmicFormula.ThreeElement.MagicCore
