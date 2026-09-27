/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.MacroTromino

#print "file: DkMathTest.Tromino.MacroTrominoAxiomAudit"

namespace DkMathTest.Tromino.MacroTrominoAxiomAudit

open DkMath.Polyomino
open DkMath.Polyomino.Tromino
open DkMath.Tromino

example : canonicalMacroFrame.shape = block2 :=
  canonicalMacroFrame_shape

example : macroPositionCount canonicalMacroFrame = 4 :=
  canonicalMacroFrame_macroPositionCount

example : canonicalMacroBody.shape = L_tromino :=
  canonicalMacroBody_shape

example : macroPositionCount canonicalMacroBody = 3 :=
  canonicalMacroBody_macroPositionCount

example : canonicalMacroGap.footprint = hole2 :=
  canonicalMacroGap_footprint

example : canonicalMacroGap.footprint.card = 1 :=
  canonicalMacroGap_footprint_card

example : canonicalMacroGap.expected = atomicFourColorMacroCell :=
  canonicalMacroGap_expected

example : macroPositionCount canonicalMacroBody +
      canonicalMacroGap.footprint.card =
    macroPositionCount canonicalMacroFrame :=
  canonical_macro_count_split

example : macroRestoreRel canonicalMacroFrame canonicalMacroBody canonicalMacroGap :=
  canonical_macroRestoreRel

example {gap₁ gap₂ : MacroGapSlot}
    (h₁ : macroRestoreRel canonicalMacroFrame canonicalMacroBody gap₁)
    (h₂ : macroRestoreRel canonicalMacroFrame canonicalMacroBody gap₂) :
    gap₁.footprint = gap₂.footprint :=
  macroRestoreRel_gap_footprint_unique h₁ h₂

example {gap₁ gap₂ : MacroGapSlot}
    (hfootprint : gap₁.footprint = gap₂.footprint)
    (hne : gap₁.footprint.Nonempty)
    (h₁ : macroRestoreRel canonicalMacroFrame canonicalMacroBody gap₁)
    (h₂ : macroRestoreRel canonicalMacroFrame canonicalMacroBody gap₂) :
    gap₁.expected = gap₂.expected :=
  macroRestoreRel_expected_unique hfootprint hne h₁ h₂

example : atomicPayloadMass canonicalMacroBody = 12 :=
  canonicalMacroBody_atomicPayloadMass

example : atomicCellCount canonicalMacroGap.expected = 4 :=
  canonicalMacroGap_atomicPayloadMass

example : atomicPayloadMass canonicalMacroFrame = 16 :=
  canonicalMacroFrame_atomicPayloadMass

example : atomicPayloadMass canonicalMacroBody +
      atomicCellCount canonicalMacroGap.expected =
    atomicPayloadMass canonicalMacroFrame :=
  canonical_atomic_mass_split

example : atomicPayloadMass canonicalMacroFrame =
      4 * macroPositionCount canonicalMacroFrame :=
  canonical_atomic_mass_scale

#print axioms DkMath.Tromino.macroRestoreRel_shape_part
#print axioms DkMath.Tromino.macroRestoreRel_gap_footprint_unique
#print axioms DkMath.Tromino.macroRestoreRel_expected_unique
#print axioms DkMath.Tromino.canonical_macroRestoreRel
#print axioms DkMath.Tromino.canonical_macro_count_split
#print axioms DkMath.Tromino.atomicPayloadMass_eq_four_mul_card_of_constant
#print axioms DkMath.Tromino.canonicalMacroBody_atomicPayloadMass
#print axioms DkMath.Tromino.canonicalMacroFrame_atomicPayloadMass
#print axioms DkMath.Tromino.canonical_atomic_mass_split
#print axioms DkMath.Tromino.canonical_atomic_mass_scale

end DkMathTest.Tromino.MacroTrominoAxiomAudit
