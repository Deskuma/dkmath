/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom

#print "file: DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom"

namespace DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

-- Small finite facts precede the integral-map conclusions.
example : (7 : ZMod 29) ^ 7 = 1 ∧ (7 : ZMod 29) ≠ 1 ∧ (7 : ZMod 29) ≠ 0 := by decide
example : ∀ x : ZMod 29, x ^ 2 - x + 1 ≠ 0 := no_eisenstein_root_zmod29
example : (4 : ZMod 13) ^ 2 - 4 + 1 = 0 := eisenstein_root_zmod13
example : ∀ x : ZMod 13, 1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 ≠ 0 :=
  no_seven_geom_root_zmod13
example : ∀ x : ZMod 29, (x ^ 7 = 1 ∧ x ≠ 1) ↔
    x = 7 ∨ x = 16 ∨ x = 20 ∨ x = 23 ∨ x = 24 ∨ x = 25 := by decide
example : ∀ x : ZMod 13, x ^ 2 - x + 1 = 0 ↔ x = 4 ∨ x = 10 := by decide
-- Transporting only the seventh-power equality would miss the image one.
example : (1 : ZMod 13) ^ 7 = 1 ∧
    1 + (1 : ZMod 13) + 1 ^ 2 + 1 ^ 3 + 1 ^ 4 + 1 ^ 5 + 1 ^ 6 ≠ 0 := by decide

example : Nonempty (Ring →+* ZMod 29) :=
  ⟨evalCyclotomicFromSeventhRoot (7 : ZMod 29)
    seven_root_zmod29.1 seven_root_zmod29.2.1 seven_root_zmod29.2.2⟩
example : evalCyclotomicFromSeventhRoot (7 : ZMod 29)
    seven_root_zmod29.1 seven_root_zmod29.2.1 seven_root_zmod29.2.2 zeta = 7 :=
  evalCyclotomicFromSeventhRoot_zeta _ _ _ _
example : Nonempty (TraceOneInt (-1) →+* ZMod 13) :=
  ⟨eisensteinResidueRingHom (4 : ZMod 13) eisenstein_root_zmod13⟩
example : eisensteinResidueRingHom (4 : ZMod 13) eisenstein_root_zmod13 (tau (-1)) = 4 :=
  eisensteinResidueRingHom_tau _ _

example : ¬ Nonempty (TraceOneInt (-1) →+* Ring) :=
  not_nonempty_eisenstein_to_seven_cyclotomic
example : ¬ Nonempty (Ring →+* TraceOneInt (-1)) :=
  not_nonempty_seven_cyclotomic_to_eisenstein

-- Both actual source rings still map to a common finite field, independently.
example : Nonempty (TraceOneInt (-1) →+* ZMod 43) ∧ Nonempty (Ring →+* ZMod 43) :=
  ⟨⟨eisensteinResidueRingHom (37 : ZMod 43) (by decide)⟩,
    ⟨evalCyclotomicFromSeventhRoot (11 : ZMod 43) (by decide) (by decide) (by decide)⟩⟩
example : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 ∧ (11 : ZMod 43) ^ 7 = 1 ∧
    (11 : ZMod 43) ≠ 1 ∧ (37 : ZMod 43) ≠ 11 := by decide

-- The old norm-coordinate function targets the discriminant -7 companion, not E.
example (z y : ℤ) : TraceOneInt (-2) := cyclotomicSevenToTraceOne z y
example (a b : ℕ) : TraceOneInt (-1) := gtailSevenNormCoord a b
example : discr (-1) = -3 ∧ discr (-2) = -7 := by decide
example : norm (tau (-1)) = 1 ∧ norm (tau (-2)) = 2 := by decide

-- Arithmetic equivalence and non-Fermat calibration remain separate from no-hom proofs.
example (a b c g : ℕ) (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ g * DkMath.CosmicFormula.GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 :=
  fermat7Equation_iff_focused_scalar_balance hfocus
example : (1166 + 1857 : ℕ) = 1858 + 1165 ∧ ¬ Fermat7Equation 1166 1857 1858 := by
  unfold Fermat7Equation
  decide

-- Ramified / Gap-only contrasts do not fabricate Tail input at q29 or q13.
example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 ∧ (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ DkMath.CosmicFormula.GTail 7 1 13 30 := by decide

#check RingHom.comp
#check RingHom.comp_apply
#check map_pow
#check map_sub
#check map_add
#check map_one
#check map_intCast

#print axioms DkMath.FLT.Seven.seven_root_zmod29
#print axioms DkMath.FLT.Seven.no_eisenstein_root_zmod29
#print axioms DkMath.FLT.Seven.eisenstein_root_zmod13
#print axioms DkMath.FLT.Seven.no_seven_geom_root_zmod13
#print axioms DkMath.FLT.Seven.not_nonempty_eisenstein_to_seven_cyclotomic
#print axioms DkMath.FLT.Seven.not_nonempty_seven_cyclotomic_to_eisenstein

end DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom
