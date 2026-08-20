/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenUnitClassification

/-!
# Golden-unit fifth-power Red Ribbon bridge

This module exposes the existing FLT5 golden-unit classification through a
relation-valued StructuralArithmetic observer.  `GoldenFifthSector i x` says
that `x` has the visible representative `goldenPhi ^ i`; the remaining factor
is an existential fifth-power witness.  The observer is deliberately not a
choice-valued sector function, so this file makes no uniqueness claim.

The fifth-power absorption theorem is the golden-order counterpart of the
natural prime-coordinate period theorem.  It is a structural analogy only:
golden-unit classes, prime-exponent period five, and ordinary additive
congruence modulo five remain distinct constructions.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

open DkMath.FLT.Five

/-- A relation-valued visible sector for a golden integer modulo fifth powers. -/
def GoldenFifthSector (i : Fin 5) (x : GoldenInt) : Prop :=
  ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)

/-- The StructuralArithmetic sector relation is exactly the existing FLT5 class predicate. -/
theorem goldenUnitFifthClass_iff_exists_sector {x : GoldenInt} :
    GoldenUnitFifthClass x ↔ ∃ i : Fin 5, GoldenFifthSector i x := by
  rfl

/-- Every golden unit admits a visible fifth-power sector witness. -/
theorem goldenUnit_has_fifthSector
    {epsilon : GoldenInt} (hUnit : GoldenUnit epsilon) :
    ∃ i : Fin 5, GoldenFifthSector i epsilon := by
  obtain ⟨i, delta, hclass⟩ := goldenUnitFifthClass_of_unit epsilon hUnit
  exact ⟨i, delta, hclass⟩

namespace GoldenFifthSector

/-- Multiplication by a complete fifth power preserves a fixed visible sector. -/
theorem mul_fifthPower
    {i : Fin 5} {x : GoldenInt}
    (hx : GoldenFifthSector i x) (eta : GoldenInt) :
    GoldenFifthSector i (goldenMul x (goldenPow eta 5)) := by
  rcases hx with ⟨delta, hdelta⟩
  refine ⟨goldenMul delta eta, ?_⟩
  rw [hdelta]
  simp only [golden_mul_eq, golden_pow_eq]
  rw [mul_pow]
  ring

end GoldenFifthSector

/-- Each explicit representative `goldenPhi ^ i` lies in its named sector. -/
@[simp] theorem goldenPhiPow_mem_fifthSector (i : Fin 5) :
    GoldenFifthSector i (goldenPow goldenPhi i.val) := by
  refine ⟨goldenOne, ?_⟩
  change goldenPhi ^ i.val = goldenPhi ^ i.val * (1 : GoldenInt) ^ 5
  simp

/-- Every stripped FLT5 golden packet obtains a StructuralArithmetic sector witness. -/
theorem signedGoldenPacket_has_fifthSector
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    ∃ i : Fin 5, GoldenFifthSector i p.beta := by
  obtain ⟨i, gamma, hbeta⟩ :=
    signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth p
  exact ⟨i, gamma, hbeta⟩

end DkMath.NumberTheory.StructuralArithmetic
