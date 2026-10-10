/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit"

namespace DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open SevenCyclotomicDegreeSixInt
local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)

example : ∀ i : Fin 6, sixSlotRoot (11 : ZMod 43) i = ![11, 35, 41, 21, 16, 4] i := by decide
example : orderOf (11 : ZMod 43) = 7 := seventhRoot_orderOf _ (by decide) (by decide)
example : Function.Injective (sixSlotRoot (11 : ZMod 43)) :=
  sixSlotRoot_injective _ (by decide) (by decide)
example : ∀ i : Fin 6, sixSlotRoot (11 : ZMod 43) i ^ 7 = 1 ∧
    sixSlotRoot (11 : ZMod 43) i ≠ 0 ∧ sixSlotRoot (11 : ZMod 43) i ≠ 1 := fun i =>
  ⟨sixSlotRoot_pow_seven _ (by decide) i, sixSlotRoot_ne_zero _ (by decide) i,
    sixSlotRoot_ne_one _ (by decide) (by decide) i⟩
example : ∀ i : Fin 6, (K i).IsMaximal ∧ (K i).IsPrime := fun i =>
  ⟨sixRootKernel_isMaximal _ _ _ _ i, sixRootKernel_isPrime _ _ _ _ i⟩
example : ∀ i : Fin 6, Submodule.cardQuot (K i) = 43 := sixRootKernel_cardQuot _ _ _ _
example : ∀ i : Fin 6, Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring) (K i) =
    Ideal.span ({(43 : ℤ)} : Set ℤ) := sixRootKernel_comap_intCast _ _ _ _
example : ∀ i j : Fin 6, i ≠ j → K i ≠ K j := sixRootKernel_ne _ _ _ _
example : ∀ i j : Fin 6, i ≠ j → K i ⊔ K j = ⊤ := sixRootKernel_sup_eq_top _ _ _ _

private theorem ratio11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

private theorem selective43 (i : Fin 6) : gtailCyclotomicLinearFactor 9 4 ∈ K i ↔ i = 0 := by
  have h := gtailCyclotomicLinearFactor_mem_sixRootKernel_iff
    (q := 43) 9 4 (by decide) (by decide) (by decide) i
  simpa only [ratio11] using h

example : ∀ i : Fin 6, gtailCyclotomicLinearFactor 9 4 ∈ K i ↔ i = 0 := selective43
example : gtailCyclotomicLinearFactor 9 4 ∈ K 0 := (selective43 0).mpr rfl
example : ∀ i : Fin 6, i ≠ 0 → gtailCyclotomicLinearFactor 9 4 ∉ K i := by
  intro i hi
  rw [selective43]
  exact hi
example : ∃! i : Fin 6, gtailCyclotomicLinearFactor 9 4 ∈ K i := by
  refine ⟨0, (selective43 0).mpr rfl, ?_⟩
  intro i hi
  exact (selective43 i).mp hi

-- Actual evaluations of the factor in all six slots.
example : ∀ i : Fin 6,
    evalCyclotomicFromSeventhRoot (sixSlotRoot (11 : ZMod 43) i)
        (sixSlotRoot_ne_zero _ (by decide) i) (sixSlotRoot_pow_seven _ (by decide) i)
        (sixSlotRoot_ne_one _ (by decide) (by decide) i) (gtailCyclotomicLinearFactor 9 4) =
      ![0, 42, 31, 39, 41, 20] i := by
  intro i
  simp only [gtailCyclotomicLinearFactor, map_sub, map_mul,
    evalCyclotomicFromSeventhRoot_zeta, map_natCast]
  change (13 : ZMod 43) - sixSlotRoot (11 : ZMod 43) i * 9 = _
  revert i
  decide
example : (13 : ZMod 43) - 35 * 9 = 42 ∧ (13 : ZMod 43) - 35 * 9 ≠ 0 := by decide

-- Original neutral arithmetic does not supply a Fermat solution.
example : (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 ∧ 43 ∣ GTail 7 1 4 9 := by decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide
example : (13 : ℕ) ∣ 14 ^ 2 + 14 * 29 + 29 ^ 2 ∧ (13 : ℕ) ∣ 13 ∧
    ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ¬ ∃ r : ZMod 7, r ^ 7 = 1 ∧ r ≠ 1 := by decide
example : ramifiedEval zeta = (1 : ZMod 7) := ramifiedEval_zeta
example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 ∧ (2 : ZMod 3) = 1 - 2 := by decide
example : ¬ ∃ t : ZMod 5, t ^ 2 - t + 1 = 0 := by decide
example : ∀ i : Fin 6, gtailCyclotomicLinearFactor 0 0 ∈ K i := by
  intro i
  simp [gtailCyclotomicLinearFactor]

#print axioms DkMath.FLT.Seven.sixSlotRoot
#print axioms DkMath.FLT.Seven.seventhRoot_orderOf
#print axioms DkMath.FLT.Seven.sixSlotRoot_zero
#print axioms DkMath.FLT.Seven.sixSlotRoot_pow_seven
#print axioms DkMath.FLT.Seven.sixSlotRoot_ne_zero
#print axioms DkMath.FLT.Seven.sixSlotRoot_ne_one
#print axioms DkMath.FLT.Seven.sixSlotRoot_injective
#print axioms DkMath.FLT.Seven.sixRootKernel
#print axioms DkMath.FLT.Seven.mem_sixRootKernel_iff
#print axioms DkMath.FLT.Seven.sixRootKernel_isMaximal
#print axioms DkMath.FLT.Seven.sixRootKernel_isPrime
#print axioms DkMath.FLT.Seven.sixRootKernel_comap_intCast
#print axioms DkMath.FLT.Seven.sixRootKernel_cardQuot
#print axioms DkMath.FLT.Seven.sixRootKernel_ne
#print axioms DkMath.FLT.Seven.sixRootKernel_sup_eq_top
#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_sixRootKernel_iff
#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor_mem_sixRootKernel_zero
#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor_not_mem_sixRootKernel

end DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit
