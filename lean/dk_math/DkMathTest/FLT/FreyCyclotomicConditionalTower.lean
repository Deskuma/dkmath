/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalTower

#print "file: DkMathTest.FLT.FreyCyclotomicConditionalTower"

namespace DkMathTest.FLT.FreyCyclotomicConditionalTower

open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)

-- The original base stage requires neither class vanishing nor resonant absorption.
example : (S.residualCyclicStageZero L hline hcofixed).carrier =
    pointSubgroup S.rationalCurve p L := rfl
example : Nat.card (S.residualCyclicStageZero L hline hcofixed).carrier = p := by
  simpa only [zero_add, pow_one] using (S.residualCyclicStageZero L hline hcofixed).card

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)

local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "towerUnion" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad

-- Exact first three sizes in the SAME chosen coherent tower.
example : Nat.card (tower 0).carrier = p ∧ Nat.card (tower 1).carrier = p ^ 2 ∧
    Nat.card (tower 2).carrier = p ^ 3 := by
  exact ⟨by simpa only [zero_add, pow_one] using (tower 0).card,
    (tower 1).card, (tower 2).card⟩

-- Compose two actual lifts: a root of an original base point exists in stage TWO,
-- not in two independently chosen unrelated groups.
example (x : Points S.rationalCurve) (hx : x ∈ pointSubgroup S.rationalCurve p L) :
    ∃ y ∈ (tower 2).carrier, p ^ 2 • y = x := by
  obtain ⟨y, hy, he⟩ := S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad 0 x hx
  obtain ⟨z, hz, hez⟩ := S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad 1 y hy
  refine ⟨z, hz, ?_⟩
  rw [pow_two, mul_nsmul, hez, he]

-- p-torsion of a late stage still lies in the ORIGINAL subgroup, not merely the previous one.
example (x : Points S.rationalCurve) (hx : x ∈ (tower 4).carrier) (hpx : p • x = 0) :
    x ∈ pointSubgroup S.rationalCurve p L := (tower 4).socle_mem_base hline hx hpx

-- The same union is p-divisible and has exactly the original socle.
example (x : Points S.rationalCurve) (hx : x ∈ towerUnion) :
    ∃ y ∈ towerUnion, p • y = x :=
  S.residualCyclicTowerUnion_divisible L hline hcofixed hζ hp5 hclass hbad x hx
example (x : Points S.rationalCurve) :
    (x ∈ towerUnion ∧ p • x = 0) ↔ x ∈ pointSubgroup S.rationalCurve p L :=
  S.residualCyclicTowerUnion_socle L hline hcofixed hζ hp5 hclass hbad x

-- Infinite union has Nat.card=0; this must never be treated as a zero finite group.
example : Infinite towerUnion ∧ Nat.card towerUnion = 0 := by
  have hi := S.residualCyclicTowerUnion_infinite L hline hcofixed hζ hp5 hclass hbad
  let := hi
  exact ⟨hi, Nat.card_eq_zero_of_infinite⟩

#print axioms Source.ResidualCyclicStage.finite
#print axioms Source.ResidualCyclicStage.killed
#print axioms Source.ResidualCyclicStage.socle_mem_base
#print axioms Source.residual_cyclic_stage_successor
#print axioms Source.residualCyclicNext_spec
#print axioms Source.residualCyclicTower
#print axioms Source.residualCyclicTower_monotone
#print axioms Source.residualCyclicTower_profile
#print axioms Source.residualCyclicTower_lift
#print axioms Source.mem_residualCyclicTowerUnion
#print axioms Source.residualCyclicTowerUnion_primary
#print axioms Source.residualCyclicTowerUnion_divisible
#print axioms Source.residualCyclicTowerUnion_stable
#print axioms Source.residualCyclicTowerUnion_socle
#print axioms Source.residualCyclicTowerUnion_infinite

end
end DkMathTest.FLT.FreyCyclotomicConditionalTower
