/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal

#print "file: DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal"

namespace DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

local notation "π" => eisensteinThreeGenerator
local notation "P" => eisensteinThreeRamifiedIdeal
local notation "I3" => eisensteinScalarIdeal 3

example : (2 : ZMod 3) ^ 2 - 2 + 1 = 0 := eisensteinThreeRoot
example : (2 : ZMod 3) = 1 - 2 := by decide
example : π = (⟨1, 1⟩ : TraceOneInt (-1)) := eisensteinThreeGenerator_eq
example : norm π = 3 := norm_eisensteinThreeGenerator
example : conj π = (⟨2, -1⟩ : TraceOneInt (-1)) := by decide
example : π * π = ofInt (-1) 3 * tau (-1) := eisensteinThreeGenerator_mul_self
example : tau (-1) * (1 - tau (-1)) = 1 := eisenstein_tau_mul_inverse
example : (1 - tau (-1)) * tau (-1) = 1 := by
  rw [mul_comm, eisenstein_tau_mul_inverse]

-- Independent finite coordinate checks of the square and inverse.
example : π * π = (⟨0, 3⟩ : TraceOneInt (-1)) ∧
    tau (-1) * (⟨1, -1⟩ : TraceOneInt (-1)) = 1 := by decide

example : ofInt (-1) 3 ∣ π * π := scalar_three_dvd_eisensteinThreeGenerator_square
example : π * π ∣ ofInt (-1) 3 := eisensteinThreeGenerator_square_dvd_scalar_three
example : ofInt (-1) 3 = (π * π) * (1 - tau (-1)) := by
  rw [eisensteinThreeGenerator_mul_self, mul_assoc, eisenstein_tau_mul_inverse, mul_one]

example : π ∈ P := eisensteinThreeGenerator_mem_ramifiedIdeal
example : π ∉ I3 := by
  rw [mem_eisensteinScalarIdeal_iff, eisensteinThreeGenerator_eq]
  decide

example : π * π ∈ I3 := eisensteinThreeGenerator_square_mem_scalarIdeal
example : P = Ideal.span ({π} : Set (TraceOneInt (-1))) := eisensteinThreeRamifiedIdeal_eq_span
example : P * P = I3 := eisensteinThreeRamifiedIdeal_mul_self

private theorem ramifiedInf_ne_scalar : P ⊓ P ≠ I3 := by
  intro heq
  have hm : π ∈ P ⊓ P := ⟨eisensteinThreeGenerator_mem_ramifiedIdeal,
    eisensteinThreeGenerator_mem_ramifiedIdeal⟩
  have hn : π ∉ I3 := by
    rw [mem_eisensteinScalarIdeal_iff, eisensteinThreeGenerator_eq]
    decide
  exact hn (heq ▸ hm)

-- Product and intersection are different: the ramified kernel is not comaximal with itself.
example : P * P = I3 ∧ P ⊓ P ≠ I3 :=
  ⟨eisensteinThreeRamifiedIdeal_mul_self, ramifiedInf_ne_scalar⟩

example : P ⊓ P = P := inf_idem _
example : P ⊔ P ≠ ⊤ := by
  rw [sup_idem]
  exact (eisensteinResidueIdeal_isMaximal (by decide : Nat.Prime 3)
    (2 : ZMod 3) eisensteinThreeRoot).ne_top

-- Actual signed witnesses consume the new generic lattice receiver.
example : (⟨-2, 1⟩ : TraceOneInt (-1)) ∈ P := by
  rw [mem_eisensteinThreeRamifiedIdeal_iff_coordinates]
  norm_num

example : π ∣ (⟨-2, 1⟩ : TraceOneInt (-1)) := by
  apply (mem_eisensteinThreeRamifiedIdeal_iff_dvd _).mp
  rw [mem_eisensteinThreeRamifiedIdeal_iff_coordinates]
  norm_num

example : (⟨-2, 1⟩ : TraceOneInt (-1)) = π * (⟨-1, 1⟩ : TraceOneInt (-1)) := by decide

example : (⟨-43, 86⟩ : TraceOneInt (-1)) ∈ P ∧
    π ∣ (⟨-43, 86⟩ : TraceOneInt (-1)) := by
  rw [mem_eisensteinThreeRamifiedIdeal_iff_coordinates, eisensteinThreeGenerator_dvd_iff_coordinates]
  norm_num

example : (⟨1, 0⟩ : TraceOneInt (-1)) ∉ P := by
  rw [mem_eisensteinThreeRamifiedIdeal_iff_coordinates]
  decide

example (z : TraceOneInt (-1)) : z ∈ P ↔ π ∣ z :=
  mem_eisensteinThreeRamifiedIdeal_iff_dvd z

#print axioms DkMath.Lib.NumberTheory.eisensteinThreeRoot
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_eq
#print axioms DkMath.Lib.NumberTheory.norm_eisensteinThreeGenerator
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_mul_self
#print axioms DkMath.Lib.NumberTheory.eisenstein_tau_mul_inverse
#print axioms DkMath.Lib.NumberTheory.scalar_three_dvd_eisensteinThreeGenerator_square
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_square_dvd_scalar_three
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeRamifiedIdeal
#print axioms DkMath.Lib.NumberTheory.mem_eisensteinThreeRamifiedIdeal_iff_coordinates
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_dvd_iff_coordinates
#print axioms DkMath.Lib.NumberTheory.mem_eisensteinThreeRamifiedIdeal_iff_dvd
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeRamifiedIdeal_eq_span
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_mem_ramifiedIdeal
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_square_mem_scalarIdeal
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeGenerator_square_span_eq_scalarIdeal
#print axioms DkMath.Lib.NumberTheory.eisensteinThreeRamifiedIdeal_mul_self

end DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal
