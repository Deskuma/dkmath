/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.NumberTheory.FixedBigGauge.SquareCertificate

namespace DkMathTest.FixedBigGaugeAudit

open DkMath.NumberTheory.FixedBigGauge
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

/-- Omitting the strict lower bound incorrectly rejects an old prime. -/
theorem lower_bound_is_necessary :
    Nat.Prime 2 ∧ 2 ≤ squareBody 2 ∧
      ¬ Nat.Coprime 2 (primeWorldModulus (primeScalesUpTo 2)) := by
  decide +kernel

/-- The complete prime world through 30 misses the composite 31 squared. -/
theorem next_square_counterexample :
    squareBody 30 = 960 ∧ ¬ Nat.Prime 961 ∧
      Nat.Coprime 961 (primeWorldModulus (primeScalesUpTo 30)) := by
  decide +kernel

/-- The much smaller world {2,3,5} cannot certify the entire 30-shell. -/
theorem incomplete_world_counterexample :
    30 < 49 ∧ 49 ≤ squareBody 30 ∧ Nat.Coprime 49 30 ∧ ¬ Nat.Prime 49 := by
  decide +kernel

/-- Division by zero cannot yield the nontrivial square normalization. -/
theorem zero_edge_counterexample :
    (0 ^ 2 - fixedBigUnit 0 2 ^ 2) / fixedBigUnit 0 2 ^ 2 ≠
      (squareBody 1 : ℝ) := by
  norm_num [fixedBigUnit, squareBody]

/-- The product and synchronization modulus of composite directions differ. -/
theorem composite_direction_arithmetic :
    6 * 14 * 21 = 1764 ∧ Nat.lcm (Nat.lcm 6 14) 21 = 42 ∧
      squareBody 1764 = 3115224 := by
  decide +kernel

#print axioms scale_unit_conservation
#print axioms fixedBig_decomposition
#print axioms fixedBig_squareBody_normalization
#print axioms fixedBigUnit_transport
#print axioms freshPrime_fixedBigUnit_refinement
#print axioms prime_iff_coprime_in_squareShell
#print axioms prime_iff_coprime_of_physical_squareShell
#print axioms next_square_counterexample
#print axioms incomplete_world_counterexample

end DkMathTest.FixedBigGaugeAudit
