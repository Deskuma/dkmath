/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Gnomon.Algebra
import DkMath.Lib.Cosmic.GTail

#print "file: DkMath.Gnomon.CosmicBridge"

/-!
# Degree-two Cosmic bridge for neutral gnomon arithmetic

The production orientation of `GTail` is
`GTail 2 1 x u = x + 2 * u`.  The square-growth gnomon uses the reversed
coordinates, so its normalized shell is
`GTail 2 1 u x = 2 * x + u`.

This module contains only the exact natural-number degree-two bridge.  It does
not import or make claims about Collatz, Legendre, prime existence, or any
analytic projection.
-/

namespace DkMath.Gnomon

open scoped BigOperators

/-- The degree-two normalized Cosmic shell in square-growth orientation. -/
theorem GTail_two_one_eq_square_shell
    (u x : ℕ) :
    DkMath.CosmicFormula.GTail 2 1 u x = 2 * x + u := by
  norm_num [DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

/-- The unit Cosmic shell is the neutral odd gnomon. -/
theorem oddGnomon_eq_GTail_two_one_unit
    (x : ℕ) :
    oddGnomon x = DkMath.CosmicFormula.GTail 2 1 1 x := by
  rw [GTail_two_one_eq_square_shell]
  simp [oddGnomon]

/-- A square-growth band is thickness times its normalized Cosmic shell. -/
theorem squareGnomonBand_eq_mul_GTail_two_one
    (x u : ℕ) :
    squareGnomonBand x u =
      u * DkMath.CosmicFormula.GTail 2 1 u x := by
  rw [GTail_two_one_eq_square_shell]
  rfl

/-- Square growth reconstructed through the existing Cosmic Formula identity. -/
theorem square_add_mul_GTail_two_one
    (x u : ℕ) :
    x ^ 2 + u * DkMath.CosmicFormula.GTail 2 1 u x =
      (x + u) ^ 2 := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap
      (R := ℕ) 2 u x).symm

/-- The neutral square-growth law in the Cosmic shell vocabulary. -/
theorem square_add_squareGnomonBand_eq_mul_GTail_two_one
    (x u : ℕ) :
    x ^ 2 + squareGnomonBand x u =
      x ^ 2 + u * DkMath.CosmicFormula.GTail 2 1 u x := by
  rw [squareGnomonBand_eq_mul_GTail_two_one]

/-- Composition of square bands transported to Cosmic coordinates. -/
theorem mul_GTail_two_one_add_thickness
    (x u v : ℕ) :
    (u + v) * DkMath.CosmicFormula.GTail 2 1 (u + v) x =
      u * DkMath.CosmicFormula.GTail 2 1 u x +
      v * DkMath.CosmicFormula.GTail 2 1 v (x + u) := by
  calc
    (u + v) * DkMath.CosmicFormula.GTail 2 1 (u + v) x =
        squareGnomonBand x (u + v) :=
      (squareGnomonBand_eq_mul_GTail_two_one x (u + v)).symm
    _ = squareGnomonBand x u + squareGnomonBand (x + u) v :=
      squareGnomonBand_add x u v
    _ = u * DkMath.CosmicFormula.GTail 2 1 u x +
          v * DkMath.CosmicFormula.GTail 2 1 v (x + u) := by
      rw [squareGnomonBand_eq_mul_GTail_two_one,
        squareGnomonBand_eq_mul_GTail_two_one]

/-- A thick Cosmic shell is the finite sum of its unit Cosmic shells. -/
theorem mul_GTail_two_one_eq_sum_unit_GTail
    (x u : ℕ) :
    u * DkMath.CosmicFormula.GTail 2 1 u x =
      (Finset.range u).sum
        (fun i => DkMath.CosmicFormula.GTail 2 1 1 (x + i)) := by
  calc
    u * DkMath.CosmicFormula.GTail 2 1 u x = squareGnomonBand x u :=
      (squareGnomonBand_eq_mul_GTail_two_one x u).symm
    _ = (Finset.range u).sum (fun i => oddGnomon (x + i)) :=
      squareGnomonBand_eq_sum_shifted_oddGnomon x u
    _ = (Finset.range u).sum
          (fun i => DkMath.CosmicFormula.GTail 2 1 1 (x + i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact oddGnomon_eq_GTail_two_one_unit (x + i)

example : DkMath.CosmicFormula.GTail 2 1 1 30 = 61 := by
  norm_num [DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

example : DkMath.CosmicFormula.GTail 2 1 1 31 = 63 := by
  norm_num [DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

example : 2 * DkMath.CosmicFormula.GTail 2 1 2 30 = 124 := by
  norm_num [DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

example :
    2 * DkMath.CosmicFormula.GTail 2 1 2 30 =
      DkMath.CosmicFormula.GTail 2 1 1 30 +
        DkMath.CosmicFormula.GTail 2 1 1 31 := by
  norm_num [DkMath.CosmicFormula.GTail, Finset.sum_range_succ]

end DkMath.Gnomon
