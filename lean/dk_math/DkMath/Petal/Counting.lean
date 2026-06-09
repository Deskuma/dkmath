/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Basic

#print "file: DkMath.Petal.Counting"

/-!
# Petal Counting

This file fixes the first counting vocabulary for relative Petal systems.

The arithmetic is ordinary natural-number arithmetic.  The important point is
the naming: `n + 1` is exposed as a lap base made from a base unit core and one
inheritance slot.
-/

namespace DkMath
namespace Petal

/-- Base unit core: the number of Petal directions. -/
def baseUnitCore (n : Nat) : Nat := n

/-- The single channel that carries the core to the next lap. -/
def inheritanceSlot (_n : Nat) : Nat := 1

/-- Lap base: Petal directions plus the inheritance slot. -/
def lapBase (n : Nat) : Nat :=
  baseUnitCore n + inheritanceSlot n

/-- Total count after `lap` relative-Petal expansions. -/
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap

/-- The one-lap relative polygon kernel. -/
def relPolygonKernel (n : Nat) : Nat :=
  baseUnitCore n * lapBase n

/-- The lap base computes to `n + 1`, but keeps the Petal meaning in the API. -/
theorem lapBase_eq_succ (n : Nat) :
    lapBase n = n + 1 := by
  rfl

/-- Zero laps return the base unit core. -/
theorem relPetalTotal_zero (n : Nat) :
    relPetalTotal n 0 = n := by
  simp [relPetalTotal, baseUnitCore]

/-- One more lap multiplies the current total by the lap base. -/
theorem relPetalTotal_succ (n lap : Nat) :
    relPetalTotal n (lap + 1) = relPetalTotal n lap * lapBase n := by
  simp [relPetalTotal, pow_succ, Nat.mul_assoc]

/-- The one-lap total is the relative polygon kernel. -/
theorem relPetalTotal_one (n : Nat) :
    relPetalTotal n 1 = relPolygonKernel n := by
  simp [relPetalTotal, relPolygonKernel]

/-- The relative polygon kernel is the first Petal-orbit total. -/
theorem relPolygonKernel_eq_relPetalTotal_one (n : Nat) :
    relPolygonKernel n = relPetalTotal n 1 := by
  exact (relPetalTotal_one n).symm

/-- The fixed `n = 5` zero-lap example. -/
theorem relPetalTotal_five_zero :
    relPetalTotal 5 0 = 5 := by
  decide

/-- The fixed `n = 5` one-lap example. -/
theorem relPetalTotal_five_one :
    relPetalTotal 5 1 = 30 := by
  decide

/-- The fixed `n = 5` two-lap example. -/
theorem relPetalTotal_five_two :
    relPetalTotal 5 2 = 180 := by
  decide

/--
Relative unit-core orbit equivalence.

Two values are in the same fixed-core Petal orbit if both are lap totals for the
same base unit core.
-/
def SameRelPetalOrbit (n a b : Nat) : Prop :=
  ∃ i j, a = relPetalTotal n i ∧ b = relPetalTotal n j

/-- The base unit and first one-lap total of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_5_30 :
    SameRelPetalOrbit 5 5 30 := by
  refine ⟨0, 1, ?_, ?_⟩ <;> decide

/-- The first and second lap totals of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_30_180 :
    SameRelPetalOrbit 5 30 180 := by
  refine ⟨1, 2, ?_, ?_⟩ <;> decide

/-- The base unit and second lap total of the pentagonal Petal orbit agree as orbit members. -/
theorem sameRelPetalOrbit_five_5_180 :
    SameRelPetalOrbit 5 5 180 := by
  refine ⟨0, 2, ?_, ?_⟩ <;> decide

end Petal
end DkMath
