/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino
import DkMath.BookOfMagic.GapCrystal

#print "file: DkMath.Tromino.Restoration"

namespace DkMath.Tromino

open DkMath.Polyomino
open DkMath.Polyomino.Tromino

/-!
# Certified geometric restoration

The retained core and the missing gap are typed by the fixed target shape.
The existing `BookOfMagic.GapFiber` and `GapCrystal` structures provide the
certificate containers; this module only supplies the Tromino-owned relation.
-/

/-- Restore a target shape by adjoining a retained core and its gap. -/
def restoreShape (core gap : Shape) : Shape := core ∪ gap

/-- A disjoint core and gap restore the fixed target shape. -/
def shapeRestoreRel (target core gap : Shape) : Prop :=
  Disjoint core gap ∧ restoreShape core gap = target

/-- Thin `GapFiber` adapter for geometric restoration over a fixed target. -/
abbrev shapeGapFiber (target core : Shape) : Type :=
  DkMath.BookOfMagic.GapFiber (shapeRestoreRel target) core

/-- Thin `GapCrystal` adapter for geometric restoration over a fixed target. -/
abbrev shapeGapCrystal (target : Shape) : Type :=
  DkMath.BookOfMagic.GapCrystal
    Shape
    (fun _ : Shape => Shape)
    (shapeRestoreRel target)

/-- The atomic L-tromino and hole restore the 2×2 block. -/
theorem atomic_shapeRestoreRel :
    shapeRestoreRel block2 L_tromino hole2 := by
  refine ⟨disjoint_L_hole, ?_⟩
  exact block2_eq_L_union_hole.symm

/-- The atomic restored shape is the existing 2×2 block. -/
theorem atomic_restoreShape :
    restoreShape L_tromino hole2 = block2 := by
  exact block2_eq_L_union_hole.symm

/-- The certified atomic gap fiber contains the existing `hole2`. -/
def atomicGapFiber : shapeGapFiber block2 L_tromino :=
  ⟨hole2, atomic_shapeRestoreRel⟩

/-- The certified atomic gap crystal retains `L_tromino` and `hole2`. -/
def atomicGapCrystal : shapeGapCrystal block2 where
  core := L_tromino
  gap := hole2
  certificate := atomic_shapeRestoreRel

/-- A fixed target and core admit at most one disjoint restoring gap. -/
theorem shapeRestoreRel_gap_unique
    {target core gap₁ gap₂ : Shape}
    (h₁ : shapeRestoreRel target core gap₁)
    (h₂ : shapeRestoreRel target core gap₂) :
    gap₁ = gap₂ := by
  rcases h₁ with ⟨hdis₁, hunion₁⟩
  rcases h₂ with ⟨hdis₂, hunion₂⟩
  ext x
  constructor
  · intro hx₁
    have hxt : x ∈ target := by
      rw [← hunion₁]
      exact Finset.mem_union_right core hx₁
    rw [← hunion₂] at hxt
    rcases Finset.mem_union.mp hxt with hxc | hx₂
    · exact False.elim (Finset.disjoint_left.mp hdis₁ hxc hx₁)
    · exact hx₂
  · intro hx₂
    have hxt : x ∈ target := by
      rw [← hunion₂]
      exact Finset.mem_union_right core hx₂
    rw [← hunion₁] at hxt
    rcases Finset.mem_union.mp hxt with hxc | hx₁
    · exact False.elim (Finset.disjoint_left.mp hdis₂ hxc hx₂)
    · exact hx₁

/-- A certified geometric gap satisfies the existing `UniqueGap` contract. -/
theorem uniqueGap_of_shapeRestoreRel
    {target core gap : Shape}
    (h : shapeRestoreRel target core gap) :
    DkMath.BookOfMagic.UniqueGap (shapeRestoreRel target) core := by
  refine ⟨gap, h, ?_⟩
  intro other hother
  exact shapeRestoreRel_gap_unique hother h

/-- The atomic Tromino hole is the unique restoring gap over `L_tromino`. -/
theorem atomic_uniqueGap :
    DkMath.BookOfMagic.UniqueGap (shapeRestoreRel block2) L_tromino := by
  exact uniqueGap_of_shapeRestoreRel atomic_shapeRestoreRel

end DkMath.Tromino
