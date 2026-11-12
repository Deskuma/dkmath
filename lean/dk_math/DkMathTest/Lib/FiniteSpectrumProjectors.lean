/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMathTest.Lib.FiniteSpectrumProjectors"

/-! # 非零の固有ベクトルによる補間射影の検査
算術的な非零類を仮定せず、F₃₇²上の二つの明示的な固有直線で検査する。
対応する射影は非零ベクトルを保持し、別の射影は消す。
-/
namespace FiniteSpectrumProjectorsTest
open Module DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable def diagonal : End (ZMod 37) (ZMod 37 × ZMod 37) where
  toFun x := (2 * x.1, 3 * x.2)
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' a x := by
    change (2 * (a * x.1), 3 * (a * x.2)) = (a * (2 * x.1), a * (3 * x.2))
    congr 1 <;> ring

def two : (ZMod 37)ˣ := Units.mk0 (2 : ZMod 37) (by decide)
def three : (ZMod 37)ˣ := Units.mk0 (3 : ZMod 37) (by decide)

example : projector Units.val diagonal two (1, 0) = (1, 0) := by
  have h : diagonal (1, 0) = (two : ZMod 37) • (1, 0) := by ext <;> simp [diagonal, two]
  simpa using projector_apply_eigen Units.val diagonal Units.val_injective (i := two) h
example : projector Units.val diagonal three (1, 0) = 0 := by
  have h : diagonal (1, 0) = (two : ZMod 37) • (1, 0) := by ext <;> simp [diagonal, two]
  have hne : three ≠ two := by decide
  simpa only [ite_eq_right hne] using
    projector_apply_eigen Units.val diagonal Units.val_injective (i := three) h
example : projector Units.val diagonal three (0, 1) = (0, 1) := by
  have h : diagonal (0, 1) = (three : ZMod 37) • (0, 1) := by ext <;> simp [diagonal, three]
  simpa using projector_apply_eigen Units.val diagonal Units.val_injective (i := three) h
example (x : ZMod 37 × ZMod 37) : ∑ a : (ZMod 37)ˣ, projector Units.val diagonal a x = x :=
  sum_projector_apply Units.val diagonal Units.val_injective x
end FiniteSpectrumProjectorsTest
