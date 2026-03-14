/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Scale

namespace DkMath.KUS.Examples

/-- toy unit。phase-04 では自然数 unit を使う。 -/
abbrev ToyUnit := Nat

/-- toy blueprint family。各 unit `u` に対して `Fin (u+1)` を割り当てる。 -/
abbrev ToyBlueprint (u : ToyUnit) : Type := Fin (u + 1)

/-- 固定 support の例。 -/
def toySupport : DkMath.KUS.US ToyUnit ToyBlueprint where
  unit := 2
  blueprint := ⟨1, by decide⟩

/-- KUS 値の例（係数 5）。 -/
def toyX : DkMath.KUS.KUS ToyUnit ToyBlueprint :=
  DkMath.KUS.ofNat toySupport 5

@[simp] theorem toyX_toNat : DkMath.KUS.toNat toyX = 5 := by
  rfl

@[simp] theorem toyX_extract : DkMath.KUS.extract toyX = toySupport := by
  rfl

/-- fixed fiber の加法例。 -/
def toyFiberSum : DkMath.KUS.Fiber toySupport := 2 + 3

@[simp] theorem toyFiberSum_eval : toyFiberSum = 5 := by
  rfl

@[simp] theorem toyFiberSum_toKUS_toNat :
    DkMath.KUS.toNat (DkMath.KUS.Fiber.toKUS toySupport toyFiberSum) = 5 := by
  rfl

/-- unit を 1 だけ拡張する toy scale。 -/
def toyScale : DkMath.KUS.ScaleSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  mapUnit := fun u => u + 1
  mapBlueprint := by
    intro u b
    exact ⟨b.val, Nat.lt_trans b.isLt (Nat.lt_succ_self (u + 1))⟩

@[simp] theorem toyScale_toNat_preserved :
    DkMath.KUS.toNat (DkMath.KUS.ScaleSpec.scaleKUS toyScale toyX) = 5 := by
  rfl

@[simp] theorem toyScale_extract_comm :
    DkMath.KUS.extract (DkMath.KUS.ScaleSpec.scaleKUS toyScale toyX)
        = DkMath.KUS.ScaleSpec.scaleUS toyScale (DkMath.KUS.extract toyX) := by
  rfl

@[simp] theorem toyScale_toKUS_comm (n : DkMath.KUS.Fiber toySupport) :
    DkMath.KUS.ScaleSpec.scaleKUS toyScale (DkMath.KUS.Fiber.toKUS toySupport n)
      = DkMath.KUS.Fiber.toKUS (DkMath.KUS.ScaleSpec.scaleUS toyScale toySupport) n := by
  exact DkMath.KUS.ScaleSpec.scaleKUS_toKUS (σ := toyScale) toySupport n

@[simp] theorem toyScale_extract_toKUS_comm (n : DkMath.KUS.Fiber toySupport) :
    DkMath.KUS.extract
        (DkMath.KUS.ScaleSpec.scaleKUS toyScale (DkMath.KUS.Fiber.toKUS toySupport n))
      = DkMath.KUS.ScaleSpec.scaleUS toyScale toySupport := by
  exact DkMath.KUS.ScaleSpec.extract_scaleKUS_toKUS (σ := toyScale) toySupport n

@[simp] theorem toyScale_toNat_add_comm
    (n m : DkMath.KUS.Fiber toySupport) :
    DkMath.KUS.toNat
        (DkMath.KUS.ScaleSpec.scaleKUS toyScale (DkMath.KUS.Fiber.toKUS toySupport (n + m)))
      = DkMath.KUS.toNat
          (DkMath.KUS.ScaleSpec.scaleKUS toyScale (DkMath.KUS.Fiber.toKUS toySupport n))
        + DkMath.KUS.toNat
            (DkMath.KUS.ScaleSpec.scaleKUS toyScale (DkMath.KUS.Fiber.toKUS toySupport m)) := by
  exact DkMath.KUS.ScaleSpec.toNat_scaleKUS_toKUS_add (σ := toyScale) toySupport n m

end DkMath.KUS.Examples
