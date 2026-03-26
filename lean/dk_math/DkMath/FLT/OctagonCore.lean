/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

#print "file: DkMath.FLT.OctagonCore"

/-!
# Octagon Core

「八角定理作図法」の座標核を固定するための最小モジュール。

この段階では、標準配置の点定義と、`sqrt 2` に関する基本恒等式を
no-so#rry で置く。
-/

namespace DkMath.FLT

abbrev Point2 := ℝ × ℝ

noncomputable section

inductive PhaseLabel where
  | sqrt2
  | sqrt3
  | mixed
  | unknown
  deriving DecidableEq, Repr

def A : Point2 := (0, 0)
def B : Point2 := (1, 0)
def C : Point2 := (1, 1)
def D : Point2 := (0, 1)

def E : Point2 := (1 / Real.sqrt 2, 1 / Real.sqrt 2)
def F : Point2 := (0, Real.sqrt 2)
def G : Point2 := (-1 / Real.sqrt 2, 1 / Real.sqrt 2)

def O : Point2 := ((Real.sqrt 2 - 1) / 2, 1 / 2)
def I : Point2 := (Real.sqrt 2 - 1, 1)

/--
八角核の固定点に対する最小ラベリング。
-/
def phaseLabelOfPoint (p : Point2) : PhaseLabel :=
  if p = I then PhaseLabel.mixed
  else if p = E ∨ p = F ∨ p = G then PhaseLabel.sqrt2
  else PhaseLabel.unknown

/--
判定器入口: 「混合位相点」述語。
-/
def isMixedPhasePoint (p : Point2) : Prop :=
  phaseLabelOfPoint p = PhaseLabel.mixed

lemma one_add_sqrt_two_mul_sqrt_two_sub_one :
    (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  calc
    (1 + Real.sqrt 2) * (Real.sqrt 2 - 1)
        = (Real.sqrt 2 * Real.sqrt 2) - 1 := by ring
    _ = 1 := by nlinarith [hsq]

lemma AI_slope_identity :
    (I.2 - A.2) = (1 + Real.sqrt 2) * (I.1 - A.1) := by
  simp [A, I, one_add_sqrt_two_mul_sqrt_two_sub_one]

lemma phaseLabel_I : phaseLabelOfPoint I = PhaseLabel.mixed := by
  simp [phaseLabelOfPoint]

lemma mixedPoint_I : isMixedPhasePoint I := by
  simpa [isMixedPhasePoint] using phaseLabel_I

end

end DkMath.FLT
