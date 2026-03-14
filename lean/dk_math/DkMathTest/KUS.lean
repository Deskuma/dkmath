/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS

/-! ## GKUS（一般係数）回帰テスト -/

#print "file: DkMathTest.KUS"

namespace DkMathTest.KUS

open DkMath.KUS

abbrev support := DkMath.KUS.Examples.toySupport
abbrev a : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  ofNat support 3
abbrev b : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  ofNat support 4

example : toNat DkMath.KUS.Examples.toyX = 5 := by
  exact DkMath.KUS.Examples.toyX_toNat

example : toNat DkMath.KUS.Examples.toyMul = 10 := by
  exact DkMath.KUS.Examples.toyMul_toNat

example : extract DkMath.KUS.Examples.toyMul = support := by
  exact DkMath.KUS.Examples.toyMul_extract

example :
    toNat (kusAdd a b (by simp [SameSupport])) = 7 := by
  simp [kusAdd]

example :
    extract (kusAdd a b (by simp [SameSupport])) = support := by
  simp [kusAdd]

example :
    toNat (kusMul a b (by simp [SameSupport])) = 12 := by
  simp [kusMul]

example :
    extract (kusMul a b (by simp [SameSupport])) = support := by
  simp [kusMul]

example :
    kusMul DkMath.KUS.Examples.toyX (oneState support)
      (by simp [SameSupport, oneState, DkMath.KUS.Examples.toyX])
      = DkMath.KUS.Examples.toyX := by
  simpa [DkMath.KUS.Examples.toyX] using (kusMul.mul_one (x := DkMath.KUS.Examples.toyX))

example :
    extract (kusMul DkMath.KUS.Examples.toyX (zeroState support)
      (by simp [SameSupport, DkMath.KUS.Examples.toyX])) = support := by
  simp [kusMul, DkMath.KUS.Examples.toyX]

end DkMathTest.KUS

namespace DkMathTest.GKUS

open DkMath.KUS

-- Nat 係数（既存 KUS との互換）
abbrev suppN := DkMath.KUS.Examples.toySupport
abbrev gnA : GKUS Nat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith 3 suppN
abbrev gnB : GKUS Nat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith 4 suppN

-- Int 係数（減法が可能）
abbrev suppI := DkMath.KUS.Examples.toySupport
abbrev giA : GKUS Int DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith (5 : Int) suppI
abbrev giB : GKUS Int DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith (8 : Int) suppI

-- Rat 係数（有理係数）
abbrev suppR := DkMath.KUS.Examples.toySupport
abbrev grA : GKUS Rat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith ((1 : Rat) / 2) suppR
abbrev grB : GKUS Rat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith ((1 : Rat) / 3) suppR

lemma hN : GSameSupport gnA gnB := by
  simp only [GSameSupport, extract_g, mkGWith.eq_1]

lemma hI : GSameSupport giA giB := by
  simp only [GSameSupport, extract_g, mkGWith.eq_1]

lemma hR : GSameSupport grA grB := by
  simp only [GSameSupport, extract_g, mkGWith.eq_1]

-- toCoeff_gOp で 3 + 4 = 7
example : toCoeff (gOp (· + ·) gnA gnB hN) = 7 := by
  simp [gOp, gnA, gnB]

-- extract_g_gOp で support 保持
example : extract_g (gOp (· + ·) gnA gnB hN) = suppN := by
  simp only [mkGWith.eq_1, gOp, extract_g.eq_1]

-- gAdd API
example : toCoeff (gAdd gnA gnB hN) = 7 := by
  simp [gAdd, gOp, gnA, gnB]

-- gMul API：3 * 4 = 12
example : toCoeff (gMul gnA gnB hN) = 12 := by
  simp [gMul, gOp, gnA, gnB]

-- gSub：8 - 5 = 3（Int）
example : toCoeff (gSub giB giA hI.symm) = (3 : Int) := by
  simp [gSub, gOp, giA, giB]

-- gSub：5 - 8 = -3（Int、マイナス係数でも support 保持）
example : toCoeff (gSub giA giB hI) = (-3 : Int) := by
  simp [gSub, gOp, giA, giB]

example : extract_g (gSub giA giB hI) = suppI := by
  simp [gOp]

-- Rat: 加算・乗算・減算の係数追跡
example : toCoeff (gAdd grA grB hR) = ((1 : Rat) / 2 + (1 : Rat) / 3) := by
  simp [gAdd, gOp, grA, grB]

example : toCoeff (gMul grA grB hR) = (((1 : Rat) / 2) * ((1 : Rat) / 3)) := by
  simp [gMul, gOp, grA, grB]

example : toCoeff (gSub grA grB hR) = ((1 : Rat) / 2 - (1 : Rat) / 3) := by
  simp [gSub, gOp, grA, grB]

example : extract_g (gAdd grA grB hR) = suppR := by
  simp [gOp]

example : extract_g (gMul grA grB hR) = suppR := by
  simp [gOp]

example : extract_g (gSub grA grB hR) = suppR := by
  simp [gOp]

-- KUS ↔ GKUS Nat 往復変換
example (x : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint) :
    gKUSToKUS (kusToGKUS x) = x := by
  simp

end DkMathTest.GKUS
