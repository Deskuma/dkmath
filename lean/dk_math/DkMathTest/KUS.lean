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

-- Rat: 除算テスト  (1/2) / (1/3) = 3/2
example : toCoeff (gDiv grA grB hR) = ((1 : Rat) / 2) / ((1 : Rat) / 3) := by
  simp [gDiv, gOp, grA, grB]

-- support 保持（ゼロ除算でも）
example : extract_g (gDiv grA grB hR) = suppR := by
  simp [gOp]

-- ゼロ除算: (1/2) / 0 の support 保持（Rat では x / 0 = 0 が定義済み）
example : extract_g (gDiv grA (mkGWith (0 : Rat) suppR) hR) = suppR := by
  simp [gOp]

-- KUS ↔ GKUS Nat 往復変換
example (x : KUS DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint) :
    gKUSToKUS (kusToGKUS x) = x := by
  simp

end DkMathTest.GKUS

namespace DkMathTest.GKUSAlgebra

open DkMath.KUS

-- 3 値テスト用の Rat 係数値
abbrev suppR := DkMath.KUS.Examples.toySupport
abbrev grA : GKUS Rat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith ((1 : Rat) / 2) suppR
abbrev grB : GKUS Rat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith ((1 : Rat) / 3) suppR
abbrev grC : GKUS Rat DkMath.KUS.Examples.ToyUnit DkMath.KUS.Examples.ToyBlueprint :=
  mkGWith ((1 : Rat) / 4) suppR

lemma hAB : GSameSupport grA grB := by simp [GSameSupport]
lemma hBC : GSameSupport grB grC := by simp [GSameSupport]
lemma hAC : GSameSupport grA grC := hAB.trans hBC

-- 加法交換則
example : gAdd grA grB hAB = gAdd grB grA hAB.symm := gAdd_comm hAB

-- 乗法交換則
example : gMul grA grB hAB = gMul grB grA hAB.symm := gMul_comm hAB

-- 加法結合則
example : gAdd (gAdd grA grB hAB) grC
          (by simp [GSameSupport, gOp])
          = gAdd grA (gAdd grB grC hBC)
          (by simp [GSameSupport, gOp]) :=
  gAdd_assoc hAB hBC (by simp [GSameSupport, gOp]) (by simp [GSameSupport, gOp])

-- 乗法結合則
example : gMul (gMul grA grB hAB) grC
          (by simp [GSameSupport, gOp])
          = gMul grA (gMul grB grC hBC)
          (by simp [GSameSupport, gOp]) :=
  gMul_assoc hAB hBC (by simp [GSameSupport, gOp]) (by simp [GSameSupport, gOp])

-- 左分配則: grA * (grB + grC) = grA * grB + grA * grC
example : gMul grA (gAdd grB grC hBC)
          (by simp [GSameSupport, gOp])
          = gAdd (gMul grA grB hAB) (gMul grA grC hAC)
          (by simp [GSameSupport, gOp]) :=
  gMul_gAdd hAB hBC
    (by simp [GSameSupport, gOp]) hAC (by simp [GSameSupport, gOp])

-- 右分配則: (grA + grB) * grC = grA * grC + grB * grC
example : gMul (gAdd grA grB hAB) grC
          (by simp [GSameSupport, gOp])
          = gAdd (gMul grA grC hAC) (gMul grB grC hBC)
          (by simp [GSameSupport, gOp]) :=
  gAdd_gMul hAB hBC
    (by simp [GSameSupport, gOp]) hAC (by simp [GSameSupport, gOp])

-- gDiv_one: grA / 1 = grA
example : gDiv grA (gOneState suppR) (by simp [GSameSupport]) = grA :=
  gDiv_one suppR (by simp [GSameSupport])

-- gDiv_add_distrib: (grA + grB) / grC = grA/grC + grB/grC
example : gDiv (gAdd grA grB hAB) grC
          (by simp [GSameSupport, gOp])
          = gAdd (gDiv grA grC hAC) (gDiv grB grC hBC)
          (by simp [GSameSupport, gOp]) :=
  gDiv_add_distrib hAB hAC hBC
    (by simp [GSameSupport, gOp]) (by simp [GSameSupport, gOp])

-- gMul_gDiv_assoc: grA * (grB / grC) = (grA * grB) / grC
example : gMul grA (gDiv grB grC hBC)
          (by simp [GSameSupport, gOp])
          = gDiv (gMul grA grB hAB) grC
          (by simp [GSameSupport, gOp]) :=
  gMul_gDiv_assoc hAB hBC
    (by simp [GSameSupport, gOp]) (by simp [GSameSupport, gOp])

end DkMathTest.GKUSAlgebra

namespace DkMathTest.GKUSTransport

open DkMath.KUS

abbrev ToyUnit := DkMath.KUS.Examples.ToyUnit
abbrev ToyBlueprint := DkMath.KUS.Examples.ToyBlueprint

def supportL : US ToyUnit ToyBlueprint where
  unit := 3
  blueprint := ⟨0, by decide⟩

def supportR : US ToyUnit ToyBlueprint where
  unit := 5
  blueprint := ⟨0, by decide⟩

abbrev gx : GKUS Rat ToyUnit ToyBlueprint :=
  mkGWith ((1 : Rat) / 2) supportL

abbrev gy : GKUS Rat ToyUnit ToyBlueprint :=
  mkGWith ((1 : Rat) / 3) supportR

def hs : HarmonizeSpec Rat ToyUnit ToyBlueprint ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  encLeft := {
    mapUnit := fun _ => 2
    mapBlueprint := fun {_} _ => ⟨0, by decide⟩
  }
  encRight := {
    mapUnit := fun _ => 2
    mapBlueprint := fun {_} _ => ⟨0, by decide⟩
  }
  sameSupport := by
    intro x y
    simp [GSameSupport]

def ds : DecodeSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  dec := {
    mapUnit := fun _ => 1
    mapBlueprint := fun {_} _ => ⟨0, by decide⟩
  }

def ds2 : DecodeSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  dec := {
    mapUnit := fun _ => 7
    mapBlueprint := fun {_} _ => ⟨0, by decide⟩
  }

def tau : ScaleSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  mapUnit := fun _ => 9
  mapBlueprint := fun {_} _ => ⟨0, by decide⟩

def decLeft : ScaleSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  mapUnit := fun _ => 11
  mapBlueprint := fun {_} _ => ⟨0, by decide⟩

def decRight : ScaleSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  mapUnit := fun _ => 13
  mapBlueprint := fun {_} _ => ⟨0, by decide⟩

def decNorm : ScaleSpec ToyUnit ToyBlueprint ToyUnit ToyBlueprint where
  mapUnit := fun _ => 17
  mapBlueprint := fun {_} _ => ⟨0, by decide⟩

def supportH : US ToyUnit ToyBlueprint where
  unit := 2
  blueprint := ⟨0, by decide⟩

def supportT : US ToyUnit ToyBlueprint where
  unit := 1
  blueprint := ⟨0, by decide⟩

def supportT2 : US ToyUnit ToyBlueprint where
  unit := 7
  blueprint := ⟨0, by decide⟩

def supportTau : US ToyUnit ToyBlueprint where
  unit := 9
  blueprint := ⟨0, by decide⟩

def supportLeftAPI : US ToyUnit ToyBlueprint where
  unit := 11
  blueprint := ⟨0, by decide⟩

def supportRightAPI : US ToyUnit ToyBlueprint where
  unit := 13
  blueprint := ⟨0, by decide⟩

def supportNormAPI : US ToyUnit ToyBlueprint where
  unit := 17
  blueprint := ⟨0, by decide⟩

example : toCoeff (HarmonizeSpec.harmonizeAdd hs gx gy) = ((1 : Rat) / 2 + (1 : Rat) / 3) := by
  simpa [gx, gy] using (HarmonizeSpec.toCoeff_harmonizeAdd (hs := hs) (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeAdd hs gx gy) = supportH := by
  simpa [HarmonizeSpec.encodeLeft, hs, gx, supportH] using
    (HarmonizeSpec.extract_g_harmonizeAdd (hs := hs) (x := gx) (y := gy))

example :
    toCoeff (HarmonizeSpec.harmonizeAddTo hs ds gx gy)
      = ((1 : Rat) / 2 + (1 : Rat) / 3) := by
  simpa [gx, gy] using
    (HarmonizeSpec.toCoeff_harmonizeAddTo (hs := hs) (ds := ds) (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeAddTo hs ds gx gy) = supportT := by
  simp [HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft, hs, ds, supportT]

example : toCoeff (HarmonizeSpec.harmonizeMul hs gx gy) = ((1 : Rat) / 2) * ((1 : Rat) / 3) := by
  simpa [gx, gy] using (HarmonizeSpec.toCoeff_harmonizeMul (hs := hs) (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeMul hs gx gy) = supportH := by
  simpa [HarmonizeSpec.encodeLeft, hs, gx, supportH] using
    (HarmonizeSpec.extract_g_harmonizeMul (hs := hs) (x := gx) (y := gy))

example :
    toCoeff (HarmonizeSpec.harmonizeMulTo hs ds2 gx gy)
      = ((1 : Rat) / 2) * ((1 : Rat) / 3) := by
  simpa [gx, gy] using
    (HarmonizeSpec.toCoeff_harmonizeMulTo (hs := hs) (ds := ds2) (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeMulTo hs ds2 gx gy) = supportT2 := by
  simp [HarmonizeSpec.harmonizeMul, HarmonizeSpec.encodeLeft, hs, ds2, supportT2]

example :
    ScaleSpec.scaleGKUS tau (HarmonizeSpec.harmonizeAddTo hs ds gx gy)
      = HarmonizeSpec.harmonizeAddTo hs ⟨ScaleSpec.comp tau ds.dec⟩ gx gy := by
  simp

example :
    ScaleSpec.scaleGKUS tau (HarmonizeSpec.harmonizeMulTo hs ds2 gx gy)
      = HarmonizeSpec.harmonizeMulTo hs ⟨ScaleSpec.comp tau ds2.dec⟩ gx gy := by
  simp

example :
    extract_g (ScaleSpec.scaleGKUS tau (HarmonizeSpec.harmonizeAddTo hs ds gx gy))
      = supportTau := by
  simp [HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft, hs, ds, tau, supportTau]

example :
    toCoeff (HarmonizeSpec.harmonizeAddLeft hs decLeft gx gy)
      = ((1 : Rat) / 2 + (1 : Rat) / 3) := by
  unfold HarmonizeSpec.harmonizeAddLeft
  simpa [DecodeSpec.ofScale, gx, gy] using
    (HarmonizeSpec.toCoeff_harmonizeAddTo (hs := hs) (ds := DecodeSpec.ofScale decLeft)
      (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeAddLeft hs decLeft gx gy) = supportLeftAPI := by
  simp [HarmonizeSpec.harmonizeAddLeft, HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft,
    hs, decLeft, supportLeftAPI]

example :
    toCoeff (HarmonizeSpec.harmonizeAddRight hs decRight gx gy)
      = ((1 : Rat) / 2 + (1 : Rat) / 3) := by
  unfold HarmonizeSpec.harmonizeAddRight
  simpa [DecodeSpec.ofScale, gx, gy] using
    (HarmonizeSpec.toCoeff_harmonizeAddTo (hs := hs) (ds := DecodeSpec.ofScale decRight)
      (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeAddRight hs decRight gx gy) = supportRightAPI := by
  simp [HarmonizeSpec.harmonizeAddRight, HarmonizeSpec.harmonizeAdd, HarmonizeSpec.encodeLeft,
    hs, decRight, supportRightAPI]

example :
    toCoeff (HarmonizeSpec.harmonizeMulNormalized hs decNorm gx gy)
      = ((1 : Rat) / 2) * ((1 : Rat) / 3) := by
  unfold HarmonizeSpec.harmonizeMulNormalized
  simpa [DecodeSpec.ofScale, gx, gy] using
    (HarmonizeSpec.toCoeff_harmonizeMulTo (hs := hs) (ds := DecodeSpec.ofScale decNorm)
      (x := gx) (y := gy))

example : extract_g (HarmonizeSpec.harmonizeMulNormalized hs decNorm gx gy) = supportNormAPI := by
  simp [HarmonizeSpec.harmonizeMulNormalized, HarmonizeSpec.harmonizeMul, HarmonizeSpec.encodeLeft,
    hs, decNorm, supportNormAPI]

end DkMathTest.GKUSTransport
