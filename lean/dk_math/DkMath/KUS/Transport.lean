/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Scale

#print "file: DkMath.KUS.Transport"

namespace DkMath.KUS

universe u₁ v₁ u₂ v₂ uH vH uT vT

/--
`HarmonizeSpec` は異なる support 系を共通調和 support `H` へ持ち上げる仕様。
- `encLeft` : 左系 → H
- `encRight`: 右系 → H
- `sameSupport` : encode 後に `GSameSupport` が成立すること
-/
structure HarmonizeSpec
    (C : Type*)
    (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
    (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
    (H : Type uH) (BH : BlueprintFamily H) where
  encLeft : ScaleSpec U₁ B₁ H BH
  encRight : ScaleSpec U₂ B₂ H BH
  sameSupport :
    ∀ (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂),
      GSameSupport (ScaleSpec.scaleGKUS encLeft x) (ScaleSpec.scaleGKUS encRight y)

/-- 共通調和 support から目的 support `T` へのデコード仕様。 -/
structure DecodeSpec
    (H : Type uH) (BH : BlueprintFamily H)
    (T : Type uT) (BT : BlueprintFamily T) where
  dec : ScaleSpec H BH T BT

namespace HarmonizeSpec

variable {C : Type*}
variable {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
variable {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
variable {H : Type uH} {BH : BlueprintFamily H}
variable {T : Type uT} {BT : BlueprintFamily T}

/-- 左入力を共通調和 support `H` へ encode。 -/
@[simp] def encodeLeft (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) : GKUS C H BH :=
  ScaleSpec.scaleGKUS hs.encLeft x

/-- 右入力を共通調和 support `H` へ encode。 -/
@[simp] def encodeRight (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (y : GKUS C U₂ B₂) : GKUS C H BH :=
  ScaleSpec.scaleGKUS hs.encRight y

/-- encode 後に共通 support で加算する（結果は H 上）。 -/
@[simp] def harmonizeAdd [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C H BH :=
  gAdd (encodeLeft hs x) (encodeRight hs y) (hs.sameSupport x y)

/-- encode → confluence(add) → decode の 3 相合成。 -/
@[simp] def harmonizeAddTo [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C T BT :=
  ScaleSpec.scaleGKUS ds.dec (harmonizeAdd hs x y)

@[simp] theorem toCoeff_harmonizeAdd [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    toCoeff (harmonizeAdd hs x y) = toCoeff x + toCoeff y := by
  unfold harmonizeAdd encodeLeft encodeRight
  simp [gAdd, gOp, toCoeff]

@[simp] theorem extract_g_harmonizeAdd [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    extract_g (harmonizeAdd hs x y) = extract_g (encodeLeft hs x) := by
  unfold harmonizeAdd encodeLeft encodeRight
  simp [gOp]

@[simp] theorem toCoeff_harmonizeAddTo [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    toCoeff (harmonizeAddTo hs ds x y) = toCoeff x + toCoeff y := by
  unfold harmonizeAddTo
  simpa using toCoeff_harmonizeAdd (hs := hs) (x := x) (y := y)

@[simp] theorem extract_g_harmonizeAddTo [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    extract_g (harmonizeAddTo hs ds x y)
      = ScaleSpec.scaleUS ds.dec (extract_g (harmonizeAdd hs x y)) := by
  simp [harmonizeAddTo]

end HarmonizeSpec

end DkMath.KUS
