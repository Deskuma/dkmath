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

namespace DecodeSpec

variable {H : Type uH} {BH : BlueprintFamily H}
variable {T : Type uT} {BT : BlueprintFamily T}

/-- `ScaleSpec` から `DecodeSpec` を作る最小コンストラクタ。 -/
@[simp] def ofScale (σ : ScaleSpec H BH T BT) : DecodeSpec H BH T BT :=
  ⟨σ⟩

@[simp] theorem dec_ofScale (σ : ScaleSpec H BH T BT) :
    (ofScale (H := H) (BH := BH) (T := T) (BT := BT) σ).dec = σ := rfl

end DecodeSpec

namespace HarmonizeSpec

variable {C : Type*}
variable {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
variable {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
variable {H : Type uH} {BH : BlueprintFamily H}
variable {T : Type uT} {BT : BlueprintFamily T}
variable {T' : Type _} {BT' : BlueprintFamily T'}

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

/-- encode 後に共通 support で乗算する（結果は H 上）。 -/
@[simp] def harmonizeMul [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C H BH :=
  gMul (encodeLeft hs x) (encodeRight hs y) (hs.sameSupport x y)

/-- encode → confluence(mul) → decode の 3 相合成。 -/
@[simp] def harmonizeMulTo [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C T BT :=
  ScaleSpec.scaleGKUS ds.dec (harmonizeMul hs x y)

/-! ## API aliases: canonical decode choices -/

/-- 左系への decode を明示した加算 API。 -/
@[simp] def harmonizeAddLeft [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decLeft : ScaleSpec H BH U₁ B₁)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C U₁ B₁ :=
  harmonizeAddTo hs (DecodeSpec.ofScale decLeft) x y

/-- 右系への decode を明示した加算 API。 -/
@[simp] def harmonizeAddRight [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decRight : ScaleSpec H BH U₂ B₂)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C U₂ B₂ :=
  harmonizeAddTo hs (DecodeSpec.ofScale decRight) x y

/-- 正規形 support への decode を明示した加算 API。 -/
@[simp] def harmonizeAddNormalized [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decNorm : ScaleSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C T BT :=
  harmonizeAddTo hs (DecodeSpec.ofScale decNorm) x y

/-- 左系への decode を明示した乗算 API。 -/
@[simp] def harmonizeMulLeft [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decLeft : ScaleSpec H BH U₁ B₁)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C U₁ B₁ :=
  harmonizeMulTo hs (DecodeSpec.ofScale decLeft) x y

/-- 右系への decode を明示した乗算 API。 -/
@[simp] def harmonizeMulRight [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decRight : ScaleSpec H BH U₂ B₂)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C U₂ B₂ :=
  harmonizeMulTo hs (DecodeSpec.ofScale decRight) x y

/-- 正規形 support への decode を明示した乗算 API。 -/
@[simp] def harmonizeMulNormalized [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (decNorm : ScaleSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) : GKUS C T BT :=
  harmonizeMulTo hs (DecodeSpec.ofScale decNorm) x y

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

@[simp] theorem toCoeff_harmonizeMul [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    toCoeff (harmonizeMul hs x y) = toCoeff x * toCoeff y := by
  unfold harmonizeMul encodeLeft encodeRight
  simp [gMul, gOp, toCoeff]

@[simp] theorem extract_g_harmonizeMul [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    extract_g (harmonizeMul hs x y) = extract_g (encodeLeft hs x) := by
  unfold harmonizeMul encodeLeft encodeRight
  simp [gOp]

@[simp] theorem toCoeff_harmonizeMulTo [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    toCoeff (harmonizeMulTo hs ds x y) = toCoeff x * toCoeff y := by
  unfold harmonizeMulTo
  simpa using toCoeff_harmonizeMul (hs := hs) (x := x) (y := y)

@[simp] theorem extract_g_harmonizeMulTo [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    extract_g (harmonizeMulTo hs ds x y)
      = ScaleSpec.scaleUS ds.dec (extract_g (harmonizeMul hs x y)) := by
  simp [harmonizeMulTo]

/-- decode の合成に対する自然性（加法版）。 -/
@[simp] theorem harmonizeAddTo_decode_comp [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (τ : ScaleSpec T BT T' BT')
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    ScaleSpec.scaleGKUS τ (harmonizeAddTo hs ds x y)
      = harmonizeAddTo hs ⟨ScaleSpec.comp τ ds.dec⟩ x y := by
  simp [harmonizeAddTo]

/-- decode の合成に対する自然性（乗法版）。 -/
@[simp] theorem harmonizeMulTo_decode_comp [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (ds : DecodeSpec H BH T BT)
    (τ : ScaleSpec T BT T' BT')
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂) :
    ScaleSpec.scaleGKUS τ (harmonizeMulTo hs ds x y)
      = harmonizeMulTo hs ⟨ScaleSpec.comp τ ds.dec⟩ x y := by
  simp [harmonizeMulTo]

end HarmonizeSpec

end DkMath.KUS
