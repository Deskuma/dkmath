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

/-! ## typeclass-based decode strategy -/

/-- 左系 decode を供給する型クラス。 -/
class LeftDecode
    (C : Type*)
    (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
    (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
    (H : Type uH) (BH : BlueprintFamily H)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH) where
  decLeft : ScaleSpec H BH U₁ B₁

/-- 右系 decode を供給する型クラス。 -/
class RightDecode
    (C : Type*)
    (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
    (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
    (H : Type uH) (BH : BlueprintFamily H)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH) where
  decRight : ScaleSpec H BH U₂ B₂

/-- 正規形 decode を供給する型クラス。 -/
class NormalizedDecode
    (C : Type*)
    (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
    (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
    (H : Type uH) (BH : BlueprintFamily H)
    (T : Type uT) (BT : BlueprintFamily T)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH) where
  decNorm : ScaleSpec H BH T BT

/-- decode 戦略タグ：左優先。 -/
structure UseLeft : Type

/-- decode 戦略タグ：右優先。 -/
structure UseRight : Type

/-- decode 戦略タグ：正規形。 -/
structure UseNormalized (T : Type uT) (BT : BlueprintFamily T) : Type

/-- decode 戦略を型クラスで選ぶための統一インターフェース。 -/
class DecodeStrategy
    (S : Type*)
    (C : Type*)
    (U₁ : Type u₁) (B₁ : BlueprintFamily U₁)
    (U₂ : Type u₂) (B₂ : BlueprintFamily U₂)
    (H : Type uH) (BH : BlueprintFamily H)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH) where
  T : outParam (Type _)
  BT : outParam (BlueprintFamily T)
  dec : ScaleSpec H BH T BT

instance instDecodeStrategyUseLeft
    {C : Type*}
    {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
    {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
    {H : Type uH} {BH : BlueprintFamily H}
    {hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH}
    [d : LeftDecode C U₁ B₁ U₂ B₂ H BH hs] :
    DecodeStrategy UseLeft C U₁ B₁ U₂ B₂ H BH hs where
  T := U₁
  BT := B₁
  dec := d.decLeft

instance instDecodeStrategyUseRight
    {C : Type*}
    {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
    {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
    {H : Type uH} {BH : BlueprintFamily H}
    {hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH}
    [d : RightDecode C U₁ B₁ U₂ B₂ H BH hs] :
    DecodeStrategy UseRight C U₁ B₁ U₂ B₂ H BH hs where
  T := U₂
  BT := B₂
  dec := d.decRight

instance instDecodeStrategyUseNormalized
    {C : Type*}
    {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
    {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
    {H : Type uH} {BH : BlueprintFamily H}
    {T : Type uT} {BT : BlueprintFamily T}
    {hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH}
    [d : NormalizedDecode C U₁ B₁ U₂ B₂ H BH T BT hs] :
    DecodeStrategy (UseNormalized T BT) C U₁ B₁ U₂ B₂ H BH hs where
  T := T
  BT := BT
  dec := d.decNorm

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

/-! ## HarmonizeSpec builder API -/

/--
`mkHarmonize` — `HarmonizeSpec` の汎用最小 builder。

`hSameSupport` として
「両 encode が常に同一の `US H BH` へ写す」ことを直接受け取り、
`sameSupport` フィールドを自動生成する。
-/
def mkHarmonize
    {C : Type*}
    {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
    {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
    {H : Type uH} {BH : BlueprintFamily H}
    (encLeft : ScaleSpec U₁ B₁ H BH)
    (encRight : ScaleSpec U₂ B₂ H BH)
    (hSameSupport : ∀ (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂),
        ScaleSpec.scaleUS encLeft (extract_g x)
          = ScaleSpec.scaleUS encRight (extract_g y)) :
    HarmonizeSpec C U₁ B₁ U₂ B₂ H BH where
  encLeft  := encLeft
  encRight := encRight
  sameSupport := fun x y => by
    simp only [GSameSupport, ScaleSpec.extract_g_scaleGKUS]
    exact hSameSupport x y

/--
`mkHarmonizeFixed` — 両 encode が固定 support `cs : US H BH` へ常に写す場合の builder。
`hL`/`hR` の証明に `simp [ScaleSpec.scaleUS, ...]` が使えるため実用的に使いやすい。
-/
def mkHarmonizeFixed
    {C : Type*}
    {U₁ : Type u₁} {B₁ : BlueprintFamily U₁}
    {U₂ : Type u₂} {B₂ : BlueprintFamily U₂}
    {H : Type uH} {BH : BlueprintFamily H}
    (encLeft : ScaleSpec U₁ B₁ H BH)
    (encRight : ScaleSpec U₂ B₂ H BH)
    (cs : US H BH)
    (hL : ∀ (x : GKUS C U₁ B₁), ScaleSpec.scaleUS encLeft (extract_g x) = cs)
    (hR : ∀ (y : GKUS C U₂ B₂), ScaleSpec.scaleUS encRight (extract_g y) = cs) :
    HarmonizeSpec C U₁ B₁ U₂ B₂ H BH :=
  mkHarmonize encLeft encRight (fun x y => by rw [hL x, hR y])

/--
`mkHarmonizeSameSpec` — 両系が同一 `enc` を共有し、固定 support `cs` へ写す場合の builder。
`mkHarmonizeFixed enc enc cs h h` の syntactic shorthand。
-/
def mkHarmonizeSameSpec
    {C : Type*}
    {U : Type u₁} {B : BlueprintFamily U}
    {H : Type uH} {BH : BlueprintFamily H}
    (enc : ScaleSpec U B H BH)
    (cs : US H BH)
    (h : ∀ (x : GKUS C U B), ScaleSpec.scaleUS enc (extract_g x) = cs) :
    HarmonizeSpec C U B U B H BH :=
  mkHarmonizeFixed enc enc cs h h

/-! ## typeclass-selected APIs -/

/-- decode 戦略 `S` を型クラスで選ぶ加算 API。 -/
@[simp] def harmonizeAddBy [Add C] (S : Type*)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [d : DecodeStrategy S C U₁ B₁ U₂ B₂ H BH hs] : GKUS C d.T d.BT :=
  harmonizeAddTo hs (DecodeSpec.ofScale d.dec) x y

/-- decode 戦略 `S` を型クラスで選ぶ乗算 API。 -/
@[simp] def harmonizeMulBy [Mul C] (S : Type*)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [d : DecodeStrategy S C U₁ B₁ U₂ B₂ H BH hs] : GKUS C d.T d.BT :=
  harmonizeMulTo hs (DecodeSpec.ofScale d.dec) x y

@[simp] theorem toCoeff_harmonizeAddBy [Add C] (S : Type*)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [d : DecodeStrategy S C U₁ B₁ U₂ B₂ H BH hs] :
    toCoeff (harmonizeAddBy (S := S) hs x y) = toCoeff x + toCoeff y := by
  unfold harmonizeAddBy
  simpa using toCoeff_harmonizeAddTo (hs := hs) (ds := DecodeSpec.ofScale d.dec) (x := x) (y := y)

@[simp] theorem toCoeff_harmonizeMulBy [Mul C] (S : Type*)
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [d : DecodeStrategy S C U₁ B₁ U₂ B₂ H BH hs] :
    toCoeff (harmonizeMulBy (S := S) hs x y) = toCoeff x * toCoeff y := by
  unfold harmonizeMulBy
  simpa using toCoeff_harmonizeMulTo (hs := hs) (ds := DecodeSpec.ofScale d.dec) (x := x) (y := y)

/-- 左戦略の加算 API（型クラス自動選択）。 -/
@[simp] def harmonizeAddAutoLeft [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [LeftDecode C U₁ B₁ U₂ B₂ H BH hs] : GKUS C U₁ B₁ :=
  harmonizeAddBy (S := UseLeft) hs x y

/-- 右戦略の加算 API（型クラス自動選択）。 -/
@[simp] def harmonizeAddAutoRight [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [RightDecode C U₁ B₁ U₂ B₂ H BH hs] : GKUS C U₂ B₂ :=
  harmonizeAddBy (S := UseRight) hs x y

/-- 正規形戦略の加算 API（型クラス自動選択）。 -/
@[simp] def harmonizeAddAutoNormalized [Add C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [NormalizedDecode C U₁ B₁ U₂ B₂ H BH T BT hs] : GKUS C T BT :=
  harmonizeAddBy (S := UseNormalized T BT) hs x y

/-- 左戦略の乗算 API（型クラス自動選択）。 -/
@[simp] def harmonizeMulAutoLeft [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [LeftDecode C U₁ B₁ U₂ B₂ H BH hs] : GKUS C U₁ B₁ :=
  harmonizeMulBy (S := UseLeft) hs x y

/-- 右戦略の乗算 API（型クラス自動選択）。 -/
@[simp] def harmonizeMulAutoRight [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [RightDecode C U₁ B₁ U₂ B₂ H BH hs] : GKUS C U₂ B₂ :=
  harmonizeMulBy (S := UseRight) hs x y

/-- 正規形戦略の乗算 API（型クラス自動選択）。 -/
@[simp] def harmonizeMulAutoNormalized [Mul C]
    (hs : HarmonizeSpec C U₁ B₁ U₂ B₂ H BH)
    (x : GKUS C U₁ B₁) (y : GKUS C U₂ B₂)
    [NormalizedDecode C U₁ B₁ U₂ B₂ H BH T BT hs] : GKUS C T BT :=
  harmonizeMulBy (S := UseNormalized T BT) hs x y

end HarmonizeSpec

end DkMath.KUS
