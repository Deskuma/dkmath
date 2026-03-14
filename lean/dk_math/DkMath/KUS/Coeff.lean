/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Add
import DkMath.KUS.Mul

#print "file: DkMath.KUS.Coeff"

/-!
## DkMath.KUS.Coeff — 係数型の一般化（phase-14）

`KUS` の係数を `Nat` から任意の型 `C` に拡張した **`GKUS C U Blueprint`** を定義する。

### 設計方針

- `GKUS C U Blueprint` は `C : Type*` で係数型をパラメータ化する。
- support（`US`）の構造は係数型に依存しない。
- `gAdd`, `gMul` は `[Add C]`, `[Mul C]` で定義する（CommSemiring まで要求しない）。
- `gSub` は `[Sub C]` で定義し、`Int` 以上の係数型で使える。
- 零追跡性は係数型に依存しない structural guarantee として維持する。
- 既存 `KUS` との関係: `KUS U Blueprint = GKUS Nat U Blueprint`（abbrev で接続）。

### ロードマップ
- phase-14: `GKUS`、`gAdd`, `gMul`、`gZero`、`gOne`（CommSemiring 範囲）
- phase-15: `gSub` と `Int` 係数テスト
- phase-16: `Rat` 係数と境界値
-/

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-! ## GKUS（一般化 KUS） -/

/--
係数型 `C` を持つ一般化 KUS。

`KUS U Blueprint` は `GKUS Nat U Blueprint` の別名として定義される。
-/
@[ext] structure GKUS (C : Type*) (U : Type u) (Blueprint : BlueprintFamily U) where
  coeff : C
  unit : U
  blueprint : Blueprint unit

/-! ## 基本 API -/

/-- `US` から `GKUS` を構築する。 -/
@[simp] def mkGWith (c : C) (support : US U Blueprint) : GKUS C U Blueprint where
  coeff := c
  unit := support.unit
  blueprint := support.blueprint

/-- `GKUS` から support（`US`）を取り出す。 -/
@[simp] def extract_g (x : GKUS C U Blueprint) : US U Blueprint where
  unit := x.unit
  blueprint := x.blueprint

/-- `GKUS` の可視係数を取り出す忘却写像。 -/
@[simp] def toCoeff (x : GKUS C U Blueprint) : C :=
  x.coeff

@[simp] theorem toCoeff_mkGWith (c : C) (support : US U Blueprint) :
    toCoeff (mkGWith c support) = c := rfl

@[simp] theorem extract_g_mkGWith (c : C) (support : US U Blueprint) :
    extract_g (mkGWith c support) = support := by
  cases support; rfl

/-! ## 零・単位元 -/

section ZeroOne

variable {C : Type*}

/-- 係数ゼロ元を持つ GKUS（zero tracking の主役）。 -/
@[simp] def gZeroState [Zero C] (support : US U Blueprint) : GKUS C U Blueprint :=
  mkGWith (0 : C) support

/-- 係数単位元を持つ GKUS。 -/
@[simp] def gOneState [One C] (support : US U Blueprint) : GKUS C U Blueprint :=
  mkGWith (1 : C) support

@[simp] theorem toCoeff_gZeroState [Zero C] (support : US U Blueprint) :
    toCoeff (gZeroState (C := C) support) = 0 := rfl

@[simp] theorem toCoeff_gOneState [One C] (support : US U Blueprint) :
    toCoeff (gOneState (C := C) support) = 1 := rfl

@[simp] theorem extract_g_gZeroState [Zero C] (support : US U Blueprint) :
    extract_g (gZeroState (C := C) support) = support := by simp

@[simp] theorem extract_g_gOneState [One C] (support : US U Blueprint) :
    extract_g (gOneState (C := C) support) = support := by simp

end ZeroOne

/-! ## GSameSupport（同一 support 述語） -/

section GSameSupport

variable {C : Type*}

/-- 2 つの GKUS 値が同一の support を持つことを表す述語。 -/
def GSameSupport (x y : GKUS C U Blueprint) : Prop :=
  extract_g x = extract_g y

namespace GSameSupport

variable {x y z : GKUS C U Blueprint}

@[simp] theorem self (x : GKUS C U Blueprint) : GSameSupport x x := rfl

theorem symm (h : GSameSupport x y) : GSameSupport y x := by
  unfold GSameSupport at *; exact h.symm

theorem trans (h₁ : GSameSupport x y) (h₂ : GSameSupport y z) :
    GSameSupport x z := by
  unfold GSameSupport at *; exact h₁.trans h₂

@[simp] theorem mkGWith_mkGWith (support : US U Blueprint) (c d : C) :
    GSameSupport (mkGWith c support) (mkGWith d support) := by simp [GSameSupport]

@[simp] theorem gZeroState_mkGWith [Zero C] (support : US U Blueprint) (c : C) :
    GSameSupport (gZeroState support) (mkGWith c support) := by simp [GSameSupport]

end GSameSupport

end GSameSupport

/-! ## 演算定義 -/

section GOps

variable {C : Type*}

/--
GKUS の基底二項演算。明示的な操作関数 `op : C → C → C` を受け取り、
typeclass 推論に依存しない安定した基盤とする。
`gAdd`, `gMul`, `gSub` はこの `gOp` の特殊化として定義される。
-/
def gOp (op : C → C → C) (x y : GKUS C U Blueprint) (_ : GSameSupport x y) : GKUS C U Blueprint :=
  mkGWith (op x.coeff y.coeff) (extract_g x)

@[simp] theorem toCoeff_gOp (op : C → C → C) {x y : GKUS C U Blueprint} (h : GSameSupport x y) :
    toCoeff (gOp op x y h) = op x.coeff y.coeff := rfl

@[simp] theorem extract_g_gOp (op : C → C → C) {x y : GKUS C U Blueprint} (h : GSameSupport x y) :
    extract_g (gOp op x y h) = extract_g x := by
  simp [gOp]

/-- 同一 support 上の GKUS 加算。 -/
abbrev gAdd [Add C] (x y : GKUS C U Blueprint) (h : GSameSupport x y) : GKUS C U Blueprint :=
  gOp (· + ·) x y h

/-- 同一 support 上の GKUS 乗算。 -/
abbrev gMul [Mul C] (x y : GKUS C U Blueprint) (h : GSameSupport x y) : GKUS C U Blueprint :=
  gOp (· * ·) x y h

/-- 同一 support 上の GKUS 減算（`Int` 以上の係数型で有効）。 -/
abbrev gSub [Sub C] (x y : GKUS C U Blueprint) (h : GSameSupport x y) : GKUS C U Blueprint :=
  gOp (· - ·) x y h

namespace gAdd
variable {x y z : GKUS C U Blueprint}

@[simp] theorem toCoeff_add [Add C] (h : GSameSupport x y) :
    toCoeff (gAdd x y h) = x.coeff + y.coeff := toCoeff_gOp _ h

@[simp] theorem extract_add_left [Add C] (h : GSameSupport x y) :
    extract_g (gAdd x y h) = extract_g x := extract_g_gOp _ h

theorem zero_tracking [AddZeroClass C] (h : GSameSupport x y)
    (_ : x.coeff + y.coeff = 0) :
    extract_g (gAdd x y h) = extract_g x := extract_add_left h

end gAdd

namespace gMul
variable {x y z : GKUS C U Blueprint}

@[simp] theorem toCoeff_mul [Mul C] (h : GSameSupport x y) :
    toCoeff (gMul x y h) = x.coeff * y.coeff := toCoeff_gOp _ h

@[simp] theorem extract_mul_left [Mul C] (h : GSameSupport x y) :
    extract_g (gMul x y h) = extract_g x := extract_g_gOp _ h

theorem zero_tracking [MulZeroClass C] (h : GSameSupport x y)
    (_ : x.coeff * y.coeff = 0) :
    extract_g (gMul x y h) = extract_g x := extract_mul_left h

end gMul

namespace gSub
variable {x y : GKUS C U Blueprint}

@[simp] theorem toCoeff_sub [Sub C] (h : GSameSupport x y) :
    toCoeff (gSub x y h) = x.coeff - y.coeff := toCoeff_gOp _ h

@[simp] theorem extract_sub_left [Sub C] (h : GSameSupport x y) :
    extract_g (gSub x y h) = extract_g x := extract_g_gOp _ h

theorem zero_tracking [Sub C] [Zero C] (h : GSameSupport x y)
    (_ : x.coeff - y.coeff = 0) :
    extract_g (gSub x y h) = extract_g x := extract_sub_left h

end gSub

/-- 同一 support 上の GKUS 除算（`Rat` など `Div` を持つ係数型で有効）。

ゼロ除算は係数型の `Div` 実装に委ねられる（`Rat` では 0 / 0 = 0 など型が処理する）。
support は演算結果によらず常に保持される（zero tracking 保証）。
-/
abbrev gDiv [Div C] (x y : GKUS C U Blueprint) (h : GSameSupport x y) : GKUS C U Blueprint :=
  gOp (· / ·) x y h

namespace gDiv
variable {x y : GKUS C U Blueprint}

@[simp] theorem toCoeff_div [Div C] (h : GSameSupport x y) :
    toCoeff (gDiv x y h) = x.coeff / y.coeff := toCoeff_gOp _ h

@[simp] theorem extract_div_left [Div C] (h : GSameSupport x y) :
    extract_g (gDiv x y h) = extract_g x := extract_g_gOp _ h

/-- ゼロ追跡性: 商が 0 になっても extract_g は常に左辺の support を返す。
`Rat` では x / 0 = 0, 0 / x = 0 が Lean の定義済みゆえ本補題は無条件に使える。 -/
theorem zero_tracking [Div C] [Zero C] (h : GSameSupport x y)
    (_ : x.coeff / y.coeff = 0) :
    extract_g (gDiv x y h) = extract_g x := extract_div_left h

end gDiv

end GOps

/-! ## 代数法則（GKUS レベル） -/

section Algebra

variable {C : Type*} {x y z : GKUS C U Blueprint}

/-- 加法交換則: 同一 support 上で `gAdd x y = gAdd y x`。 -/
theorem gAdd_comm [AddCommMonoid C] (h : GSameSupport x y) :
    gAdd x y h = gAdd y x h.symm := by
  have h' : extract_g x = extract_g y := h
  simp only [gAdd, gOp]; rw [add_comm, h']

/-- 加法結合則: 同一 support を持つ 3 値に対し結合順は自由。 -/
theorem gAdd_assoc [AddSemigroup C]
    (hxy : GSameSupport x y) (hyz : GSameSupport y z)
    (h₁ : GSameSupport (gAdd x y hxy) z)
    (h₂ : GSameSupport x (gAdd y z hyz)) :
    gAdd (gAdd x y hxy) z h₁ = gAdd x (gAdd y z hyz) h₂ := by
  apply GKUS.ext
  · simp [gOp, add_assoc]
  · simp [gOp]
  · simp [gOp]

/-- 乗法交換則: 同一 support 上で `gMul x y = gMul y x`。 -/
theorem gMul_comm [CommMonoid C] (h : GSameSupport x y) :
    gMul x y h = gMul y x h.symm := by
  have h' : extract_g x = extract_g y := h
  simp only [gMul, gOp]; rw [mul_comm, h']

/-- 乗法結合則: 同一 support を持つ 3 値に対し結合順は自由。 -/
theorem gMul_assoc [Semigroup C]
    (hxy : GSameSupport x y) (hyz : GSameSupport y z)
    (h₁ : GSameSupport (gMul x y hxy) z)
    (h₂ : GSameSupport x (gMul y z hyz)) :
    gMul (gMul x y hxy) z h₁ = gMul x (gMul y z hyz) h₂ := by
  apply GKUS.ext
  · simp [gOp, mul_assoc]
  · simp [gOp]
  · simp [gOp]

/-- 左分配則: `x * (y + z) = x * y + x * z`（GKUS レベル）。 -/
theorem gMul_gAdd [Distrib C]
    (hxy : GSameSupport x y) (hyz : GSameSupport y z)
    (h₁ : GSameSupport x (gAdd y z hyz))
    (hxz : GSameSupport x z)
    (h₂ : GSameSupport (gMul x y hxy) (gMul x z hxz)) :
    gMul x (gAdd y z hyz) h₁ = gAdd (gMul x y hxy) (gMul x z hxz) h₂ := by
  apply GKUS.ext
  · simp [gOp, mul_add]
  · simp [gOp]
  · simp [gOp]

/-- 右分配則: `(x + y) * z = x * z + y * z`（GKUS レベル）。 -/
theorem gAdd_gMul [Distrib C]
    (hxy : GSameSupport x y) (hyz : GSameSupport y z)
    (h₁ : GSameSupport (gAdd x y hxy) z)
    (hxz : GSameSupport x z)
    (h₂ : GSameSupport (gMul x z hxz) (gMul y z hyz)) :
    gMul (gAdd x y hxy) z h₁ = gAdd (gMul x z hxz) (gMul y z hyz) h₂ := by
  apply GKUS.ext
  · simp [gOp, add_mul]
  · simp [gOp]
  · simp [gOp]

end Algebra

/-! ## Nat 係数との接続 -/

/--
既存 `KUS U Blueprint` を `GKUS Nat U Blueprint` として再解釈する埋め込み。

この方向の変換は「係数 `Nat` + support そのまま」なので自然。
-/
@[simp] def kusToGKUS (x : KUS U Blueprint) : GKUS Nat U Blueprint :=
  mkGWith (toNat x) (extract x)

/-- 逆方向: `GKUS Nat` から `KUS` へ変換する。 -/
@[simp] def gKUSToKUS (x : GKUS Nat U Blueprint) : KUS U Blueprint :=
  ofNat (extract_g x) x.coeff

@[simp] theorem kusToGKUS_coeff (x : KUS U Blueprint) :
    toCoeff (kusToGKUS x) = toNat x := rfl

@[simp] theorem kusToGKUS_extract (x : KUS U Blueprint) :
    extract_g (kusToGKUS x) = extract x := by
  simp [kusToGKUS, extract_g, extract]

@[simp] theorem gKUSToKUS_roundtrip (x : KUS U Blueprint) :
    gKUSToKUS (kusToGKUS x) = x := by
  simp [gKUSToKUS, kusToGKUS]

end DkMath.KUS
