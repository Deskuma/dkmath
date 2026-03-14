/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Monoid

#print "file: DkMath.KUS.Add"

/-!
## DkMath.KUS.Add — KUS 加算（phase-12）

### 設計方針

KUS は「演算結果が零になったとき、何が押しつぶされたか」を追跡する装置である。

通常演算: `n + m → 0`（zero で情報消失）
KUS 加算: `kusAdd x y → zeroState s`（zero でも `extract` で support `s` を回収可能）

加算は「同一 support（SameSupport）を持つ KUS 同士」に限定して定義する。
これにより `extract (kusAdd x y h) = extract x` が成り立ち、
係数が零になっても支持体は常に保持される（零追跡性）。

### 非目標

- 異なる support を持つ KUS 同士の加算（将来の設計候補）
- 減法・乗法・除法（加算の整合確立後に順次導入）
-/

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-! ## SameSupport（同一 support 述語） -/

/--
2 つの KUS 値が同一の support（US）を持つことを表す述語。

KUS 加算の前提条件として使う。
-/
def SameSupport (x y : KUS U Blueprint) : Prop :=
  extract x = extract y

namespace SameSupport

variable {x y z : KUS U Blueprint}

@[simp] theorem self (x : KUS U Blueprint) : SameSupport x x := rfl

theorem symm (h : SameSupport x y) : SameSupport y x := by
  unfold SameSupport at *; exact h.symm

theorem trans (h₁ : SameSupport x y) (h₂ : SameSupport y z) :
    SameSupport x z := by
  unfold SameSupport at *; exact h₁.trans h₂

/-- 同じ support から作った ofNat 同士は SameSupport。 -/
@[simp] theorem ofNat_ofNat (support : US U Blueprint) (n m : Nat) :
    SameSupport (ofNat support n) (ofNat support m) := by
  simp [SameSupport]

/-- zeroState と ofNat は SameSupport。 -/
@[simp] theorem zeroState_ofNat (support : US U Blueprint) (n : Nat) :
    SameSupport (zeroState support) (ofNat support n) := by
  simp [SameSupport]

/-- zeroState 同士は SameSupport。 -/
@[simp] theorem zeroState_self (support : US U Blueprint) :
    SameSupport (zeroState support) (zeroState support) := rfl

end SameSupport

/-! ## kusAdd（KUS 加算） -/

/--
同一 support 上の KUS 加算。

- 可視係数は `Nat` として加算する。
- support（US）は左辺のものを保持する。
- 係数が零になっても `extract (kusAdd x y h) = extract x` が成り立つ。
-/
def kusAdd (x y : KUS U Blueprint) (_ : SameSupport x y) : KUS U Blueprint :=
  ofNat (extract x) (toNat x + toNat y)

namespace kusAdd

variable {x y z : KUS U Blueprint}

/-- kusAdd の可視係数は Nat 加算に一致する。 -/
@[simp] theorem toNat_add (h : SameSupport x y) :
    toNat (kusAdd x y h) = toNat x + toNat y := by
  simp [kusAdd]

/-- kusAdd は左辺の support を保持する。 -/
@[simp] theorem extract_add_left (h : SameSupport x y) :
    extract (kusAdd x y h) = extract x := by
  simp [kusAdd]

/-- SameSupport のため右辺の support とも一致する。 -/
@[simp] theorem extract_add_right (h : SameSupport x y) :
    extract (kusAdd x y h) = extract y := by
  rw [extract_add_left h]; exact h

/-- kusAdd の結果と第三値は SameSupport（右 iff）。 -/
@[simp] theorem sameSupport_result_right (h : SameSupport x y) :
    SameSupport (kusAdd x y h) z ↔ SameSupport x z := by
  unfold SameSupport
  simp only [extract_add_left h]

/-- kusAdd の結果に右から連結する SameSupport（左 iff）。 -/
@[simp] theorem sameSupport_result_left (h : SameSupport y z) :
    SameSupport x (kusAdd y z h) ↔ SameSupport x y := by
  unfold SameSupport
  simp only [extract_add_left h]

/-! ### 零追跡補題 -/

/--
**零追跡性（Zero Tracking）**

KUS 加算の結果係数が 0 になっても、support は `extract` で回収できる。

通常演算:  `n + m = 0` → 情報消失
KUS 加算:  `toNat x + toNat y = 0` → `extract (kusAdd x y h) = extract x` は成立
-/
theorem zero_tracking (h : SameSupport x y) (_ : toNat x + toNat y = 0) :
    extract (kusAdd x y h) = extract x := by
  -- support 保持は kusAdd の定義による構造的保証であり hz に依存しない
  exact extract_add_left h

/--
加算が零になったとき、結果は zeroState として再構成できる。
-/
theorem kusAdd_eq_zeroState (h : SameSupport x y) (hz : toNat x + toNat y = 0) :
    kusAdd x y h = zeroState (extract x) := by
  unfold kusAdd
  rw [hz, ofNat_zero]

/-! ### 単位元補題 -/

/-- zeroState は左単位元。 -/
@[simp] theorem zero_add (x : KUS U Blueprint) :
    kusAdd (zeroState (extract x)) x (by simp [SameSupport]) = x := by
  simp [kusAdd]

/-- zeroState は右単位元。 -/
@[simp] theorem add_zero (x : KUS U Blueprint) :
    kusAdd x (zeroState (extract x)) (by simp [SameSupport]) = x := by
  simp [kusAdd]

/-! ### 演算法則（toNat レベル） -/

/-- 加算の交換則（toNat レベル）。 -/
theorem toNat_comm (h : SameSupport x y) :
    toNat (kusAdd x y h) = toNat (kusAdd y x (SameSupport.symm h)) := by
  simp only [toNat_add]; omega

/-- 加算の結合則（toNat レベル）。 -/
theorem toNat_assoc
    (h₁₂ : SameSupport x y) (h₂₃ : SameSupport y z)
    (h₁₂z : SameSupport (kusAdd x y h₁₂) z)
    (hx₂₃ : SameSupport x (kusAdd y z h₂₃)) :
    toNat (kusAdd (kusAdd x y h₁₂) z h₁₂z)
      = toNat (kusAdd x (kusAdd y z h₂₃) hx₂₃) := by
  simp only [toNat_add]; omega

end kusAdd

/-! ## 零閉補題 -/

/-- zeroState の加算は zeroState（零の閉性）。 -/
@[simp] theorem zeroState_kusAdd_zeroState (s : US U Blueprint) :
    kusAdd (zeroState s) (zeroState s) (by simp [SameSupport]) = zeroState s := by
  simp [kusAdd]

/-- ofNat と zeroState の加算は元の ofNat 値。 -/
@[simp] theorem kusAdd_ofNat_zeroState (support : US U Blueprint) (n : Nat) :
    kusAdd (ofNat support n) (zeroState support)
      (by simp [SameSupport]) = ofNat support n := by
  simp [kusAdd]

end DkMath.KUS
