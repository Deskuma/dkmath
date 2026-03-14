/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Add

#print "file: DkMath.KUS.Mul"

/-!
## DkMath.KUS.Mul — KUS 乗法（phase-13）

加法で固めた SameSupport 制約を保ったまま、
乗法を「可視係数の積 + support 保持」で定義する。

通常演算の係数は `Nat` 乗法で行うが、結果が 0 になっても
`extract` で support を回収できる（零追跡性）。
-/

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-- 同一 support 上の KUS 乗法。 -/
def kusMul (x y : KUS U Blueprint) (_ : SameSupport x y) : KUS U Blueprint :=
  ofNat (extract x) (toNat x * toNat y)

/-- fixed support 上の構造保持的な 1。 -/
def oneState (support : US U Blueprint) : KUS U Blueprint :=
  ofNat support 1

namespace kusMul

variable {x y z : KUS U Blueprint}

/-- kusMul の可視係数は Nat 乗法に一致する。 -/
@[simp] theorem toNat_mul (h : SameSupport x y) :
    toNat (kusMul x y h) = toNat x * toNat y := by
  simp [kusMul]

/-- kusMul は左辺の support を保持する。 -/
@[simp] theorem extract_mul_left (h : SameSupport x y) :
    extract (kusMul x y h) = extract x := by
  simp [kusMul]

/-- SameSupport より右辺の support とも一致する。 -/
@[simp] theorem extract_mul_right (h : SameSupport x y) :
    extract (kusMul x y h) = extract y := by
  rw [extract_mul_left h]
  exact h

/-- 結果と第三値の SameSupport（右 iff）。 -/
@[simp] theorem sameSupport_result_right (h : SameSupport x y) :
    SameSupport (kusMul x y h) z ↔ SameSupport x z := by
  unfold SameSupport
  simp only [extract_mul_left h]

/-- 結果に右連結する SameSupport（左 iff）。 -/
@[simp] theorem sameSupport_result_left (h : SameSupport y z) :
    SameSupport x (kusMul y z h) ↔ SameSupport x y := by
  unfold SameSupport
  simp only [extract_mul_left h]

/-! ### 零追跡補題 -/

/--
係数積が 0 でも support は保持される。
-/
theorem zero_tracking (h : SameSupport x y) (_ : toNat x * toNat y = 0) :
    extract (kusMul x y h) = extract x := by
  exact extract_mul_left h

/-- 係数積が 0 のとき、結果は zeroState として再構成できる。 -/
theorem kusMul_eq_zeroState (h : SameSupport x y) (hz : toNat x * toNat y = 0) :
    kusMul x y h = zeroState (extract x) := by
  unfold kusMul
  rw [hz, ofNat_zero]

/-! ### 単位元補題 -/

/-- oneState は左単位元。 -/
@[simp] theorem one_mul (x : KUS U Blueprint) :
    kusMul (oneState (extract x)) x (by
      unfold oneState SameSupport
      simp) = x := by
  simp [kusMul, oneState]

/-- oneState は右単位元。 -/
@[simp] theorem mul_one (x : KUS U Blueprint) :
    kusMul x (oneState (extract x)) (by
      unfold oneState SameSupport
      simp) = x := by
  simp [kusMul, oneState]

/-! ### 演算法則（toNat レベル） -/

/-- 乗法の交換則（toNat レベル）。 -/
theorem toNat_comm (h : SameSupport x y) :
    toNat (kusMul x y h) = toNat (kusMul y x (SameSupport.symm h)) := by
  simpa [toNat_mul] using Nat.mul_comm (toNat x) (toNat y)

/-- 乗法の結合則（toNat レベル）。 -/
theorem toNat_assoc
    (h₁₂ : SameSupport x y) (h₂₃ : SameSupport y z)
    (h₁₂z : SameSupport (kusMul x y h₁₂) z)
    (hx₂₃ : SameSupport x (kusMul y z h₂₃)) :
    toNat (kusMul (kusMul x y h₁₂) z h₁₂z)
      = toNat (kusMul x (kusMul y z h₂₃) hx₂₃) := by
  simpa [toNat_mul] using Nat.mul_assoc (toNat x) (toNat y) (toNat z)

end kusMul

/-- zeroState の乗法は zeroState（零閉性）。 -/
@[simp] theorem zeroState_kusMul_zeroState (s : US U Blueprint) :
    kusMul (zeroState s) (zeroState s) (by simp [SameSupport]) = zeroState s := by
  simp [kusMul]

/-- ofNat と oneState の乗法は元の ofNat 値。 -/
@[simp] theorem kusMul_ofNat_oneState (support : US U Blueprint) (n : Nat) :
    kusMul (ofNat support n) (oneState support)
      (by simp [SameSupport, oneState]) = ofNat support n := by
  simp [kusMul, oneState]

end DkMath.KUS
