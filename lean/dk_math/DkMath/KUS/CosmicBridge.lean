/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Bridge
import DkMath.CosmicFormula.Defs

#print "file: DkMath.KUS.CosmicBridge"

/-!
## DkMath.KUS.CosmicBridge

`CosmicFormula`（絶対量）と `KUS Bridge`（離散依存型 support）の接続層。

```
CosmicFormula.G / Body / Big
        │
        │  cosmicTerm k d x u  (個別項の分解)
        ↓
GKUS ℕ ℕ DHNTBlueprint         (整数係数・support は次元)
        │
        │  DHNT embedQty 経由で連続量とも対応
        ↓
kusAbsVal / toCoeff             (実体値・係数の取り出し)
```

詳細設計: `DkMath/KUS/docs/KUS-bridge-design-spec.md`
-/

namespace DkMath.KUS.CosmicBridge

open DkMath.KUS
open DkMath.KUS.Bridge
open DkMath.CosmicFormula

/-! ## DHNTBlueprint の再利用 -/

-- Bridge.lean で定義済みの DHNTBlueprint を流用
-- abbrev DHNTBlueprint := Bridge.DHNTBlueprint

/-! ## cosmicTerm — 個別項の GKUS 表現 -/

/--
`CosmicFormula.G` の第 `k` 項を `GKUS ℕ ℕ DHNTBlueprint` として表現する。

元の定義:
```
G R x u d = ∑ k ∈ range d, C(d,k+1) * x^(k+1) * u^(d-1-k)
```

ここでは係数 `C(d,k+1)` を `GKUS` の coeff に対応させ、
support unit を次元 `d` として埋め込む。
-/
noncomputable def cosmicTerm (d k : ℕ) : GKUS ℕ ℕ DHNTBlueprint :=
  mkGWith (Nat.choose d (k + 1)) ⟨d, trivialBlueprint d⟩

@[simp] theorem toCoeff_cosmicTerm (d k : ℕ) :
    toCoeff (cosmicTerm d k) = Nat.choose d (k + 1) := rfl

@[simp] theorem extract_g_cosmicTerm_unit (d k : ℕ) :
    (extract_g (cosmicTerm d k)).unit = d := rfl

/-! ## cosmicBody — Body の GKUS 和分解 -/

/--
`Body d 1 1 = G ℝ 1 1 d = ∑ k, C(d,k+1)` の整数版。
単位を 1 に設定したときの Body の係数和が `2^d - 1` に等しいことを示す補題の
下準備として `Finset.sum` ベースの表現を用意する。
-/
noncomputable def cosmicBodyCoeffSum (d : ℕ) : ℕ :=
  ∑ k ∈ Finset.range d, Nat.choose d (k + 1)

/--
`cosmicBodyCoeffSum d = 2^d - 1`
（二項定理 `∑_{k=0}^{d} C(d,k) = 2^d` から `k=0` 項を引いた値）
-/
theorem cosmicBodyCoeffSum_eq (d : ℕ) :
    cosmicBodyCoeffSum d + 1 = 2 ^ d := by
  simp only [cosmicBodyCoeffSum]
  have h := Nat.sum_range_choose d
  -- h : ∑ k ∈ range (d+1), C(d,k) = 2^d
  rw [Finset.sum_range_succ'] at h
  -- 分離した: C(d,0) + ∑_{k < d} C(d,k+1) = 2^d
  simp only [Nat.choose_zero_right] at h
  linarith

/-- `cosmicBodyCoeffSum d ≥ d` — 次元数以上の係数和を持つ。 -/
theorem cosmicBodyCoeffSum_ge (d : ℕ) (_ : 1 ≤ d) :
    d ≤ cosmicBodyCoeffSum d := by
  simp only [cosmicBodyCoeffSum]
  calc d = ∑ _ ∈ Finset.range d, 1 := by simp
    _ ≤ ∑ k ∈ Finset.range d, Nat.choose d (k + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_range] at hk
        have : 1 ≤ k + 1 ∧ k + 1 ≤ d := ⟨Nat.succ_le_succ (Nat.zero_le k), hk⟩
        exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos this.2 |>.ne')

/-! ## Body と toCoeff の対応 -/

/--
`G ℕ 1 1 d = cosmicBodyCoeffSum d`
整数引数で評価した Body の係数和は `cosmicBodyCoeffSum` に等しい。
-/
theorem G_one_one_eq (d : ℕ) :
    G ℕ 1 1 d = cosmicBodyCoeffSum d := by
  simp [G, cosmicBodyCoeffSum, d_sub_one_k, d_sub_n_k]

/--
`Body d 1 1 + 1 = 2^d` （ℝ 上）
`B(d, 1, 1) = G ℝ 1 1 d = 2^d - 1`（実数でも成立）
-/
theorem body_one_one (d : ℕ) :
    Body 1 1 d + 1 = (2 : ℝ) ^ d := by
  have h : cosmicBodyCoeffSum d + 1 = 2 ^ d := cosmicBodyCoeffSum_eq d
  simp only [Body, G, cosmicBodyCoeffSum, d1k] at *
  simp only [mul_one, one_pow] at *
  norm_cast at h ⊢

/-! ## GKUS → CosmicFormula の方向 -/

/--
`cosmicTerm d k` の抽象係数和が `cosmicBodyCoeffSum` に一致することの直和版。
個別 GKUS 項の `toCoeff` を sum すると Body の係数和になる。
-/
theorem sum_toCoeff_cosmicTerm (d : ℕ) :
    ∑ k ∈ Finset.range d, toCoeff (cosmicTerm d k)
      = cosmicBodyCoeffSum d := by
  simp only [toCoeff_cosmicTerm, cosmicBodyCoeffSum]

end DkMath.KUS.CosmicBridge
