/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Bridge
import DkMath.CosmicFormula.Defs
import DkMath.CosmicFormula.CoreBeamGap

#print "file: DkMath.KUS.CosmicBridge"

set_option linter.style.longLine false

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

/-! ## 3 層分解の KUS 対応 (phase-29) -/

/--
`Gap d 1` に対応する KUS 表現。係数 1、support unit = d。
（`Gap _ u d = u^d`、u=1 のとき値は 1）
-/
noncomputable def cosmicGap (d : ℕ) : GKUS ℕ ℕ DHNTBlueprint :=
  mkGWith 1 ⟨d, trivialBlueprint d⟩

@[simp] theorem toCoeff_cosmicGap (d : ℕ) :
    toCoeff (cosmicGap d) = 1 := rfl

@[simp] theorem extract_g_cosmicGap_unit (d : ℕ) :
    (extract_g (cosmicGap d)).unit = d := rfl

/--
`Core d 1` に対応する KUS 表現。係数 1、support unit = d。
（`Core d x = x^d`、x=1 のとき値は 1）
unit=1 での Core と Gap は値が等しい（`1^d = 1`）。
-/
noncomputable def cosmicCore (d : ℕ) : GKUS ℕ ℕ DHNTBlueprint :=
  mkGWith 1 ⟨d, trivialBlueprint d⟩

@[simp] theorem toCoeff_cosmicCore (d : ℕ) :
    toCoeff (cosmicCore d) = 1 := rfl

/-- x=u=1 のとき Core と Gap は KUS 上で等しい。 -/
theorem cosmicCore_eq_cosmicGap (d : ℕ) :
    cosmicCore d = cosmicGap d := rfl

/--
`Big d 1 1` に対応する KUS 表現。係数 `2^d`、support unit = d。
（`Big x u d = (x+u)^d`、x=u=1 のとき `2^d`）
-/
noncomputable def cosmicBig (d : ℕ) : GKUS ℕ ℕ DHNTBlueprint :=
  mkGWith (2 ^ d) ⟨d, trivialBlueprint d⟩

@[simp] theorem toCoeff_cosmicBig (d : ℕ) :
    toCoeff (cosmicBig d) = 2 ^ d := rfl

/--
`Big = Body + Gap` の KUS 係数対応。

DHNT/CosmicFormula では `Big d 1 1 = Body 1 1 d + Gap _ 1 d`。
KUS の係数上では `2^d = cosmicBodyCoeffSum d + 1`。
-/
theorem toCoeff_cosmicBig_eq (d : ℕ) :
    toCoeff (cosmicBig d)
      = (∑ k ∈ Finset.range d, toCoeff (cosmicTerm d k))
        + toCoeff (cosmicGap d) := by
  simp only [toCoeff_cosmicBig, toCoeff_cosmicGap, sum_toCoeff_cosmicTerm]
  exact_mod_cast (cosmicBodyCoeffSum_eq d).symm

/--
`Big = Core + Body + Gap` の KUS 係数対応（3 層分解）

x=u=1 では `Core = Gap = 1`、`Body = cosmicBodyCoeffSum d = 2^d - 1`
したがって `2^d = 1 + (2^d - 1) + 1 - 1 = 1 + cosmicBodyCoeffSum d + 1 - 1`
正確には `CoreBeamGap.body_eq_core_add_beam` により
`Body = Core + Beam` → `Big = Core + Beam + Gap`
KUS 係数版では `2^d = 1 + (2^d - 2) + 1`（d ≥ 1 のとき）

本補題はシンプルな 2 層版 `Big = Body + Gap` を `sum + 1 = 2^d` として述べる。
-/
theorem cosmicBig_body_gap_coeff (d : ℕ) :
    cosmicBodyCoeffSum d + toCoeff (cosmicGap d) = toCoeff (cosmicBig d) := by
  simp only [toCoeff_cosmicBig, toCoeff_cosmicGap]
  exact_mod_cast cosmicBodyCoeffSum_eq d

/--
DHNT `body_one_one` の KUS 係数版。
`Body 1 1 d + Gap _ 1 d = Big 1 1 d`（係数が一致）を KUS ℕ で述べる。
-/
theorem cosmicBodyPlusGap_eq_big (d : ℕ) :
    (∑ k ∈ Finset.range d, toCoeff (cosmicTerm d k)) + 1 = 2 ^ d := by
  rw [sum_toCoeff_cosmicTerm]
  exact_mod_cast cosmicBodyCoeffSum_eq d

/-! ## Beam の GKUS 表現（d ≥ 2 向け） -/

/--
`Beam d 1 1` に対応する KUS 係数。
`Big = Core + Beam + Gap` より `2^d = 1 + Beam + 1`。
したがって x=u=1 での Beam の係数は `2^d - 2`（d ≥ 2 が必要）。
-/
noncomputable def cosmicBeamCoeff (d : ℕ) : ℕ :=
  cosmicBodyCoeffSum d - 1  -- Body - Core = (2^d - 1) - 1

/-- `cosmicBeamCoeff d ≥ 0` は自明だが、d ≥ 2 では `cosmicBeamCoeff d + 2 = 2^d`。 -/
theorem cosmicBeamCoeff_add_two (d : ℕ) (hd : 2 ≤ d) :
    cosmicBeamCoeff d + 2 = 2 ^ d := by
  simp only [cosmicBeamCoeff]
  have hbody := cosmicBodyCoeffSum_eq d
  have hge : 1 ≤ cosmicBodyCoeffSum d := by
    have := cosmicBodyCoeffSum_ge d (by omega)
    omega
  omega

end DkMath.KUS.CosmicBridge
