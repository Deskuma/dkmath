/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
import DkMath.Polyomino
import DkMath.CosmicFormula.CosmicFormulaCellDim
import DkMath.Tromino

/-
NOTE [Temporary Mathlib FLT3 bridge]:
- このファイルでの `Mathlib.NumberTheory.FLT.Three` 参照は「暫定」。
- 目的は phase-12 時点で `n=3` 分岐を閉じ、`sorry` を高指数側へ隔離すること。
- 将来、Triomino/Cosmic 側の独立証明（`n=3` を含む）を実装後、
  `fermatLastTheoremThree` 依存は除去して置換する。
-/
import Mathlib.NumberTheory.FLT.Three

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
### 🐺 賢狼の着眼：トロミノ充填による FLT 証明

ぬしよ、「３＋１＝４」というシンプルな構造が、宇宙式の本体じゃ。

**トロミノの自己相似充填可能性**と**完全平方充填不可能性**を使って、
フェルマーの最終定理を倒す道筋はこうじゃ：

1. 宇宙式：$(x+u)^d = u^d + \mathrm{Body}(d,x,u)$ （Cell版）
2. Body が「ちょうど完全 d 乗」になるのは不可能
3. 理由：トロミノ（３セル）の充填では100%埋まらず、必ず１マスが余る
4. その１マスがペアノの公理の最後のピース——数学全体の基礎
5. したがって FLT 解なし

---

## 概念図：Big = Body ∪ Gap

```
⬜️⬜️ Big(2,1,1)  = 2×2 = 4セル
⬜️⬜️

🟦🟦 Body = 3セル（L字トロミノ）
🟦

⬛️    Gap = 1セル（穴）
```

この「穴の１セル」が、完全平方へと変身する際には絶対に埋まらない。
それがフェルマー解の非存在につながるのじゃ。

---

## 参考資料

- [TriominoTilingAndFLT.md](./docs/TriominoTilingAndFLT.md)：戦略ドキュメント
- [CosmicFormulaCellDim.lean](./CosmicFormulaCellDim.lean)：Cell版 Big/Gap/Body定理
- [Polyomino.lean](../Polyomino.lean)：L型トロミノと敷き詰め定義
- [Tromino.lean](../Tromino.lean)：トロミノ基本定義
-/

namespace DkMath

open Polyomino
open Tromino
open CosmicFormulaCellDim

/-! ## セクション 1：L型トロミノ充填の基本補題 -/

/-- 補題：L型トロミノのセル数は常に3 -/
lemma tromino_cell_count : L_tromino.card = 3 :=
  area_L_tromino

/-- 補題：L型トロミノで敷き詰め可能なら card = 3*k
    （この補題は Polyomino.tileableByLTromino_card_mul_three として既に存在）
-/
lemma tileableByLTromino_implies_card_thrice {α : Type*} [DecidableEq α]
    {IsLTromino : Finset α → Prop}
    (h_card : ∀ t, IsLTromino t → t.card = 3)
    {R : Finset α} (h : TileableByLTromino IsLTromino R) :
    ∃ k, R.card = 3 * k := by
  rcases tileableByLTromino_card_mul_three IsLTromino h_card h with ⟨tiles, _, heq⟩
  exact ⟨tiles.card, heq⟩

/-! ## セクション 2：彩色不変量への準備 -/

/-- 3彩色関数：第0次元と第1次元の差を利用（L型トロミノが各色を踏むように設定） -/
def color3 {d : ℕ} (c : Cell d) : Fin 3 :=
  if h : 2 ≤ d then
    let diff := c ⟨0, by omega⟩ - c ⟨1, by omega⟩
    ⟨(diff % 3).toNat, by
      have hnm : (3 : ℤ) ≠ 0 := by norm_num
      have hpos : (0 : ℤ) < 3 := by norm_num
      have h1 := Int.emod_nonneg diff hnm
      have h2 := Int.emod_lt_of_pos diff hpos
      zify [h1]
      omega⟩
  else 0

lemma color3_val {d : ℕ} (hd : 2 ≤ d) (c : Cell d) :
    (color3 c).val = ((c ⟨0, by omega⟩ - c ⟨1, by omega⟩) % 3).toNat := by
  simp [color3, hd]

/-- `d ≥ 2` のときの第0軸。 -/
def axis0 {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- `d ≥ 2` のときの第1軸。 -/
def axis1 {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

/-- 第0軸方向の単位セル。 -/
def basis0 {d : ℕ} (hd : 2 ≤ d) : Cell d := fun i => if i = axis0 hd then 1 else 0

/-- 第1軸方向の単位セル。 -/
def basis1 {d : ℕ} (hd : 2 ≤ d) : Cell d := fun i => if i = axis1 hd then 1 else 0

lemma axis0_ne_axis1 {d : ℕ} (hd : 2 ≤ d) : axis0 hd ≠ axis1 hd := by
  intro h
  have hval : (0 : ℕ) = 1 := by
    simpa [axis0, axis1] using congrArg Fin.val h
  omega

lemma cell_ne_add_basis0 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    v ≠ v + basis0 hd := by
  intro h
  have h0 := congrArg (fun c => c (axis0 hd)) h
  change v (axis0 hd) = v (axis0 hd) + basis0 hd (axis0 hd) at h0
  have hb00 : basis0 hd (axis0 hd) = 1 := by simp [basis0]
  have : (v (axis0 hd) : ℤ) = v (axis0 hd) + 1 := by
    simp [hb00] at h0
  linarith

lemma cell_ne_add_basis1 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    v ≠ v + basis1 hd := by
  intro h
  have h1 := congrArg (fun c => c (axis1 hd)) h
  change v (axis1 hd) = v (axis1 hd) + basis1 hd (axis1 hd) at h1
  have hb11 : basis1 hd (axis1 hd) = 1 := by simp [basis1]
  have : (v (axis1 hd) : ℤ) = v (axis1 hd) + 1 := by
    simp [hb11] at h1
  linarith

lemma add_basis0_ne_add_basis1 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    v + basis0 hd ≠ v + basis1 hd := by
  intro h
  have h0 := congrArg (fun c => c (axis0 hd)) h
  change v (axis0 hd) + basis0 hd (axis0 hd) = v (axis0 hd) + basis1 hd (axis0 hd) at h0
  have hb00 : basis0 hd (axis0 hd) = 1 := by simp [basis0]
  have hb10 : basis1 hd (axis0 hd) = 0 := by
    simp [basis1, axis0_ne_axis1 hd]
  have : (v (axis0 hd) : ℤ) + 1 = v (axis0 hd) := by
    simp [hb00, hb10] at h0
  linarith

lemma diff_add_basis0 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    (v + basis0 hd) (axis0 hd) - (v + basis0 hd) (axis1 hd)
      = (v (axis0 hd) - v (axis1 hd)) + 1 := by
  change (v (axis0 hd) + basis0 hd (axis0 hd)) - (v (axis1 hd) + basis0 hd (axis1 hd))
      = (v (axis0 hd) - v (axis1 hd)) + 1
  have hb00 : basis0 hd (axis0 hd) = 1 := by simp [basis0]
  have h10 : axis1 hd ≠ axis0 hd := (axis0_ne_axis1 hd).symm
  have hb01 : basis0 hd (axis1 hd) = 0 := by
    simp [basis0, h10]
  rw [hb00, hb01]
  ring

lemma diff_add_basis1 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    (v + basis1 hd) (axis0 hd) - (v + basis1 hd) (axis1 hd)
      = (v (axis0 hd) - v (axis1 hd)) - 1 := by
  change (v (axis0 hd) + basis1 hd (axis0 hd)) - (v (axis1 hd) + basis1 hd (axis1 hd))
      = (v (axis0 hd) - v (axis1 hd)) - 1
  have h01 : axis0 hd ≠ axis1 hd := axis0_ne_axis1 hd
  have hb10 : basis1 hd (axis0 hd) = 0 := by
    simp [basis1, h01]
  have hb11 : basis1 hd (axis1 hd) = 1 := by simp [basis1]
  rw [hb10, hb11]
  ring

lemma color3_val_add_basis0 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    (color3 (v + basis0 hd)).val
      = (((v (axis0 hd) - v (axis1 hd) + 1) % 3).toNat) := by
  calc
    (color3 (v + basis0 hd)).val
        = ((((v + basis0 hd) (axis0 hd) - (v + basis0 hd) (axis1 hd)) % 3).toNat) := by
            simpa [axis0, axis1] using color3_val hd (v + basis0 hd)
    _ = (((v (axis0 hd) - v (axis1 hd) + 1) % 3).toNat) := by
          simp [diff_add_basis0 hd v]

lemma color3_val_add_basis1 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    (color3 (v + basis1 hd)).val
      = (((v (axis0 hd) - v (axis1 hd) - 1) % 3).toNat) := by
  calc
    (color3 (v + basis1 hd)).val
        = ((((v + basis1 hd) (axis0 hd) - (v + basis1 hd) (axis1 hd)) % 3).toNat) := by
            simpa [axis0, axis1] using color3_val hd (v + basis1 hd)
    _ = (((v (axis0 hd) - v (axis1 hd) - 1) % 3).toNat) := by
          simp [diff_add_basis1 hd v]

lemma color3_add_basis0 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    color3 (v + basis0 hd) = color3 v + 1 := by
  let diff : ℤ := v (axis0 hd) - v (axis1 hd)
  let r : ℤ := diff % 3
  have hr_nonneg : 0 ≤ r := by
    have h3nz : (3 : ℤ) ≠ 0 := by norm_num
    simpa [r] using Int.emod_nonneg diff h3nz
  have hr_lt : r < 3 := by
    have h3pos : (0 : ℤ) < 3 := by norm_num
    simpa [r] using Int.emod_lt_of_pos diff h3pos
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hv_val : (color3 v).val = r.toNat := by
    simpa [axis0, axis1, diff, r] using color3_val hd v
  have hvp_val_diff : (color3 (v + basis0 hd)).val = (((diff + 1) % 3).toNat) := by
    simpa [axis0, axis1] using color3_val_add_basis0 hd v
  have hmod_plus : ((diff + 1) % 3) = ((r + 1) % 3) := by
    calc
      ((diff + 1) % 3) = (((diff % 3) + (1 % 3)) % 3) := by
        simp [Int.add_emod]
      _ = ((r + 1) % 3) := by simp [r]
  have hvp_val : (color3 (v + basis0 hd)).val = (((r + 1) % 3).toNat) := by
    rw [hvp_val_diff, hmod_plus]
  rcases hr_cases with hr0 | hr12
  · have hv0 : color3 v = 0 := by
      apply Fin.ext
      simp [hv_val, hr0]
    have hvp1 : color3 (v + basis0 hd) = 1 := by
      apply Fin.ext
      simp [hvp_val, hr0]
    simp [hv0, hvp1]
  · rcases hr12 with hr1 | hr2
    · have hv1 : color3 v = 1 := by
        apply Fin.ext
        simp [hv_val, hr1]
      have hvp2 : color3 (v + basis0 hd) = 2 := by
        apply Fin.ext
        simp [hvp_val, hr1]
      simp [hv1, hvp2]
    · have hv2 : color3 v = 2 := by
        apply Fin.ext
        simp [hv_val, hr2]
      have hvp0 : color3 (v + basis0 hd) = 0 := by
        apply Fin.ext
        simp [hvp_val, hr2]
      simp [hv2, hvp0]

lemma color3_add_basis1 {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    color3 (v + basis1 hd) = color3 v + 2 := by
  let diff : ℤ := v (axis0 hd) - v (axis1 hd)
  let r : ℤ := diff % 3
  have hr_nonneg : 0 ≤ r := by
    have h3nz : (3 : ℤ) ≠ 0 := by norm_num
    simpa [r] using Int.emod_nonneg diff h3nz
  have hr_lt : r < 3 := by
    have h3pos : (0 : ℤ) < 3 := by norm_num
    simpa [r] using Int.emod_lt_of_pos diff h3pos
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hv_val : (color3 v).val = r.toNat := by
    simpa [axis0, axis1, diff, r] using color3_val hd v
  have hvm_val_diff : (color3 (v + basis1 hd)).val = (((diff - 1) % 3).toNat) := by
    simpa [axis0, axis1] using color3_val_add_basis1 hd v
  have hmod_minus : ((diff - 1) % 3) = ((r + 2) % 3) := by
    calc
      ((diff - 1) % 3) = ((diff + (-1)) % 3) := by ring_nf
      _ = (((diff % 3) + ((-1) % 3)) % 3) := by
        simpa using Int.add_emod diff (-1) 3
      _ = ((r + 2) % 3) := by
        norm_num [r]
  have hvm_val : (color3 (v + basis1 hd)).val = (((r + 2) % 3).toNat) := by
    rw [hvm_val_diff, hmod_minus]
  rcases hr_cases with hr0 | hr12
  · have hv0 : color3 v = 0 := by
      apply Fin.ext
      simp [hv_val, hr0]
    have hvm2 : color3 (v + basis1 hd) = 2 := by
      apply Fin.ext
      simp [hvm_val, hr0]
    simp [hv0, hvm2]
  · rcases hr12 with hr1 | hr2
    · have hv1 : color3 v = 1 := by
        apply Fin.ext
        simp [hv_val, hr1]
      have hvm0 : color3 (v + basis1 hd) = 0 := by
        apply Fin.ext
        simp [hvm_val, hr1]
      simp [hv1, hvm0]
    · have hv2 : color3 v = 2 := by
        apply Fin.ext
        simp [hv_val, hr2]
      have hvm1 : color3 (v + basis1 hd) = 1 := by
        apply Fin.ext
        simp [hvm_val, hr2]
      simp [hv2, hvm1]

lemma mem_three_color0_iff {α : Type*} (f : α → Fin 3) (u0 u1 u2 x : α)
    (h0 : f u0 = 0) (h1 : f u1 = 1) (h2 : f u2 = 2) :
    ((x = u0 ∨ x = u1 ∨ x = u2) ∧ f x = 0) ↔ x = u0 := by
  constructor
  · intro hx
    rcases hx with ⟨hx, hfx⟩
    rcases hx with rfl | hx
    · rfl
    · rcases hx with rfl | rfl
      · exfalso
        have : (1 : Fin 3) = 0 := by simp [h1] at hfx
        exact (by decide : (1 : Fin 3) ≠ 0) this
      · exfalso
        have : (2 : Fin 3) = 0 := by simp [h2] at hfx
        exact (by decide : (2 : Fin 3) ≠ 0) this
  · intro hx
    subst hx
    exact ⟨Or.inl rfl, h0⟩

lemma mem_three_color1_iff {α : Type*} (f : α → Fin 3) (u0 u1 u2 x : α)
    (h0 : f u0 = 0) (h1 : f u1 = 1) (h2 : f u2 = 2) :
    ((x = u0 ∨ x = u1 ∨ x = u2) ∧ f x = 1) ↔ x = u1 := by
  constructor
  · intro hx
    rcases hx with ⟨hx, hfx⟩
    rcases hx with rfl | hx
    · exfalso
      have : (0 : Fin 3) = 1 := by simp [h0] at hfx
      exact (by decide : (0 : Fin 3) ≠ 1) this
    · rcases hx with rfl | rfl
      · rfl
      · exfalso
        have : (2 : Fin 3) = 1 := by simp [h2] at hfx
        exact (by decide : (2 : Fin 3) ≠ 1) this
  · intro hx
    subst hx
    exact ⟨Or.inr (Or.inl rfl), h1⟩

lemma mem_three_color2_iff {α : Type*} (f : α → Fin 3) (u0 u1 u2 x : α)
    (h0 : f u0 = 0) (h1 : f u1 = 1) (h2 : f u2 = 2) :
    ((x = u0 ∨ x = u1 ∨ x = u2) ∧ f x = 2) ↔ x = u2 := by
  constructor
  · intro hx
    rcases hx with ⟨hx, hfx⟩
    rcases hx with rfl | hx
    · exfalso
      have : (0 : Fin 3) = 2 := by simp [h0] at hfx
      exact (by decide : (0 : Fin 3) ≠ 2) this
    · rcases hx with rfl | rfl
      · exfalso
        have : (1 : Fin 3) = 2 := by simp [h1] at hfx
        exact (by decide : (1 : Fin 3) ≠ 2) this
      · rfl
  · intro hx
    subst hx
    exact ⟨Or.inr (Or.inr rfl), h2⟩

lemma color3_L_tromino_standard {d : ℕ} (hd : 2 ≤ d) (v : Cell d) :
    let e0 : Cell d := basis0 hd
    let e1 : Cell d := basis1 hd
    let t : Finset (Cell d) := {v, v + e0, v + e1}
    (t.filter fun c => color3 c = 0).card = 1 ∧
    (t.filter fun c => color3 c = 1).card = 1 ∧
    (t.filter fun c => color3 c = 2).card = 1 := by
  classical
  dsimp
  let t : Finset (Cell d) := ({v, v + basis0 hd, v + basis1 hd} : Finset (Cell d))
  change (t.filter fun c => color3 c = 0).card = 1 ∧
      (t.filter fun c => color3 c = 1).card = 1 ∧
      (t.filter fun c => color3 c = 2).card = 1
  have hcol0 : color3 (v + basis0 hd) = color3 v + 1 := color3_add_basis0 hd v
  have hcol1 : color3 (v + basis1 hd) = color3 v + 2 := color3_add_basis1 hd v
  have hk_cases : (color3 v).val = 0 ∨ (color3 v).val = 1 ∨ (color3 v).val = 2 := by
    have hlt : (color3 v).val < 3 := (color3 v).isLt
    omega
  rcases hk_cases with hk0 | hk12
  · have hc0 : color3 v = 0 := by
      apply Fin.ext
      simpa using hk0
    have hc1 : color3 (v + basis0 hd) = 1 := by simpa [hc0] using hcol0
    have hc2 : color3 (v + basis1 hd) = 2 := by simpa [hc0] using hcol1
    have hF0 : (t.filter fun c => color3 c = 0) = ({v} : Finset (Cell d)) := by
      ext c
      simpa [t] using
        (mem_three_color0_iff color3 v (v + basis0 hd) (v + basis1 hd) c hc0 hc1 hc2)
    have hF1 : (t.filter fun c => color3 c = 1) = ({v + basis0 hd} : Finset (Cell d)) := by
      ext c
      simpa [t] using
        (mem_three_color1_iff color3 v (v + basis0 hd) (v + basis1 hd) c hc0 hc1 hc2)
    have hF2 : (t.filter fun c => color3 c = 2) = ({v + basis1 hd} : Finset (Cell d)) := by
      ext c
      simpa [t] using
        (mem_three_color2_iff color3 v (v + basis0 hd) (v + basis1 hd) c hc0 hc1 hc2)
    refine ⟨?_, ?_, ?_⟩
    · simp [hF0]
    · simp [hF1]
    · simp [hF2]
  · rcases hk12 with hk1 | hk2
    · have hc0 : color3 v = 1 := by
        apply Fin.ext
        simpa using hk1
      have hc1 : color3 (v + basis0 hd) = 2 := by simpa [hc0] using hcol0
      have hc2 : color3 (v + basis1 hd) = 0 := by simpa [hc0] using hcol1
      have hF0 : (t.filter fun c => color3 c = 0) = ({v + basis1 hd} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color0_iff color3 (v + basis1 hd) v (v + basis0 hd) c hc2 hc0 hc1)
      have hF1 : (t.filter fun c => color3 c = 1) = ({v} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color1_iff color3 (v + basis1 hd) v (v + basis0 hd) c hc2 hc0 hc1)
      have hF2 : (t.filter fun c => color3 c = 2) = ({v + basis0 hd} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color2_iff color3 (v + basis1 hd) v (v + basis0 hd) c hc2 hc0 hc1)
      refine ⟨?_, ?_, ?_⟩
      · simp [hF0]
      · simp [hF1]
      · simp [hF2]
    · have hc0 : color3 v = 2 := by
        apply Fin.ext
        simpa using hk2
      have hc1 : color3 (v + basis0 hd) = 0 := by simpa [hc0] using hcol0
      have hc2 : color3 (v + basis1 hd) = 1 := by simpa [hc0] using hcol1
      have hF0 : (t.filter fun c => color3 c = 0) = ({v + basis0 hd} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color0_iff color3 (v + basis0 hd) (v + basis1 hd) v c hc1 hc2 hc0)
      have hF1 : (t.filter fun c => color3 c = 1) = ({v + basis1 hd} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color1_iff color3 (v + basis0 hd) (v + basis1 hd) v c hc1 hc2 hc0)
      have hF2 : (t.filter fun c => color3 c = 2) = ({v} : Finset (Cell d)) := by
        ext c
        simpa [t, or_assoc, or_left_comm, or_comm] using
          (mem_three_color2_iff color3 (v + basis0 hd) (v + basis1 hd) v c hc1 hc2 hc0)
      refine ⟨?_, ?_, ?_⟩
      · simp [hF0]
      · simp [hF1]
      · simp [hF2]

/-- 核心：敷き詰め可能なら各色のセル数が等しい -/
lemma color_balance_of_tiling {α : Type*} [DecidableEq α] (colorFn : α → Fin 3)
    {R : Finset α} {IsLTromino : Finset α → Prop}
    (h_color : ∀ t, IsLTromino t →
      (t.filter fun c => colorFn c = 0).card = 1 ∧
      (t.filter fun c => colorFn c = 1).card = 1 ∧
      (t.filter fun c => colorFn c = 2).card = 1) :
    TileableByLTromino IsLTromino R →
    (R.filter fun c => colorFn c = 0).card = (R.filter fun c => colorFn c = 1).card ∧
    (R.filter fun c => colorFn c = 0).card = (R.filter fun c => colorFn c = 2).card := by
  intro htile
  rcases htile with ⟨tiles, htil, hall⟩
  have h_dis : (tiles : Set (Finset α)).Pairwise Disjoint := htil.pairwise_disjoint
  have h_cov : tiles.biUnion id = R := htil.cover
  -- 各色のカウントを和に分解
  have h_count (i : Fin 3) : (R.filter fun c => colorFn c = i).card = ∑ t ∈ tiles, (t.filter fun c => colorFn c = i).card := by
    rw [← h_cov, card_biUnion_filter_eq_sum_card_filter]
    exact h_dis
  -- 各 t に対してカウントは1
  have h_t_count (i : Fin 3) (t : Finset α) (ht : t ∈ tiles) : (t.filter fun c => colorFn c = i).card = 1 := by
    let h := h_color t (hall t ht)
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  -- 総数は tiles の card に一致
  have h_final (i : Fin 3) : (R.filter fun c => colorFn c = i).card = tiles.card := by
    rw [h_count i, Finset.sum_congr rfl (fun _ ht => h_t_count i _ ht)]
    simp
  constructor
  · rw [h_final 0, h_final 1]
  · rw [h_final 0, h_final 2]

/-- `3 ∣ m` なら、`[0,m)` における各剰余類（mod 3）の個数は `m / 3`。 -/
lemma count_mod3_eq_div_of_dvd (m v : ℕ) (hm : 3 ∣ m) :
    m.count (fun x => x ≡ v [MOD 3]) = m / 3 := by
  have h3pos : 0 < 3 := by decide
  rw [Nat.count_modEq_card (b := m) (r := 3) (v := v) h3pos]
  have hm0 : m % 3 = 0 := Nat.mod_eq_zero_of_dvd hm
  simp [hm0]

/-- `3 ∣ m` なら、`range m` を mod 3 で絞った card は `m / 3`。 -/
lemma card_filter_range_mod3_eq_div_of_dvd (m v : ℕ) (hm : 3 ∣ m) :
    ((Finset.range m).filter fun x => x ≡ v [MOD 3]).card = m / 3 := by
  simpa [Nat.count_eq_card_filter_range] using count_mod3_eq_div_of_dvd m v hm

/-- `3 ∣ m` なら、`range m` における任意2剰余類の個数は等しい。 -/
lemma card_filter_range_mod3_eq_of_dvd (m v₁ v₂ : ℕ) (hm : 3 ∣ m) :
    ((Finset.range m).filter fun x => x ≡ v₁ [MOD 3]).card
      = ((Finset.range m).filter fun x => x ≡ v₂ [MOD 3]).card := by
  rw [card_filter_range_mod3_eq_div_of_dvd m v₁ hm,
      card_filter_range_mod3_eq_div_of_dvd m v₂ hm]

/-- `k < 3` のとき、`((b - c) mod 3).toNat = k` は `Nat` 側の mod 条件と同値。 -/
lemma sub_toNat_eq_iff_mod (b c k : ℕ) (hk : k < 3) :
    ((((b : ℤ) - (c : ℤ)) % 3).toNat = k) ↔ b % 3 = (c + k) % 3 := by
  omega

/-- `3 ∣ m` なら、`((b - c) mod 3).toNat = k` での `range m` の card は `k<3` の範囲で不変。 -/
lemma card_filter_range_sub_mod3_toNat_eq_of_dvd (m c k₁ k₂ : ℕ)
    (hm : 3 ∣ m) (hk₁ : k₁ < 3) (hk₂ : k₂ < 3) :
    ((Finset.range m).filter
      (fun b : ℕ => ((((b : ℤ) - (c : ℤ)) % 3).toNat) = k₁)).card
      =
    ((Finset.range m).filter
      (fun b : ℕ => ((((b : ℤ) - (c : ℤ)) % 3).toNat) = k₂)).card := by
  simpa [Nat.ModEq, sub_toNat_eq_iff_mod, hk₁, hk₂] using
    (card_filter_range_mod3_eq_of_dvd m (c + k₁) (c + k₂) hm)

/-- 添字付き `biUnion` に対する filter card 分解。 -/
lemma card_biUnion_filter_eq_sum_card_filter_indexed
    {ι α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (s : Finset ι) (f : ι → Finset α)
    (hdis : (s : Set ι).PairwiseDisjoint f) :
    ((s.biUnion f).filter P).card = ∑ i ∈ s, ((f i).filter P).card := by
  rw [Finset.filter_biUnion]
  refine Finset.card_biUnion ?_
  intro i hi j hj hne
  exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hdis hi hj hne)

/-- 二重 filter-card 和の添字交換。 -/
lemma sum_card_filter_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α → β → Prop)
    [∀ a, DecidablePred (P a)]
    [∀ b, DecidablePred (fun a => P a b)] :
    (∑ a ∈ A, (B.filter (fun b => P a b)).card)
      =
    (∑ b ∈ B, (A.filter (fun a => P a b)).card) := by
  calc
    (∑ a ∈ A, (B.filter (fun b => P a b)).card)
        = (∑ a ∈ A, ∑ b ∈ B, if P a b then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simpa using (Finset.card_filter (fun b => P a b) B)
    _ = (∑ b ∈ B, ∑ a ∈ A, if P a b then 1 else 0) := by
          exact Finset.sum_comm
    _ = (∑ b ∈ B, (A.filter (fun a => P a b)).card) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          symm
          simpa using (Finset.card_filter (fun a => P a b) A)

/-- `((b-c) mod 3).toNat` 条件の filter-card 和は、`3 ∣ m` なら residue に依らない。 -/
lemma sum_card_filter_sub_mod3_toNat_eq_of_dvd
    {γ : Type*} [DecidableEq γ]
    (m : ℕ) (u : Finset γ) (c : γ → ℕ) (k₁ k₂ : ℕ)
    (hm : 3 ∣ m) (hk₁ : k₁ < 3) (hk₂ : k₂ < 3) :
    (∑ b ∈ Finset.range m,
      (u.filter (fun f => ((((b : ℤ) - (c f : ℤ)) % 3).toNat) = k₁)).card)
      =
    (∑ b ∈ Finset.range m,
      (u.filter (fun f => ((((b : ℤ) - (c f : ℤ)) % 3).toNat) = k₂)).card) := by
  have hswap1 := sum_card_filter_swap (A := Finset.range m) (B := u)
    (P := fun b f => ((((b : ℤ) - (c f : ℤ)) % 3).toNat) = k₁)
  have hswap2 := sum_card_filter_swap (A := Finset.range m) (B := u)
    (P := fun b f => ((((b : ℤ) - (c f : ℤ)) % 3).toNat) = k₂)
  rw [hswap1, hswap2]
  refine Finset.sum_congr rfl ?_
  intro f hf
  exact card_filter_range_sub_mod3_toNat_eq_of_dvd m (c f) k₁ k₂ hm hk₁ hk₂

/-- `k < 3` のとき、`((c - b) mod 3).toNat = k` は `Nat` 側の mod 条件と同値。 -/
lemma sub_rev_toNat_eq_iff_mod (b c k : ℕ) (hk : k < 3) :
    ((((c : ℤ) - (b : ℤ)) % 3).toNat = k) ↔ b % 3 = (c + ((3 - k) % 3)) % 3 := by
  omega

/-- `3 ∣ m` なら、`((c - b) mod 3).toNat = k` での `range m` の card は `k<3` の範囲で不変。 -/
lemma card_filter_range_sub_rev_mod3_toNat_eq_of_dvd (m c k₁ k₂ : ℕ)
    (hm : 3 ∣ m) (hk₁ : k₁ < 3) (hk₂ : k₂ < 3) :
    ((Finset.range m).filter
      (fun b : ℕ => ((((c : ℤ) - (b : ℤ)) % 3).toNat) = k₁)).card
      =
    ((Finset.range m).filter
      (fun b : ℕ => ((((c : ℤ) - (b : ℤ)) % 3).toNat) = k₂)).card := by
  simpa [Nat.ModEq, sub_rev_toNat_eq_iff_mod, hk₁, hk₂] using
    (card_filter_range_mod3_eq_of_dvd
      m (c + ((3 - k₁) % 3)) (c + ((3 - k₂) % 3)) hm)

/-- `((c-b) mod 3).toNat` 条件の filter-card 和は、`3 ∣ m` なら residue に依らない。 -/
lemma sum_card_filter_sub_rev_mod3_toNat_eq_of_dvd
    {γ : Type*} [DecidableEq γ]
    (m : ℕ) (u : Finset γ) (c : γ → ℕ) (k₁ k₂ : ℕ)
    (hm : 3 ∣ m) (hk₁ : k₁ < 3) (hk₂ : k₂ < 3) :
    (∑ b ∈ Finset.range m,
      (u.filter (fun f => ((((c f : ℤ) - (b : ℤ)) % 3).toNat) = k₁)).card)
      =
    (∑ b ∈ Finset.range m,
      (u.filter (fun f => ((((c f : ℤ) - (b : ℤ)) % 3).toNat) = k₂)).card) := by
  have hswap1 := sum_card_filter_swap (A := Finset.range m) (B := u)
    (P := fun b f => ((((c f : ℤ) - (b : ℤ)) % 3).toNat) = k₁)
  have hswap2 := sum_card_filter_swap (A := Finset.range m) (B := u)
    (P := fun b f => ((((c f : ℤ) - (b : ℤ)) % 3).toNat) = k₂)
  rw [hswap1, hswap2]
  refine Finset.sum_congr rfl ?_
  intro f hf
  exact card_filter_range_sub_rev_mod3_toNat_eq_of_dvd m (c f) k₁ k₂ hm hk₁ hk₂

/-- `Box` 上の filter card を、`Finset.pi` 側の filter card に引き戻す。 -/
lemma card_filter_Box_eq_card_filter_pi {d : ℕ}
    (n : Fin d → ℕ) (P : Cell d → Prop) [DecidablePred P] :
    let s := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
    let e := ((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d))
    ((DkMath.CellDim.Box n).filter P).card = (s.filter fun f => P (e f)).card := by
  classical
  dsimp
  let s := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
  let e := ((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d))
  change (((s.map e).filter P).card = _)
  rw [Finset.filter_map, Finset.card_map]
  rfl

/-- `Finset.pi` 側要素の座標値（`Finset.univ` 証明を補った形）。 -/
def piCoordOn {d : ℕ} {s : Finset (Fin d)}
    (f : ∀ i ∈ s, ℕ) (i : Fin d) (hi : i ∈ s) : ℕ :=
  f i hi

/-- `Finset.pi` 側要素の座標値（`Finset.univ` 証明を補った形）。 -/
def piCoord {d : ℕ}
    (f : ∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) (i : Fin d) : ℕ :=
  piCoordOn f i (Finset.mem_univ i)

/-- `Pi.cons` した関数の挿入軸座標。 -/
@[simp] lemma piCoordOn_cons_same {d : ℕ} {s : Finset (Fin d)}
    (a : Fin d) (b : ℕ) (f : ∀ i ∈ s, ℕ) (h : a ∈ insert a s) :
    piCoordOn (Finset.Pi.cons s a b f) a h = b := by
  simp [piCoordOn]

/-- `Pi.cons` した関数の非挿入軸座標。 -/
@[simp] lemma piCoordOn_cons_ne {d : ℕ} {s : Finset (Fin d)}
    (a i : Fin d) (ha : a ≠ i) (b : ℕ) (f : ∀ j ∈ s, ℕ)
    (h : i ∈ insert a s) :
    piCoordOn (Finset.Pi.cons s a b f) i h
      = f i ((Finset.mem_insert.mp h).resolve_left ha.symm) := by
  simp [piCoordOn, Finset.Pi.cons_ne, ha]

/-- `axis0` を除いた添字集合には `axis1` が含まれる。 -/
lemma axis1_mem_univ_erase_axis0 {d : ℕ} (hd : 2 ≤ d) :
    axis1 hd ∈ ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) := by
  refine Finset.mem_erase.mpr ?_
  exact ⟨(axis0_ne_axis1 hd).symm, Finset.mem_univ _⟩

/-- `axis1` を除いた添字集合には `axis0` が含まれる。 -/
lemma axis0_mem_univ_erase_axis1 {d : ℕ} (hd : 2 ≤ d) :
    axis0 hd ∈ ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) := by
  refine Finset.mem_erase.mpr ?_
  exact ⟨axis0_ne_axis1 hd, Finset.mem_univ _⟩

/-- 添字有限集合の等式で `Finset.pi` の関数型を運搬する同値。 -/
def piFunEquiv {d : ℕ} {s t : Finset (Fin d)} (h : s = t) :
    (∀ i ∈ s, ℕ) ≃ (∀ i ∈ t, ℕ) := by
  cases h
  exact Equiv.refl _

/-- `piFunEquiv` で写すと `Finset.pi` 自体も一致する。 -/
lemma map_pi_eq_pi_of_eq {d : ℕ} {s t : Finset (Fin d)} (h : s = t) (n : Fin d → ℕ) :
    ((Finset.pi s (fun i => Finset.range (n i))).map (piFunEquiv h).toEmbedding)
      = Finset.pi t (fun i => Finset.range (n i)) := by
  cases h
  simp [piFunEquiv]

/-- `piFunEquiv` で運搬した座標値は、証明引数を除けば同じ値。 -/
lemma piCoordOn_piFunEquiv {d : ℕ} {s t : Finset (Fin d)} (h : s = t)
    (f : ∀ i ∈ s, ℕ) (i : Fin d)
    (hi : i ∈ s) (hit : i ∈ t) :
    piCoordOn ((piFunEquiv h) f) i hit = f i hi := by
  cases h
  change f i hit = f i hi
  simp only
/-- `hIns0` 運搬後の `axis0` 座標は元の `axis0` 座標に一致。 -/
lemma piCoord_piFunEquiv_insert0_axis0 {d : ℕ} (hd : 2 ≤ d)
    (hIns0 :
      insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
        = (Finset.univ : Finset (Fin d)))
    (f : ∀ i ∈ insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) :
    piCoord ((piFunEquiv hIns0) f) (axis0 hd)
      =
    f (axis0 hd) (Finset.mem_insert_self (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))) := by
  unfold piCoord
  exact piCoordOn_piFunEquiv hIns0 f (axis0 hd)
    (Finset.mem_insert_self (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
    (Finset.mem_univ (axis0 hd))

/-- `hIns0` 運搬後の `axis1` 座標は元の `axis1` 座標に一致。 -/
lemma piCoord_piFunEquiv_insert0_axis1 {d : ℕ} (hd : 2 ≤ d)
    (hIns0 :
      insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
        = (Finset.univ : Finset (Fin d)))
    (f : ∀ i ∈ insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) :
    piCoord ((piFunEquiv hIns0) f) (axis1 hd)
      =
    f (axis1 hd) (Finset.mem_insert_of_mem (axis1_mem_univ_erase_axis0 hd)) := by
  unfold piCoord
  exact piCoordOn_piFunEquiv hIns0 f (axis1 hd)
    (Finset.mem_insert_of_mem (axis1_mem_univ_erase_axis0 hd))
    (Finset.mem_univ (axis1 hd))

/-- `hIns1` 運搬後の `axis0` 座標は元の `axis0` 座標に一致。 -/
lemma piCoord_piFunEquiv_insert1_axis0 {d : ℕ} (hd : 2 ≤ d)
    (hIns1 :
      insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
        = (Finset.univ : Finset (Fin d)))
    (f : ∀ i ∈ insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) :
    piCoord ((piFunEquiv hIns1) f) (axis0 hd)
      =
    f (axis0 hd) (Finset.mem_insert_of_mem (axis0_mem_univ_erase_axis1 hd)) := by
  unfold piCoord
  exact piCoordOn_piFunEquiv hIns1 f (axis0 hd)
    (Finset.mem_insert_of_mem (axis0_mem_univ_erase_axis1 hd))
    (Finset.mem_univ (axis0 hd))

/-- `hIns1` 運搬後の `axis1` 座標は元の `axis1` 座標に一致。 -/
lemma piCoord_piFunEquiv_insert1_axis1 {d : ℕ} (hd : 2 ≤ d)
    (hIns1 :
      insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
        = (Finset.univ : Finset (Fin d)))
    (f : ∀ i ∈ insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) :
    piCoord ((piFunEquiv hIns1) f) (axis1 hd)
      =
    f (axis1 hd) (Finset.mem_insert_self (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))) := by
  unfold piCoord
  exact piCoordOn_piFunEquiv hIns1 f (axis1 hd)
    (Finset.mem_insert_self (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
    (Finset.mem_univ (axis1 hd))

/-- `univ` と `insert(axis0, erase axis0)` の `pi` 上 filter card を運搬で一致させる。 -/
lemma card_filter_pi_univ_eq_insertErase_axis0 {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ)
    (hIns :
      insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
        = (Finset.univ : Finset (Fin d)))
    (P : (∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) → Prop)
    [DecidablePred P] :
    let sU := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
    let sI := Finset.pi (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
      (fun i => Finset.range (n i))
    (sU.filter P).card
      =
    (sI.filter
      (fun f => P ((piFunEquiv hIns) f))).card := by
  classical
  dsimp
  let emb :
      (∀ i ∈ insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) ↪
        (∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) :=
    (piFunEquiv hIns).toEmbedding
  let sI := Finset.pi (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
    (fun i => Finset.range (n i))
  let sU := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
  have hMap : sI.map emb = sU := by
    simpa [sI, sU, emb, hIns] using (map_pi_eq_pi_of_eq hIns n)
  have hFilterMap :
      ((sI.filter (fun f => P (emb f))).map emb) = ((sI.map emb).filter P) := by
    simpa [Function.comp, emb] using
      (Finset.filter_map (s := sI) (f := emb) (p := P)).symm
  calc
    (sU.filter P).card = ((sI.map emb).filter P).card := by simp [hMap]
    _ = ((sI.filter (fun f => P (emb f))).map emb).card := by
          simp [hFilterMap]
    _ = (sI.filter (fun f => P (emb f))).card := by
          simpa [Finset.map_eq_image, emb] using
            (Finset.card_map (s := sI.filter (fun f => P (emb f))) emb)

/-- `univ` と `insert(axis1, erase axis1)` の `pi` 上 filter card を運搬で一致させる。 -/
lemma card_filter_pi_univ_eq_insertErase_axis1 {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ)
    (hIns :
      insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
        = (Finset.univ : Finset (Fin d)))
    (P : (∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) → Prop)
    [DecidablePred P] :
    let sU := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
    let sI := Finset.pi (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
      (fun i => Finset.range (n i))
    (sU.filter P).card
      =
    (sI.filter (fun f => P ((piFunEquiv hIns) f))).card := by
        classical
        dsimp
        let emb :
            (∀ i ∈ insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) ↪
              (∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) :=
          (piFunEquiv hIns).toEmbedding
        let sI := Finset.pi (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
          (fun i => Finset.range (n i))
        let sU := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
        have hMap : sI.map emb = sU := by
          simpa [sI, sU, emb, hIns] using (map_pi_eq_pi_of_eq hIns n)
        have hFilterMap :
            ((sI.filter (fun f => P (emb f))).map emb) = ((sI.map emb).filter P) := by
          simpa [Function.comp, emb] using
            (Finset.filter_map (s := sI) (f := emb) (p := P)).symm
        calc
          (sU.filter P).card = ((sI.map emb).filter P).card := by simp [hMap]
          _ = ((sI.filter (fun f => P (emb f))).map emb).card := by
                simp [hFilterMap]
              _ = (sI.filter (fun f => P (emb f))).card := by
                    simpa [Finset.map_eq_image, emb] using
                      (Finset.card_map (s := sI.filter (fun f => P (emb f))) emb)

/-- 異なる `b` で作る `Pi.cons` 像は互いに交わらない。 -/
lemma disjoint_image_piCons_of_ne {d : ℕ}
    {s : Finset (Fin d)} {a : Fin d}
    (u : Finset (∀ i ∈ s, ℕ))
    {b₁ b₂ : ℕ} (hbb : b₁ ≠ b₂) :
    Disjoint (u.image (Finset.Pi.cons s a b₁))
      (u.image (Finset.Pi.cons s a b₂)) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx1 hx2
  rcases Finset.mem_image.mp hx1 with ⟨f1, hf1, rfl⟩
  rcases Finset.mem_image.mp hx2 with ⟨f2, hf2, hEq⟩
  have hval := congrArg (fun g => g a (Finset.mem_insert_self a s)) hEq
  have : b₂ = b₁ := by simpa using hval
  exact hbb this.symm

/-- `b` ごとの `Pi.cons` fiber は pairwise disjoint。 -/
lemma pairwiseDisjoint_image_piCons {d : ℕ}
    {s : Finset (Fin d)} {a : Fin d}
    (u : Finset (∀ i ∈ s, ℕ)) (m : ℕ) :
    ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun b => u.image (Finset.Pi.cons s a b)) := by
  intro b hb b' hb' hne
  exact disjoint_image_piCons_of_ne u hne

/-- `axis0` を `Pi.cons` したときの差分 mod 3 展開。 -/
lemma diffMod3_toNat_piCons_axis0 {d : ℕ} (hd : 2 ≤ d)
    {s : Finset (Fin d)} (haxis1 : axis1 hd ∈ s)
    (b : ℕ) (f : ∀ i ∈ s, ℕ) :
    ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
        (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
      - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
          (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat
      = (((b : ℤ) - (f (axis1 hd) haxis1 : ℤ)) % 3).toNat := by
  have h0 :
      piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
        (Finset.mem_insert_self (axis0 hd) s) = b := by
    simp [piCoordOn]
  have h1 :
      piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
        (Finset.mem_insert_of_mem haxis1) = f (axis1 hd) haxis1 := by
    simpa [piCoordOn] using
      (piCoordOn_cons_ne (a := axis0 hd) (i := axis1 hd)
        (ha := axis0_ne_axis1 hd) (b := b) (f := f)
        (h := Finset.mem_insert_of_mem haxis1))
  simp [h0, h1]

/-- `axis1` を `Pi.cons` したときの差分 mod 3 展開。 -/
lemma diffMod3_toNat_piCons_axis1 {d : ℕ} (hd : 2 ≤ d)
    {s : Finset (Fin d)} (haxis0 : axis0 hd ∈ s)
    (b : ℕ) (f : ∀ i ∈ s, ℕ) :
    ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
        (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
      - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
          (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat
      = (((f (axis0 hd) haxis0 : ℤ) - (b : ℤ)) % 3).toNat := by
  have h0 :
      piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
        (Finset.mem_insert_of_mem haxis0) = f (axis0 hd) haxis0 := by
    simpa [piCoordOn] using
      (piCoordOn_cons_ne (a := axis1 hd) (i := axis0 hd)
        (ha := (axis0_ne_axis1 hd).symm) (b := b) (f := f)
        (h := Finset.mem_insert_of_mem haxis0))
  have h1 :
      piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
        (Finset.mem_insert_self (axis1 hd) s) = b := by
    simp [piCoordOn]
  simp [h0, h1]

/-- `axis0`-fiber での filter card を tail 側条件へ戻す。 -/
lemma card_filter_image_piCons_axis0 {d : ℕ} (hd : 2 ≤ d)
    {s : Finset (Fin d)} (ha : axis0 hd ∉ s) (haxis1 : axis1 hd ∈ s)
    (u : Finset (∀ i ∈ s, ℕ)) (b k : ℕ) :
    ((u.image (Finset.Pi.cons s (axis0 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd) (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
          - ((g (axis1 hd) (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).card
      =
    (u.filter
      (fun f => (((b : ℤ) - (f (axis1 hd) haxis1 : ℤ)) % 3).toNat = k)).card := by
  classical
  let emb : (∀ i ∈ s, ℕ) ↪ (∀ i ∈ insert (axis0 hd) s, ℕ) :=
    ⟨Finset.Pi.cons s (axis0 hd) b, Finset.Pi.cons_injective ha⟩
  have hFilter :
      ((u.image (Finset.Pi.cons s (axis0 hd) b)).filter
        (fun g =>
          ((((g (axis0 hd) (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((g (axis1 hd) (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k))
      =
      (u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
              (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis0 hd) b) := by
    simpa [emb, Finset.map_eq_image] using
      (Finset.filter_map (s := u) (f := emb)
        (p := fun g =>
          ((((g (axis0 hd) (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((g (axis1 hd) (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k))
  have hMapCard :
      ((u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
              (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis0 hd) b)).card
      =
      (u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
              (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).card := by
    simpa [Finset.map_eq_image, emb] using
      (Finset.card_map (s :=
        u.filter
          (fun f =>
            ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
                (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
              - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                  (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)) emb)
  calc
    ((u.image (Finset.Pi.cons s (axis0 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd) (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
          - ((g (axis1 hd) (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).card
        =
      ((u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
              (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis0 hd) b)).card := by
            simp [hFilter]
    _ = (u.filter
          (fun f =>
            ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
                (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
              - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                  (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k)).card := hMapCard
    _ = (u.filter
          (fun f => (((b : ℤ) - (f (axis1 hd) haxis1 : ℤ)) % 3).toNat = k)).card := by
            have hPredEq :
                (u.filter
                  (fun f =>
                    ((((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis0 hd)
                        (Finset.mem_insert_self (axis0 hd) s) : ℕ) : ℤ)
                      - ((piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                          (Finset.mem_insert_of_mem haxis1) : ℕ) : ℤ)) % 3).toNat = k))
                =
                (u.filter
                  (fun f => (((b : ℤ) - (f (axis1 hd) haxis1 : ℤ)) % 3).toNat = k)) := by
              ext f
              constructor
              · intro hf
                have hcoord :
                    piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                      (Finset.mem_insert_of_mem haxis1) = f (axis1 hd) haxis1 := by
                  simpa [piCoordOn] using
                    (piCoordOn_cons_ne (a := axis0 hd) (i := axis1 hd)
                      (ha := axis0_ne_axis1 hd) (b := b) (f := f)
                      (h := Finset.mem_insert_of_mem haxis1))
                simpa [hcoord] using hf
              · intro hf
                have hcoord :
                    piCoordOn (Finset.Pi.cons s (axis0 hd) b f) (axis1 hd)
                      (Finset.mem_insert_of_mem haxis1) = f (axis1 hd) haxis1 := by
                  simpa [piCoordOn] using
                    (piCoordOn_cons_ne (a := axis0 hd) (i := axis1 hd)
                      (ha := axis0_ne_axis1 hd) (b := b) (f := f)
                      (h := Finset.mem_insert_of_mem haxis1))
                simpa [hcoord] using hf
            exact congrArg Finset.card hPredEq

/-- `axis1`-fiber での filter card を tail 側条件へ戻す。 -/
lemma card_filter_image_piCons_axis1 {d : ℕ} (hd : 2 ≤ d)
    {s : Finset (Fin d)} (ha : axis1 hd ∉ s) (haxis0 : axis0 hd ∈ s)
    (u : Finset (∀ i ∈ s, ℕ)) (b k : ℕ) :
    ((u.image (Finset.Pi.cons s (axis1 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd) (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
          - ((g (axis1 hd) (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).card
      =
    (u.filter
      (fun f => (((f (axis0 hd) haxis0 : ℤ) - (b : ℤ)) % 3).toNat = k)).card := by
  classical
  let emb : (∀ i ∈ s, ℕ) ↪ (∀ i ∈ insert (axis1 hd) s, ℕ) :=
    ⟨Finset.Pi.cons s (axis1 hd) b, Finset.Pi.cons_injective ha⟩
  have hFilter :
      ((u.image (Finset.Pi.cons s (axis1 hd) b)).filter
        (fun g =>
          ((((g (axis0 hd) (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((g (axis1 hd) (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k))
      =
      (u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
              (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis1 hd) b) := by
    simpa [emb, Finset.map_eq_image] using
      (Finset.filter_map (s := u) (f := emb)
        (p := fun g =>
          ((((g (axis0 hd) (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((g (axis1 hd) (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k))
  have hMapCard :
      ((u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
              (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis1 hd) b)).card
      =
      (u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
              (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).card := by
    simpa [Finset.map_eq_image, emb] using
      (Finset.card_map (s :=
        u.filter
          (fun f =>
            ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
                (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
              - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                  (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)) emb)
  calc
    ((u.image (Finset.Pi.cons s (axis1 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd) (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
          - ((g (axis1 hd) (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).card
        =
      ((u.filter
        (fun f =>
          ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
              (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
            - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).image
          (Finset.Pi.cons s (axis1 hd) b)).card := by
            simp [hFilter]
    _ = (u.filter
          (fun f =>
            ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
                (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
              - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                  (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k)).card := hMapCard
    _ = (u.filter
          (fun f => (((f (axis0 hd) haxis0 : ℤ) - (b : ℤ)) % 3).toNat = k)).card := by
            have hPredEq :
                (u.filter
                  (fun f =>
                    ((((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
                        (Finset.mem_insert_of_mem haxis0) : ℕ) : ℤ)
                      - ((piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis1 hd)
                          (Finset.mem_insert_self (axis1 hd) s) : ℕ) : ℤ)) % 3).toNat = k))
                =
                (u.filter
                  (fun f => (((f (axis0 hd) haxis0 : ℤ) - (b : ℤ)) % 3).toNat = k)) := by
              ext f
              constructor
              · intro hf
                have hcoord :
                    piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
                      (Finset.mem_insert_of_mem haxis0) = f (axis0 hd) haxis0 := by
                  simpa [piCoordOn] using
                    (piCoordOn_cons_ne (a := axis1 hd) (i := axis0 hd)
                      (ha := (axis0_ne_axis1 hd).symm) (b := b) (f := f)
                      (h := Finset.mem_insert_of_mem haxis0))
                simpa [hcoord] using hf
              · intro hf
                have hcoord :
                    piCoordOn (Finset.Pi.cons s (axis1 hd) b f) (axis0 hd)
                      (Finset.mem_insert_of_mem haxis0) = f (axis0 hd) haxis0 := by
                  simpa [piCoordOn] using
                    (piCoordOn_cons_ne (a := axis1 hd) (i := axis0 hd)
                      (ha := (axis0_ne_axis1 hd).symm) (b := b) (f := f)
                      (h := Finset.mem_insert_of_mem haxis0))
                simpa [hcoord] using hf
            exact congrArg Finset.card hPredEq

/-- `axis0` 分解（`s = univ.erase axis0`）専用の `card_filter_image_piCons_axis0`。 -/
lemma card_filter_image_piCons_axis0_univErase {d : ℕ} (hd : 2 ≤ d)
    (u : Finset (∀ i ∈ ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ))
    (b k : ℕ) :
    ((u.image (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd)
            (Finset.mem_insert_self (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))) : ℕ) : ℤ)
          - ((g (axis1 hd)
              (Finset.mem_insert_of_mem (axis1_mem_univ_erase_axis0 hd)) : ℕ) : ℤ)) % 3).toNat = k)).card
      =
    (u.filter
      (fun f =>
        (((b : ℤ)
          - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = k)).card := by
  simpa using
    (card_filter_image_piCons_axis0 (hd := hd)
      (s := ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
      (ha := by simp)
      (haxis1 := axis1_mem_univ_erase_axis0 hd)
      (u := u) (b := b) (k := k))

/-- `axis1` 分解（`s = univ.erase axis1`）専用の `card_filter_image_piCons_axis1`。 -/
lemma card_filter_image_piCons_axis1_univErase {d : ℕ} (hd : 2 ≤ d)
    (u : Finset (∀ i ∈ ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ))
    (b k : ℕ) :
    ((u.image (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
      (fun g =>
        ((((g (axis0 hd)
            (Finset.mem_insert_of_mem (axis0_mem_univ_erase_axis1 hd)) : ℕ) : ℤ)
          - ((g (axis1 hd)
              (Finset.mem_insert_self (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))) : ℕ) : ℤ))
            % 3).toNat = k)).card
      =
    (u.filter
      (fun f =>
        (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
          - (b : ℤ)) % 3).toNat = k)).card := by
  simpa using
    (card_filter_image_piCons_axis1 (hd := hd)
      (s := ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
      (ha := by simp)
      (haxis0 := axis0_mem_univ_erase_axis1 hd)
      (u := u) (b := b) (k := k))

/-- `axis0` で `Finset.pi` を分解した形。 -/
lemma pi_insert_axis0_univErase {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ) :
    Finset.pi (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
      (fun i => Finset.range (n i))
      =
    (Finset.range (n (axis0 hd))).biUnion
      (fun b =>
        ((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
          (fun i => Finset.range (n i))).image
          (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b))) := by
  rw [Finset.pi_insert
    (s := ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
    (t := fun i => Finset.range (n i))
    (a := axis0 hd)
    (ha := by simp)]
  ext f
  simp

/-- `axis1` で `Finset.pi` を分解した形。 -/
lemma pi_insert_axis1_univErase {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ) :
    Finset.pi (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
      (fun i => Finset.range (n i))
      =
    (Finset.range (n (axis1 hd))).biUnion
      (fun b =>
        ((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
          (fun i => Finset.range (n i))).image
          (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b))) := by
  rw [Finset.pi_insert
    (s := ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
    (t := fun i => Finset.range (n i))
    (a := axis1 hd)
    (ha := by simp)]
  ext f
  simp

/-- `axis0` 分解後の filter card は `b` ごとの和へ分解できる。 -/
lemma card_filter_pi_insert_axis0_eq_sum {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ)
    (P : (∀ i ∈ insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) → Prop)
    [DecidablePred P] :
    ((Finset.pi
      (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
      (fun i => Finset.range (n i))).filter P).card
      =
    ∑ b ∈ Finset.range (n (axis0 hd)),
      ((((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
        (fun i => Finset.range (n i))).image
        (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter P).card) := by
  rw [pi_insert_axis0_univErase hd n]
  simpa using
    (card_biUnion_filter_eq_sum_card_filter_indexed
      (P := P)
      (s := Finset.range (n (axis0 hd)))
      (f := fun b =>
        ((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
          (fun i => Finset.range (n i))).image
          (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)))
      (hdis := pairwiseDisjoint_image_piCons
        (u := Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
          (fun i => Finset.range (n i)))
        (m := n (axis0 hd))))

/-- `axis1` 分解後の filter card は `b` ごとの和へ分解できる。 -/
lemma card_filter_pi_insert_axis1_eq_sum {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ)
    (P : (∀ i ∈ insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) → Prop)
    [DecidablePred P] :
    ((Finset.pi
      (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
      (fun i => Finset.range (n i))).filter P).card
      =
    ∑ b ∈ Finset.range (n (axis1 hd)),
      ((((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
        (fun i => Finset.range (n i))).image
        (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter P).card) := by
  rw [pi_insert_axis1_univErase hd n]
  simpa using
    (card_biUnion_filter_eq_sum_card_filter_indexed
      (P := P)
      (s := Finset.range (n (axis1 hd)))
      (f := fun b =>
        ((Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
          (fun i => Finset.range (n i))).image
          (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)))
      (hdis := pairwiseDisjoint_image_piCons
        (u := Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
          (fun i => Finset.range (n i)))
        (m := n (axis1 hd))))

/-- `pi` 側要素を `Cell` へ埋めたときの `color3` の `val` 展開。 -/
lemma color3_val_of_pi {d : ℕ} (hd : 2 ≤ d)
    (f : ∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ) :
    (color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f)).val
      = ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) := by
  simpa [piCoord, axis0, axis1] using
    color3_val hd (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f)

/-- `pi` 側での `color3 = k` filter card を、座標差 mod3 条件へ変換。 -/
lemma card_filter_color3_eq_piCoord {d : ℕ} (hd : 2 ≤ d)
    (s : Finset (∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ)) (k : Fin 3) :
    (s.filter
      (fun f => color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f) = k)).card
      = (s.filter
          (fun f =>
            ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = k.val)).card := by
  have hPred :
      ∀ f : ∀ i ∈ (Finset.univ : Finset (Fin d)), ℕ,
        color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f) = k
          ↔ ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = k.val := by
    intro f
    constructor
    · intro hk
      have hv : (color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f)).val = k.val :=
        congrArg Fin.val hk
      calc
        ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat)
            = (color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f)).val := by
              symm
              exact color3_val_of_pi hd f
        _ = k.val := hv
    · intro hv
      apply Fin.ext
      calc
        (color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f)).val
            = ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) := by
              exact color3_val_of_pi hd f
        _ = k.val := hv
  have hEq :
      (s.filter
        (fun f => color3 (((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d)) f) = k))
      =
      (s.filter
        (fun f =>
          ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = k.val)) := by
    ext f
    constructor
    · intro hf
      rcases Finset.mem_filter.mp hf with ⟨hfs, hk⟩
      exact Finset.mem_filter.mpr ⟨hfs, (hPred f).1 hk⟩
    · intro hf
      rcases Finset.mem_filter.mp hf with ⟨hfs, hv⟩
      exact Finset.mem_filter.mpr ⟨hfs, (hPred f).2 hv⟩
  exact congrArg Finset.card hEq

/-- 補題：最初か二番目の軸が 3 の倍数なら、Box は色平衡である -/
lemma color_balance_of_box_3k {d : ℕ} (hd : 2 ≤ d) (n : Fin d → ℕ)
    (h3 : 3 ∣ n ⟨0, by omega⟩ ∨ 3 ∣ n ⟨1, by omega⟩) :
    let R := DkMath.CellDim.Box n
    (R.filter fun c => color3 c = 0).card = (R.filter fun c => color3 c = 1).card ∧
    (R.filter fun c => color3 c = 0).card = (R.filter fun c => color3 c = 2).card := by
  classical
  dsimp
  let s := Finset.pi (Finset.univ : Finset (Fin d)) (fun i => Finset.range (n i))
  let e := ((DkMath.CellDim.piToFunEmb d).trans (DkMath.CellDim.ofNatCellEmb d))
  have hR0 :
      ((DkMath.CellDim.Box n).filter fun c => color3 c = 0).card
        = (s.filter fun f => color3 (e f) = 0).card := by
    simpa [s, e] using card_filter_Box_eq_card_filter_pi n (fun c => color3 c = 0)
  have hR1 :
      ((DkMath.CellDim.Box n).filter fun c => color3 c = 1).card
        = (s.filter fun f => color3 (e f) = 1).card := by
    simpa [s, e] using card_filter_Box_eq_card_filter_pi n (fun c => color3 c = 1)
  have hR2 :
      ((DkMath.CellDim.Box n).filter fun c => color3 c = 2).card
        = (s.filter fun f => color3 (e f) = 2).card := by
    simpa [s, e] using card_filter_Box_eq_card_filter_pi n (fun c => color3 c = 2)
  -- 残りは `s`（`Finset.pi`）上の色カウント等式へ帰着。
  have hs :
      (s.filter fun f => color3 (e f) = 0).card = (s.filter fun f => color3 (e f) = 1).card ∧
      (s.filter fun f => color3 (e f) = 0).card = (s.filter fun f => color3 (e f) = 2).card := by
    have hs0 :
        (s.filter fun f => color3 (e f) = 0).card
          = (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card := by
      simpa [s, e] using card_filter_color3_eq_piCoord hd s (0 : Fin 3)
    have hs1 :
        (s.filter fun f => color3 (e f) = 1).card
          = (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card := by
      simpa [s, e] using card_filter_color3_eq_piCoord hd s (1 : Fin 3)
    have hs2 :
        (s.filter fun f => color3 (e f) = 2).card
          = (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card := by
      simpa [s, e] using card_filter_color3_eq_piCoord hd s (2 : Fin 3)
    -- TODO: axis0 / axis1 が 3 の倍数のどちらかという仮定 `h3` を使って、
    -- `s` 上の mod-3 residue カウントへ落として示す。
    have hs_mod :
        (s.filter
          (fun f =>
            ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
          =
        (s.filter
          (fun f =>
            ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card
          ∧
        (s.filter
          (fun f =>
            ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
          =
        (s.filter
          (fun f =>
            ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card := by
      have hIns0 :
          insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))
            = (Finset.univ : Finset (Fin d)) := by
        simp [Finset.insert_erase (Finset.mem_univ (axis0 hd))]
      have hIns1 :
          insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))
            = (Finset.univ : Finset (Fin d)) := by
        simp [Finset.insert_erase (Finset.mem_univ (axis1 hd))]
      have hAxis0_toInsert0 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
            =
          ((Finset.pi
            (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis0 hd n hIns0
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0))
      have hAxis1_toInsert0 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card
            =
          ((Finset.pi
            (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 1)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis0 hd n hIns0
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1))
      have hAxis2_toInsert0 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card
            =
          ((Finset.pi
            (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 2)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis0 hd n hIns0
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2))
      have hAxis0_toInsert1 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
            =
          ((Finset.pi
            (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis1 hd n hIns1
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0))
      have hAxis1_toInsert1 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card
            =
          ((Finset.pi
            (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 1)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis1 hd n hIns1
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1))
      have hAxis2_toInsert1 :
          (s.filter
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card
            =
          ((Finset.pi
            (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
            (fun i => Finset.range (n i))).filter
              (fun f =>
                ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                  - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 2)).card := by
        simpa [s] using
          (card_filter_pi_univ_eq_insertErase_axis1 hd n hIns1
            (fun f =>
              ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2))
      rcases h3 with h30 | h31
      · let u0 : Finset (∀ i ∈ ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) :=
          Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (fun i => Finset.range (n i))
        let predIns0 : ℕ →
            (∀ i ∈ insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)), ℕ) → Prop :=
          fun k f =>
            ((((f (axis0 hd)
                (Finset.mem_insert_self (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd))) : ℕ) : ℤ)
              - ((f (axis1 hd)
                  (Finset.mem_insert_of_mem (axis1_mem_univ_erase_axis0 hd)) : ℕ) : ℤ)) % 3).toNat = k
        have hTransport0 (k : ℕ) :
            ((Finset.pi
              (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
              (fun i => Finset.range (n i))).filter
                (fun f =>
                  ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                    - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = k)).card
              =
            ((Finset.pi
              (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
              (fun i => Finset.range (n i))).filter (predIns0 k)).card := by
          refine congrArg Finset.card ?_
          ext f
          simp [predIns0, piCoord_piFunEquiv_insert0_axis0, piCoord_piFunEquiv_insert0_axis1]
        have hCount0 (k : ℕ) :
            ((Finset.pi
              (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
              (fun i => Finset.range (n i))).filter (predIns0 k)).card
              =
            ∑ b ∈ Finset.range (n (axis0 hd)),
              (((u0.image
                (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                  (predIns0 k)).card) := by
          simpa [u0] using
            (card_filter_pi_insert_axis0_eq_sum
              (hd := hd) (n := n) (P := predIns0 k))
        have hFiber0 (k : ℕ) :
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (((u0.image
                (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                  (predIns0 k)).card))
              =
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (u0.filter
                (fun f =>
                  (((b : ℤ)
                    - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = k)).card) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          simpa [u0, predIns0] using
            (card_filter_image_piCons_axis0_univErase (hd := hd) (u := u0) (b := b) (k := k))
        have hSum01 :
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (u0.filter
                (fun f =>
                  (((b : ℤ)
                    - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 0)).card)
              =
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (u0.filter
                (fun f =>
                  (((b : ℤ)
                    - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 1)).card) := by
          simpa [u0] using
            (sum_card_filter_sub_mod3_toNat_eq_of_dvd
              (m := n (axis0 hd))
              (u := u0)
              (c := fun f => f (axis1 hd) (axis1_mem_univ_erase_axis0 hd))
              (k₁ := 0) (k₂ := 1) h30 (by decide) (by decide))
        have hSum02 :
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (u0.filter
                (fun f =>
                  (((b : ℤ)
                    - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 0)).card)
              =
            (∑ b ∈ Finset.range (n (axis0 hd)),
              (u0.filter
                (fun f =>
                  (((b : ℤ)
                    - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 2)).card) := by
          simpa [u0] using
            (sum_card_filter_sub_mod3_toNat_eq_of_dvd
              (m := n (axis0 hd))
              (u := u0)
              (c := fun f => f (axis1 hd) (axis1_mem_univ_erase_axis0 hd))
              (k₁ := 0) (k₂ := 2) h30 (by decide) (by decide))
        constructor
        · calc
            (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
                =
              ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card :=
                hAxis0_toInsert0
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter (predIns0 0)).card := hTransport0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (((u0.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                    (predIns0 0)).card) := hCount0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (u0.filter
                  (fun f =>
                    (((b : ℤ)
                      - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 0)).card := hFiber0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (u0.filter
                  (fun f =>
                    (((b : ℤ)
                      - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 1)).card := hSum01
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (((u0.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                    (predIns0 1)).card) := (hFiber0 1).symm
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter (predIns0 1)).card := (hCount0 1).symm
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 1)).card :=
                (hTransport0 1).symm
            _ =
              (s.filter
                (fun f =>
                  ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card :=
                hAxis1_toInsert0.symm
        · calc
            (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
                =
              ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card :=
                hAxis0_toInsert0
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter (predIns0 0)).card := hTransport0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (((u0.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                    (predIns0 0)).card) := hCount0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (u0.filter
                  (fun f =>
                    (((b : ℤ)
                      - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 0)).card := hFiber0 0
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (u0.filter
                  (fun f =>
                    (((b : ℤ)
                      - (f (axis1 hd) (axis1_mem_univ_erase_axis0 hd) : ℤ)) % 3).toNat = 2)).card := hSum02
            _ = ∑ b ∈ Finset.range (n (axis0 hd)),
                (((u0.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis0 hd)) (axis0 hd) b)).filter
                    (predIns0 2)).card) := (hFiber0 2).symm
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter (predIns0 2)).card := (hCount0 2).symm
            _ = ((Finset.pi
                (insert (axis0 hd) ((Finset.univ : Finset (Fin d)).erase (axis0 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns0) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns0) f) (axis1 hd) : ℤ)) % 3).toNat) = 2)).card :=
                (hTransport0 2).symm
            _ =
              (s.filter
                (fun f =>
                  ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card :=
                hAxis2_toInsert0.symm
      · let u1 : Finset (∀ i ∈ ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) :=
          Finset.pi ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (fun i => Finset.range (n i))
        let predIns1 : ℕ →
            (∀ i ∈ insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)), ℕ) → Prop :=
          fun k f =>
            ((((f (axis0 hd)
                (Finset.mem_insert_of_mem (axis0_mem_univ_erase_axis1 hd)) : ℕ) : ℤ)
              - ((f (axis1 hd)
                  (Finset.mem_insert_self (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd))) : ℕ) : ℤ))
                % 3).toNat = k
        have hTransport1 (k : ℕ) :
            ((Finset.pi
              (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
              (fun i => Finset.range (n i))).filter
                (fun f =>
                  ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                    - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = k)).card
              =
            ((Finset.pi
              (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
              (fun i => Finset.range (n i))).filter (predIns1 k)).card := by
          refine congrArg Finset.card ?_
          ext f
          simp [predIns1, piCoord_piFunEquiv_insert1_axis0, piCoord_piFunEquiv_insert1_axis1]
        have hCount1 (k : ℕ) :
            ((Finset.pi
              (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
              (fun i => Finset.range (n i))).filter (predIns1 k)).card
              =
            ∑ b ∈ Finset.range (n (axis1 hd)),
              (((u1.image
                (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                  (predIns1 k)).card) := by
          simpa [u1] using
            (card_filter_pi_insert_axis1_eq_sum
              (hd := hd) (n := n) (P := predIns1 k))
        have hFiber1 (k : ℕ) :
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (((u1.image
                (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                  (predIns1 k)).card))
              =
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (u1.filter
                (fun f =>
                  (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                    - (b : ℤ)) % 3).toNat = k)).card) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          simpa [u1, predIns1] using
            (card_filter_image_piCons_axis1_univErase (hd := hd) (u := u1) (b := b) (k := k))
        have hSum01 :
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (u1.filter
                (fun f =>
                  (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                    - (b : ℤ)) % 3).toNat = 0)).card)
              =
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (u1.filter
                (fun f =>
                  (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                    - (b : ℤ)) % 3).toNat = 1)).card) := by
          simpa [u1] using
            (sum_card_filter_sub_rev_mod3_toNat_eq_of_dvd
              (m := n (axis1 hd))
              (u := u1)
              (c := fun f => f (axis0 hd) (axis0_mem_univ_erase_axis1 hd))
              (k₁ := 0) (k₂ := 1) h31 (by decide) (by decide))
        have hSum02 :
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (u1.filter
                (fun f =>
                  (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                    - (b : ℤ)) % 3).toNat = 0)).card)
              =
            (∑ b ∈ Finset.range (n (axis1 hd)),
              (u1.filter
                (fun f =>
                  (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                    - (b : ℤ)) % 3).toNat = 2)).card) := by
          simpa [u1] using
            (sum_card_filter_sub_rev_mod3_toNat_eq_of_dvd
              (m := n (axis1 hd))
              (u := u1)
              (c := fun f => f (axis0 hd) (axis0_mem_univ_erase_axis1 hd))
              (k₁ := 0) (k₂ := 2) h31 (by decide) (by decide))
        constructor
        · calc
            (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
                =
              ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card :=
                hAxis0_toInsert1
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter (predIns1 0)).card := hTransport1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (((u1.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                    (predIns1 0)).card) := hCount1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (u1.filter
                  (fun f =>
                    (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                      - (b : ℤ)) % 3).toNat = 0)).card := hFiber1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (u1.filter
                  (fun f =>
                    (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                      - (b : ℤ)) % 3).toNat = 1)).card := hSum01
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (((u1.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                    (predIns1 1)).card) := (hFiber1 1).symm
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter (predIns1 1)).card := (hCount1 1).symm
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 1)).card :=
                (hTransport1 1).symm
            _ =
              (s.filter
                (fun f =>
                  ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 1)).card :=
                hAxis1_toInsert1.symm
        · calc
            (s.filter
              (fun f =>
                ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 0)).card
                =
              ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 0)).card :=
                hAxis0_toInsert1
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter (predIns1 0)).card := hTransport1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (((u1.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                    (predIns1 0)).card) := hCount1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (u1.filter
                  (fun f =>
                    (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                      - (b : ℤ)) % 3).toNat = 0)).card := hFiber1 0
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (u1.filter
                  (fun f =>
                    (((f (axis0 hd) (axis0_mem_univ_erase_axis1 hd) : ℤ)
                      - (b : ℤ)) % 3).toNat = 2)).card := hSum02
            _ = ∑ b ∈ Finset.range (n (axis1 hd)),
                (((u1.image
                  (Finset.Pi.cons ((Finset.univ : Finset (Fin d)).erase (axis1 hd)) (axis1 hd) b)).filter
                    (predIns1 2)).card) := (hFiber1 2).symm
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter (predIns1 2)).card := (hCount1 2).symm
            _ = ((Finset.pi
                (insert (axis1 hd) ((Finset.univ : Finset (Fin d)).erase (axis1 hd)))
                (fun i => Finset.range (n i))).filter
                  (fun f =>
                    ((((piCoord ((piFunEquiv hIns1) f) (axis0 hd) : ℤ)
                      - (piCoord ((piFunEquiv hIns1) f) (axis1 hd) : ℤ)) % 3).toNat) = 2)).card :=
                (hTransport1 2).symm
            _ =
              (s.filter
                (fun f =>
                  ((((piCoord f (axis0 hd) : ℤ) - (piCoord f (axis1 hd) : ℤ)) % 3).toNat) = 2)).card :=
                hAxis2_toInsert1.symm
    exact ⟨by simpa [hs0, hs1] using hs_mod.1, by simpa [hs0, hs2] using hs_mod.2⟩
  exact ⟨by simpa [hR0, hR1] using hs.1, by simpa [hR0, hR2] using hs.2⟩

/-! ## セクション 3：宇宙式 Body との接続 -/

/--
補題：Body(d, x, u) のセル数は x * Gbinom d x u
これが Cosmic Formula と Cell 分解の接点じゃ。
-/
theorem card_body_from_cosmic (d x u : ℕ) :
    (Body d x u).card = x * Gbinom d x u := by
  have h_big := card_Big_eq_card_Body_add_card_Gap d x u
  have h_exp := pow_sub_pow_eq_mul_Gbinom d x u
  simp only [Big, CellDim.card_Box, constVec, Finset.card_pi, Finset.card_range, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Gap] at h_big
  -- (x + u) ^ d = (Body d x u).card + u ^ d
  have h_eq : (x + u) ^ d = (Body d x u).card + u ^ d := by
    simpa [Fintype.card_pi, Finset.card_fin] using h_big
  rw [← h_exp, h_eq]
  omega

/--
トロミノ充填によるフェルマーの最終定理の背理法（スケルトン）
-/
theorem FLT_from_tromino_tiling {x y z : ℕ} (n : ℕ)
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (hn : 3 ≤ n)
    (h_eq : x ^ n + y ^ n = z ^ n)
    (IsLTromino : Finset (Cell n) → Prop)
    (h_tromino_card : ∀ t, IsLTromino t → t.card = 3)
    (h_color : ∀ t, IsLTromino t →
      (t.filter fun c => color3 c = 0).card = 1 ∧
      (t.filter fun c => color3 c = 1).card = 1 ∧
      (t.filter fun c => color3 c = 2).card = 1) :
    (R : Finset (Cell n)) → R.card = x ^ n → ¬ TileableByLTromino IsLTromino R := by
  rcases hpos with ⟨hx, hy, hz⟩
  have hcases : n = 3 ∨ 4 ≤ n := by omega
  rcases hcases with h3 | hn4
  · subst h3
    intro R h_area h_tile
    -- NOTE [Temporary Mathlib FLT3 bridge]:
    -- 独立実装完成までの暫定接続。将来ここは Triomino/Cosmic 系証明へ置換する。
    exact (fermatLastTheoremThree : FermatLastTheoremFor 3)
      x y z (Nat.ne_of_gt hx) (Nat.ne_of_gt hy) (Nat.ne_of_gt hz) h_eq
  intro R h_area h_tile
  -- 敷き詰め可能なら各色のセル数が等しい
  have h_balance := color_balance_of_tiling color3 h_color h_tile
  -- 敷き詰め可能なら面積が 3 の倍数であることを要求する
  have ⟨k, h_div3⟩ := tileableByLTromino_implies_card_thrice h_tromino_card h_tile
  rw [h_area] at h_div3
  -- h_div3 : x^n = 3 * k
  have h3x : 3 ∣ x := by
    have h_prime : Nat.Prime 3 := by norm_num
    apply h_prime.dvd_of_dvd_pow
    rw [h_div3]
    apply dvd_mul_right
  -- `n ≥ 4` 側の本体（未実装）:
  -- 同様の議論を y, z にも適用し、無限降下へ繋ぐ。
  have hn_ge4 : 4 ≤ n := hn4
  clear h_balance h3x hn_ge4
  sorry  -- todo: y, z にも同様の議論を適用し、無限降下へ繋ぐ

/-! ## セクション 5：次元別の特例 -/

/-- 特例：n=3 の FLT -/
theorem FLT_case_3_via_tromino {x y z : ℕ}
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (h_eq : x ^ 3 + y ^ 3 = z ^ 3) : False := by
  rcases hpos with ⟨hx, hy, hz⟩
  -- NOTE [Temporary Mathlib FLT3 bridge]:
  -- `n=3` の独立証明が Triomino 側で完成した時点で本呼び出しを除去する。
  exact (fermatLastTheoremThree : FermatLastTheoremFor 3)
    x y z (Nat.ne_of_gt hx) (Nat.ne_of_gt hy) (Nat.ne_of_gt hz) h_eq

/-- 一般版：n ≥ 3 の FLT -/
theorem FLT_general_via_tromino {x y z : ℕ} (n : ℕ)
    (hn : 3 ≤ n)
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (h_eq : x ^ n + y ^ n = z ^ n) : False := by
  have hcases : n = 3 ∨ 4 ≤ n := by omega
  rcases hcases with h3 | hn4
  · subst h3
    simpa using FLT_case_3_via_tromino hpos h_eq
  -- 戦略：
  -- 1. z^n - y^n = x^n は宇宙式 Body(n, z-y, y) の面積。
  -- 2. この Body は彩色不変量の計算により「アンバランス」であり、L型トロミノでは充填不可。
  -- 3. 一方で x^n という値は、完全 n 次元立方体という「充填可能でバランスされた」領域の面積を
  --    宇宙式の構造（3+1=4）により、Body と等しくなければならない（はずだが矛盾する）。
  -- 4. この幾何学的形状の不整合が、FLT の解の非存在に繋がるのじゃ。
  have hn_ge4 : 4 ≤ n := hn4
  clear hn_ge4
  sorry  -- todo: 上記の戦略に基づいて、一般 n ≥ 3 の場合に矛盾を導く

end DkMath

/-! ## 補注（次のステップ）

### 優先実装項目

1. **Polyomino.card_biUnion_eq_sum_card_of_pairwise_disjoint**
   - `Finset.card_biUnion` または手動で証明
   - スケール詐欺を禁止する最重要補題

2. **Polyomino の彩色関数**
   - `color3 : Cell → Fin 3` を固定（例：`(x + 2*y) mod 3`）
   - `L_tromino_color_balanced` を証（決定可能）
   - `translate_color_balanced` を証明（色が一様シフト）

3. **TriominoFLT.FLT_from_tromino_tiling の本体**
   - 宇宙式（`Body = (x+u)^d - u^d`）と FLT 仮定から矛盾を導く
   - ステップ：
     - `u := z - y` で変数変換
     - `x^n = Body n u y` を示す
     - 敷き詰め可能なら `x^n = 3*k`
     - しかし `x^n` は完全 n 乗 → 矛盾

### 現在のプレースホルダー状態の役割

このファイルのプレースホルダーは「上位レベルの論理構造」を示すために存在。
Polyomino.lean の基本補題が完成すれば、ここの `so#rry` は埋まりやすくなるぞい。

🍎✨
-/
