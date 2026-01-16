/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
-- import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
-- import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace DkMath
namespace CosmicFormulaDim

open scoped BigOperators Real

/-! ### A: 代数レイヤ（d 次元の「実体項」G） -/

/-- d 次元の「実体項」G の定義 -/
noncomputable def G (d : ℕ) (x u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    (Nat.choose d (k+1) : ℝ) * x^k * u^(d-1-k)

/--
cosmic_id : (x + u)^d - x * G d x u = u^d に関する数学的説明（日本語）

命題の主張:
  任意の自然数 d と実数 x, u について
    (x + u)^d - x * G d x u = u^d
  が成り立つ。

証明のアイデア（高レベル）:
  1. 二項定理 (add_pow) を用いて (x + u)^d を
     Σ_{k=0}^{d} C(d,k) x^k u^{d-k} に展開する。
  2. 定義から x * G d x u は
     Σ_{j=0}^{d-1} C(d,j+1) x^{j+1} u^{d-1-j}
     と展開できる（添え字を調整すれば k≥1 の項に対応する）。
  3. (1) の和を k=0 の項（即ち u^d）と k≥1 の和に分離する。
     k≥1 の和は添え字 k ↦ k+1 によって (2) の和と一致するので、
     (x+u)^d から x * G d x u を引くと残るのは u^d だけになる。

補題・注意点:
  - Finset.sum_range_succ' を用いて k=d の項（または k=0 の項）を分離する。
  - 添え字の変形には sum_congr を用いる。具体的には k を k+1 にシフトして
    指数 d-(k+1) = d-1-k の等式を使う必要がある。
  - 自然数の減算に関する等式（Nat.sub_sub や Nat.succ_le_of_lt 等）を明示的に
   扱い、必要なら omega（または同等の補題）で細かい等号を解決する。
  - 結合・交換・係数に関する単純な代数処理は ring や simp（例えば
    Nat.choose_zero_right, pow_zero, mul_one）で片付ける。

まとめ:
  二項展開の k=0 項が目標の u^d を与え、残る項は x*G の展開と対応して互いに打ち消すため、等式が成立する。
-/
theorem cosmic_id (d : ℕ) (x u : ℝ) :
    (x + u)^d - x * G d x u = u^d := by
  unfold G
  rw [add_pow, Finset.mul_sum]
  -- 二項定理: (x+u)^d = Σ_{k=0}^{d} C(d,k) x^k u^{d-k}
  -- G の展開: x * G = Σ_{j=0}^{d-1} C(d,j+1) x^{j+1} u^{d-1-j}
  -- 戦略: 二項展開の k=0 項(= u^d)を分離し、残りの和が相殺されることを示す

  -- 補題1: 二項展開を k=0 の項と k≥1 の項に分割
  have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * ↑(d.choose k)
          = x^0 * u^d * ↑(d.choose 0)
          + ∑ k ∈ Finset.range d, x^(k+1) * u^(d-1-k) * ↑(d.choose (k+1)) := by
    rw [Finset.sum_range_succ']  -- k=d の項を分離
    simp only [pow_zero, Nat.sub_zero]
    rw [add_comm]  -- 項の順序を入れ替え: Σ_{0..d-1} + [k=d] → [k=d] + Σ_{0..d-1}
    congr 1
    -- 各項で指数を調整: d - (k+1) = d - 1 - k
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    -- k < d を用いて d-(k+1) = d-1-k を示す（omegaは自然数減算に弱いため明示的に）
    have hk' : k < d := Finset.mem_range.mp hk
    have h1 : k + 1 ≤ d := Nat.succ_le_of_lt hk'
    have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
    have h3 : d - k - 1 = d - 1 - k := by omega
    rw [h2, h3]
  -- 補題2: x * G を展開すると、補題1の第2項と同じ形になる
  have h2 : ∑ k ∈ Finset.range d, x * (↑(d.choose (k + 1)) * x ^ k * u ^ (d - 1 - k))
          = ∑ k ∈ Finset.range d, x^(k+1) * u^(d-1-k) * ↑(d.choose (k+1)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- 補題1と補題2より、二つの和が相殺されて u^d のみが残る
  rw [h1, h2]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  ring


/-! ### C: 解析接続の橋脚（体積定数） -/

/-- d 次元球の体積定数の複素数版 -/
noncomputable def volConstC (s : ℂ) : ℂ :=
  (π : ℂ)^(s/2) / Complex.Gamma (s/2 + 1)

-- 整数点では「いつもの定数」に一致、みたいな補題を作る

/-- 整数点での体積定数の評価 -/
theorem volConstC_nat (n : ℕ) :
    volConstC n = (π : ℂ)^( (n:ℂ)/2 ) / Complex.Gamma ((n:ℂ)/2 + 1) := by
  simp [volConstC]

/-! そして `EuclideanSpace.volume_ball` を “評価点 n” で回収する橋を架ける。
    ここは coercion (ℝ→ENNReal→ℝ) の整理が主戦場。 -/

-- 偶数次元評価の補題群

open scoped Real

/--
偶数次元 2*m に対する定数 `volConstC` の評価を与える補題。

具体的には
  volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ)
が成り立つ。

証明の方針：
定義を展開して (2*m)/2 = m を用い，複素べき乗や有理数のキャストによる簡約を行うと，
ガンマ関数の項が `Complex.Gamma (m + 1 : ℂ)` の形になる．
ここで補題 `Complex.Gamma_nat_eq_factorial` を適用して `Γ(m+1)=m!` と置き換えれば結論が得られる。
-/
theorem volConstC_even (m : ℕ) :
    volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ) := by
  -- 展開して (2*m)/2 = m および Γ(m+1)=m! を使う
  simp only [volConstC, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
    Complex.cpow_natCast]
  -- ここで ((2*m : ℂ)/2 + 1) が (m + 1 : ℂ) になっているはずなのでガンマ関数の整数値評価を適用
  have hg : Complex.Gamma (m + 1 : ℂ) = (Nat.factorial m : ℂ) := by
    -- mathlib の補題を利用
    exact Complex.Gamma_nat_eq_factorial m
  rw [hg]

/--
偶数次元 2*m における体積定数の簡潔な説明と証明方針。

定理は
  volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ)
を主張する。証明は定義
  volConstC n = π^(n/2) / Γ(n/2 + 1)
に n = 2*m を代入し、(2*m)/2 = m を用いることで
  π^(m) / Γ(m + 1)
とし、さらにガンマ関数の整数引数に対する恒等式
  Γ(m+1) = m!
(Complex.Gamma_nat_eq_factorial) を適用して右辺が π^m / m! になることから得られる。
また証明中に (2 : ℂ) ≠ 0 を確認するために norm_num を用いている。
-/
theorem volConstC_even' (m : ℕ) :
    volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ) := by
  have h : (2:ℂ) ≠ 0 := by norm_num
  -- 展開して (2*m)/2 = m および Γ(m+1)=m! を使う
  simp [volConstC, h, Complex.Gamma_nat_eq_factorial]

-- ここから先は実数版の体積定数とその偶数次元評価、および
-- `EuclideanSpace.volume_ball` からの回収の橋を架ける補題群

open scoped BigOperators Real ENNReal
open MeasureTheory

/-- 実数版：体積定数（mathlib の `EuclideanSpace.volume_ball` に合わせて √π を使う版） -/
noncomputable def volConstR (n : ℕ) : ℝ :=
  (Real.sqrt Real.pi) ^ n / Real.Gamma ((n : ℝ) / 2 + 1)

/-- 偶数次元での実数版体積定数の評価：volConstR (2*m) = π^m / m! -/
theorem volConstR_even (m : ℕ) :
    volConstR (2*m) = Real.pi^m / (Nat.factorial m) := by
  unfold volConstR
  -- 分子の簡約：(√π)^(2*m) = π^m
  have hsqrt : (Real.sqrt Real.pi)^(2*m) = Real.pi^m := by
    have h1 : (Real.sqrt Real.pi)^(2*m) = ((Real.sqrt Real.pi)^2)^m := by
      rw [← pow_mul]
    rw [h1, Real.sq_sqrt (le_of_lt Real.pi_pos)]
  rw [hsqrt]
  -- 分母の簡約：↑(2*m)/2 + 1 = ↑m + 1 にしてからガンマ関数を階乗に変換
  congr 1
  have hdiv : (↑(2*m) : ℝ)/2 + 1 = (m : ℝ) + 1 := by
    push_cast
    ring
  rw [hdiv, Real.Gamma_nat_eq_factorial]


/-!
## 偶数次元の球体積：`EuclideanSpace.volume_ball` から回収する橋

目標（概形）：
  volume (ball (0) r) = ofReal (π^m / m!) * (ofReal r)^(2*m)

注意：
- `volume` は `ENNReal`、係数は `Real` → `ENNReal.ofReal` へキャストされる。
- `r < 0` の場合は ball が空になったり `ofReal` が 0 扱いになったりするので、
  必要なら `by_cases hr : 0 ≤ r` を挟む。
-/

/-- `EuclideanSpace ℝ (Fin (2*m))` の原点中心球の体積（偶数次元版の形） -/
theorem volume_ball_fin_even (m : ℕ) (hm : m ≥ 1) (r : ℝ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r)
      =
    ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
      * (ENNReal.ofReal r) ^ (2*m) := by
  classical
  -- m ≥ 1 より 2*m ≥ 2 > 0 なので Fin (2*m) は非空
  have : Nonempty (Fin (2*m)) := by
    apply Fin.pos_iff_nonempty.mp
    omega
  -- 一般公式を取得
  have hball :=
    (EuclideanSpace.volume_ball
      (x := (0 : EuclideanSpace ℝ (Fin (2*m))))
      (r := r))
  -- volConstR を用いて係数を整理
  have hball' : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r)
        =
      (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (volConstR (2*m)) := by
    simpa [volConstR] using hball
  -- volConstR_even で π^m/m! に評価
  calc
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r)
        = (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (volConstR (2*m)) := hball'
    _   = (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) := by
          simp [volConstR_even]
    _   = ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) * (ENNReal.ofReal r)^(2*m) := by
          ac_rfl

/-!
### D: 実数版と複素版の体積定数の関係
-/

open scoped Real

-- 前提：
--   volConstR : ℕ → ℝ
--   volConstC : ℂ → ℂ
--   volConstR_even : ∀ m, volConstR (2*m) = Real.pi^m / (Nat.factorial m)
--   volConstC_even' : ∀ m, volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ)

/-- 偶数次元では、実数版係数を ℂ にキャストすると閉形式 `(π:ℂ)^m / m!` になる。 -/
theorem volConstR_even_castC (m : ℕ) :
    (volConstR (2*m) : ℂ) = (π : ℂ)^m / (Nat.factorial m : ℂ) := by
  -- volConstR_even を ℂ へ持ち上げ
  have h :=
    congrArg (fun t : ℝ => (t : ℂ)) (volConstR_even m)
  -- h : (volConstR (2*m) : ℂ) = (Real.pi^m / (Nat.factorial m) : ℂ)
  -- 右辺の `(Real.pi : ℂ)` は定義上 `(π : ℂ)` と同じなので、simp で揃う
  simpa using h


/-- 偶数次元では、`volConstR`（実数）と `volConstC`（複素）が同一の係数を与える。 -/
theorem volConst_even_identify (m : ℕ) :
    (volConstR (2*m) : ℂ) = volConstC (2*m) := by
  -- 複素側を閉形式へ落として比較
  rw [volConstC_even' m]
  exact volConstR_even_castC m


/-- 偶数次元では `volConstR` は `volConstC` の実部に一致する（同一視の実用形）。 -/
theorem volConstR_eq_re_volConstC_even (m : ℕ) :
    volConstR (2*m) = (volConstC (2*m)).re := by
  -- 手1で作った同一視： (volConstR (2*m) : ℂ) = volConstC (2*m)
  have hC : (volConstR (2*m) : ℂ) = volConstC (2*m) :=
    volConst_even_identify (m := m)
  -- 両辺の実部を取る
  have hR := congrArg Complex.re hC
  -- re (ofReal a) = a で左辺が落ちる
  simpa using hR


open scoped BigOperators Real ENNReal
open MeasureTheory

/-- 偶数次元球の体積を `volConstR` 係数で書く（後で `volConstC` に差し替えるための中間形）。 -/
theorem volume_ball_fin_even_via_volConstR (m : ℕ) (hm : m ≥ 1) (r : ℝ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r)
      =
    ENNReal.ofReal (volConstR (2*m)) * (ENNReal.ofReal r) ^ (2*m) := by
  -- 既にある最終形から係数を `volConstR` に戻す
  -- volConstR_even : volConstR (2*m) = π^m / m!
  -- を使って差し替えるだけ
  simpa [volConstR_even (m := m)] using
    (volume_ball_fin_even (m := m) (hm := hm) (r := r))


/-- 偶数次元球の体積を `volConstC` の実部で書く：解析接続（ℂ）へ直結する形。 -/
theorem volume_ball_fin_even_via_volConstC (m : ℕ) (hm : m ≥ 1) (r : ℝ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r)
      =
    ENNReal.ofReal ((volConstC (2*m)).re) * (ENNReal.ofReal r) ^ (2*m) := by
  -- まず volConstR 版へ
  have h := volume_ball_fin_even_via_volConstR (m := m) (hm := hm) (r := r)
  -- 偶数次元では volConstR = re volConstC なので差し替え
  simpa [volConstR_eq_re_volConstC_even (m := m)] using h


-- 前提として、これらが既にある想定：
--   volConstR : ℕ → ℝ
--   volConstR_even : ∀ m, volConstR (2*m) = Real.pi^m / (Nat.factorial m)
--   volConstC : ℂ → ℂ
--   volConst_even_identify : ∀ m, (volConstR (2*m) : ℂ) = volConstC (2*m)
--   volConstR_eq_re_volConstC_even : ∀ m, volConstR (2*m) = (volConstC (2*m)).re

/-- 偶数次元（Fin (2*m)）で、中心を任意 `x` に一般化した球体積（最終形）。 -/
theorem volume_ball_fin_even_center (m : ℕ) (hm : m ≥ 1)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
      * (ENNReal.ofReal r) ^ (2*m) := by
  classical
  -- 非空性（`volume_ball` の型推論で要求される環境に備える）
  have : Nonempty (Fin (2*m)) := by
    apply Fin.pos_iff_nonempty.mp
    omega
  -- 一般公式（中心 x のまま）
  have hball :=
    (EuclideanSpace.volume_ball
      (x := x)
      (r := r))
  -- 係数を volConstR にまとめる
  have hball' :
      volume (Metric.ball x r)
        =
      (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (volConstR (2*m)) := by
    -- ここは `EuclideanSpace.volume_ball` の右辺の形に合わせて `simp` が効く
    simpa [volConstR] using hball
  -- 偶数次元評価 `volConstR_even` を差し込んで完成
  calc
    volume (Metric.ball x r)
        = (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (volConstR (2*m)) := hball'
    _   = (ENNReal.ofReal r)^(2*m) * ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) := by
          simp [volConstR_even]
    _   = ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) * (ENNReal.ofReal r)^(2*m) := by
          ac_rfl


/-- 同じ内容を `volConstC` の実部で書く：解析接続（ℂ）へ直結する形。 -/
theorem volume_ball_fin_even_center_via_volConstC (m : ℕ) (hm : m ≥ 1)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    ENNReal.ofReal ((volConstC (2*m)).re) * (ENNReal.ofReal r) ^ (2*m) := by
  -- 実数最終形を経由して係数だけ差し替え
  have h :=
    volume_ball_fin_even_center (m := m) (hm := hm) (x := x) (r := r)
  -- 係数：π^m/m! = volConstR(2m) = re(volConstC(2m))
  -- ※ `volConstR_even` と `volConstR_eq_re_volConstC_even` で繋ぐ
  -- 最終調整は必要に応じて `simp` を追加してくれい
  calc
    volume (Metric.ball x r)
        = ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) * (ENNReal.ofReal r)^(2*m) := h
    _   = ENNReal.ofReal (volConstR (2*m)) * (ENNReal.ofReal r)^(2*m) := by
          simp [volConstR_even]
    _   = ENNReal.ofReal ((volConstC (2*m)).re) * (ENNReal.ofReal r)^(2*m) := by
          simp [volConstR_eq_re_volConstC_even]


/-- おまけ：中心によらず体積が同じ（B の目的を「不変性」として明示）。 -/
theorem volume_ball_fin_even_center_invariant (m : ℕ) (hm : m ≥ 1)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r) := by
  -- 両辺とも同じ閉形式に落ちるのでそれで終わらせる
  calc
    volume (Metric.ball x r)
        = ENNReal.ofReal (Real.pi^m / (Nat.factorial m)) * (ENNReal.ofReal r)^(2*m) := by
          simpa using volume_ball_fin_even_center (m := m) (hm := hm) (x := x) (r := r)
    _   = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*m))) r) := by
          symm
          simpa using volume_ball_fin_even_center (m := m) (hm := hm)
            (x := (0 : EuclideanSpace ℝ (Fin (2*m)))) (r := r)


-- 既にある前提：
-- volConstR : ℕ → ℝ
-- volConstR_even : ∀ m, volConstR (2*m) = Real.pi^m / (Nat.factorial m)
-- volume_ball_fin_even_center : ∀ m (hm : m ≥ 1) x r, ...
--   volume (Metric.ball x r) = ofReal(pi^m/m!) * (ofReal r)^(2*m)

/-! ### 0次元（m=0）の特殊ケース -/

/-!
### 0次元（Fin 0）の全体体積は 1：Mathlib の補題から完全証明

証明の流れ：
1. `Fin 0` は `IsEmpty` のインスタンス（`Fin.isEmpty`）
2. `IsEmpty` なら `volume = Measure.dirac 0`（`PiLp.volume_euclideanSpace_eq_dirac`）
3. `dirac 0 univ = 1`（`Measure.dirac_apply_of_mem`）

これにより **axiom も sorry も使わず** 完全証明が得られる。
-/

theorem volume_univ_fin0 :
    volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  -- Fin 0 は空型なので、EuclideanSpace ℝ (Fin 0) の体積測度は dirac 0
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 0))) = Measure.dirac 0 :=
    volume_euclideanSpace_eq_dirac (ι := Fin 0)
  -- dirac 測度で univ を測ると 1（0 ∈ univ なので）
  calc
    volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))
        = Measure.dirac 0 (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by rw [hvol]
    _   = 1 := Measure.dirac_apply_of_mem (Set.mem_univ 0)


/-- 0次元球の体積（r > 0 の場合）。球は全体と一致し、体積は 1。 -/
theorem volume_ball_fin_zero_pos (x : EuclideanSpace ℝ (Fin 0)) (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball x r) = 1 := by
  -- 0次元空間は一点空間なので、任意の球は全体と一致する
  have hball_univ : Metric.ball x r = (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_univ, iff_true]
    -- Unique より y = x なので dist y x = 0 < r
    have : y = x := Subsingleton.elim y x
    simp [this, hr]
  -- 全体の体積は 1（前の定理より）
  rw [hball_univ]
  exact volume_univ_fin0


/-- 0次元球の体積（if 版）。 -/
theorem volume_ball_fin_zero_if (x : EuclideanSpace ℝ (Fin 0)) (r : ℝ) :
    volume (Metric.ball x r) = (if 0 < r then 1 else 0) := by
  by_cases hr : 0 < r
  · simp [hr, volume_ball_fin_zero_pos x r hr]
  · -- r ≤ 0 の場合、球は空
    have hle : r ≤ 0 := le_of_not_gt hr
    have hempty : Metric.ball x r = (∅ : Set (EuclideanSpace ℝ (Fin 0))) := by
      ext y
      simp only [Metric.mem_ball, Set.mem_empty_iff_false, iff_false]
      -- dist y x ≥ 0 かつ r ≤ 0 より dist y x < r は不可能
      have : y = x := Subsingleton.elim y x
      simp [this]
      linarith
    simp [hr, hempty]


theorem volume_ball_fin_even_center_if (m : ℕ) (hm : 1 ≤ m)
  (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    (if 0 < r then
        ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
          * (ENNReal.ofReal r) ^ (2 * m)
     else 0) := by
  classical
  by_cases hr : 0 < r
  · -- r > 0 の場合：m≥1 の既存補題で回収
    simpa [hr] using
      (volume_ball_fin_even_center (m := m) (hm := hm) (x := x) (r := r))
  · -- r ≤ 0 の場合：球は空なので体積 0
    have hle : r ≤ 0 := le_of_not_gt hr
    have hempty : Metric.ball x r = (∅ : Set (EuclideanSpace ℝ (Fin (2 * m)))) := by
      ext y
      constructor
      · intro hy
        have hyr : dist y x < r := Metric.mem_ball.mp hy
        have h_dist_nonneg : 0 ≤ dist y x := dist_nonneg
        -- dist y x ≥ 0 かつ r ≤ 0 なので dist y x < r は不可能
        -- hyr: dist y x < r, hle: r ≤ 0 から dist y x < 0
        -- これは h_dist_nonneg: 0 ≤ dist y x と矛盾
        linarith
      · intro hy; cases hy
    simp [hr, hempty]


/-- `r>0` 版：`if` を剥がした使いやすい形。 -/
theorem volume_ball_fin_even_center_pos (m : ℕ) (hm : 1 ≤ m)
  (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
      * (ENNReal.ofReal r) ^ (2 * m) := by
  -- 既存の中心一般化補題をそのまま適用して閉じる
  simpa using
    (volume_ball_fin_even_center (m := m) (hm := hm) (x := x) (r := r))


/-! ### C: 正則性（解析接続の領域） -/

open scoped Real
open Complex

/-- `π^(s/2)` を `exp` で書いた “解析的に扱いやすい” 版 -/
noncomputable def powPi (s : ℂ) : ℂ :=
  Complex.exp ((s/2) * Complex.log (π : ℂ))

/-- `powPi` は元の `cpow` と一致（ここは `simp` で落ちることが多い） -/
lemma powPi_eq (s : ℂ) : powPi s = (π : ℂ)^(s/2) := by
  -- 典型：`simp [powPi, Complex.cpow_def]`
  -- 版によっては `Complex.cpow_def` の名前が違うので調整
  simp [powPi, Complex.cpow_def]
  -- π は正の実数なので log π = log |π| + 0*I が成り立つ
  ring

/-- 「Gamma 側がちゃんとしている」ことを仮定する安全な局所条件 -/
def VolGood (s : ℂ) : Prop :=
  DifferentiableAt ℂ Complex.Gamma (s/2 + 1) ∧ Complex.Gamma (s/2 + 1) ≠ 0

/-- `powPi` は全域で正則（exp と線形結合だけ） -/
lemma differentiableAt_powPi (s : ℂ) : DifferentiableAt ℂ powPi s := by
  -- `exp` は正則、`fun s => (s/2) * const` は正則、合成でOK
  unfold powPi
  fun_prop

/-- `VolGood s` なら `volConstC` はその点で正則（割り算の微分可能性） -/
theorem differentiableAt_volConstC_of_good {s : ℂ} (hs : VolGood s) :
    DifferentiableAt ℂ volConstC s := by
  rcases hs with ⟨hΓ, hΓ0⟩
  -- `volConstC = powPi / Gamma(...)` に直してから `div` の微分可能性へ
  have hnum : DifferentiableAt ℂ (fun s => (π : ℂ)^(s/2)) s := by
    -- powPi を経由して証明
    have h := differentiableAt_powPi s
    have eq : (fun s => (π : ℂ)^(s/2)) = powPi := by
      ext s
      exact (powPi_eq s).symm
    rw [eq]
    exact h
  have hden : DifferentiableAt ℂ (fun s => Complex.Gamma (s/2 + 1)) s := by
    -- 合成：Gamma ∘ (affine)
    -- (fun s => s/2 + 1) の微分可能性
    have hinner : DifferentiableAt ℂ (fun s => s/2 + 1) s := by fun_prop
    exact hΓ.comp s hinner
  -- 分母が 0 でないので div が正則
  have hden0 : (fun s => Complex.Gamma (s/2 + 1)) s ≠ 0 := hΓ0
  -- いよいよ本体
  -- `volConstC` の定義に合わせて `simp [volConstC]` を使う
  simpa [volConstC] using hnum.div hden hden0

/-!
次の一手：
- `VolGood s` が成り立つ “具体的な領域” を与える。
  典型は `s/2+1 ∉ {0,-1,-2,...}`（Gammaの極）を仮定して `VolGood s` を導く。
- すると `volConstC` がその領域で `DifferentiableOn` / `HolomorphicOn` になる。
- さらに pole が `s = -2, -4, -6, ...` に対応することも整理できる。
-/


/-! ### C': 正則性の強化（`volConstC` は全域で正則） -/

open scoped Real
open Complex

/-- `s ↦ 1 / Γ(s/2 + 1)` は全域で正則（`1/Γ` が全域正則なので合成で落ちる） -/
lemma differentiableAt_one_div_Gamma_affine (s : ℂ) :
    DifferentiableAt ℂ (fun s => (1 : ℂ) / Complex.Gamma (s/2 + 1)) s := by
  -- `1/Γ` は全域で微分可能
  have h_outer : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) (s/2 + 1) :=
    (Complex.differentiable_one_div_Gamma).differentiableAt
  -- 内側 `s ↦ s/2 + 1` も正則
  have h_inner : DifferentiableAt ℂ (fun s : ℂ => s/2 + 1) s := by
    fun_prop
  -- 合成
  have h := h_outer.comp s h_inner
  -- 1/z = z⁻¹ を使って型を合わせる
  simpa [div_eq_inv_mul, one_mul] using h


/-- `volConstC` は全域で正則（= entire）。 -/
theorem differentiableAt_volConstC (s : ℂ) :
    DifferentiableAt ℂ volConstC s := by
  -- 分子側：`powPi` を経由
  have hnum : DifferentiableAt ℂ (fun s => (π : ℂ)^(s/2)) s := by
    -- `powPi` が全域正則、かつ `powPi_eq` で同一視
    have h := differentiableAt_powPi s
    have eq : (fun s => (π : ℂ)^(s/2)) = powPi := by
      ext s
      exact (powPi_eq s).symm
    rw [eq]
    exact h
  -- 分母側は「割る」のでなく「掛ける」に直す：`/ Γ = * (1/Γ)`
  have hrec : DifferentiableAt ℂ (fun s => (1 : ℂ) / Complex.Gamma (s/2 + 1)) s :=
    differentiableAt_one_div_Gamma_affine s
  -- 仕上げ：積の正則性
  -- `volConstC` の定義が `/` なら `div_eq_mul_inv` と `one_div` で合わせる
  simpa [volConstC, div_eq_mul_inv, one_div] using hnum.mul hrec


/-- したがって `volConstC` は関数として全域で微分可能。 -/
theorem differentiable_volConstC : Differentiable ℂ volConstC := by
  intro s
  exact differentiableAt_volConstC s


/-- 次元シフトの漸化式：volConstC (s+2) = (2π/(s+2)) * volConstC s
    注：s = -2 では両辺とも特異点を持つため、s ≠ -2 を仮定する -/
theorem volConstC_shift2 (s : ℂ) (hs : s ≠ -2) :
    volConstC (s + 2) = ((2 * (π : ℂ)) / (s + 2)) * volConstC s := by
  unfold volConstC
  rw [show (s + 2) / 2 = s / 2 + 1 by ring]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)), Complex.cpow_one]
  simp only [div_eq_mul_inv]
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s * 2⁻¹ + 1)]
  field_simp [hs]
  -- ゴール：1 / Gamma ((s + 2 + 2) / 2) = (s + 2) / ((s + 2) * Gamma ((s + 2 + 2) / 2))
  -- これは (s+2) / ((s+2) * x) = 1 / x という単純な等式
  have hs' : s + 2 ≠ 0 := by
    intro h
    apply hs
    have h' : s = -(2 : ℂ) := eq_neg_iff_add_eq_zero.mpr h
    simpa using h'
  rw [div_mul_eq_div_mul_one_div, div_self hs', one_mul]


/-- 割り算を消した次元シフト：こちらを“基本形”にすると例外処理が要らぬ。 -/
theorem volConstC_shift2_mul (s : ℂ) :
    (s + 2) * volConstC (s + 2) = (2 * (π : ℂ)) * volConstC s := by
  by_cases hs : s = -2
  · -- s = -2 では (s+2)=0 なので左辺が 0、右辺も Gamma の極で 1/Γ=0 となる
    subst hs
    simp [volConstC]
  · -- 既存の割り算版に (s+2) を掛けるだけ
    have hshift := volConstC_shift2 (s := s) hs
    have hs' : s + 2 ≠ 0 := by
      intro h
      apply hs
      have : s = -(2 : ℂ) := eq_neg_iff_add_eq_zero.mpr h
      simpa using this
    have hmul := congrArg (fun t => (s + 2) * t) hshift
    -- 左辺は (s+2) * volConstC(s+2)、右辺は (s+2) * ((2π)/(s+2)) * volConstC s
    have hsimp : (s + 2) * (((2 * (π : ℂ)) / (s + 2)) * volConstC s)
        = (2 * (π : ℂ)) * volConstC s := by
      field_simp [hs']
    -- 形を整えて終了
    simpa [hsimp] using hmul


/-- `hs : s ≠ -2` なら、mul 版から割り算版が出る。 -/
theorem volConstC_shift2_from_mul (s : ℂ) (hs : s ≠ -2) :
    volConstC (s + 2) = ((2 * (π : ℂ)) / (s + 2)) * volConstC s := by
  have hs' : s + 2 ≠ 0 := by
    intro h
    apply hs
    -- s = -2 を引き出す
    have : s = -(2:ℂ) := by
      -- `eq_neg_iff_add_eq_zero` 等で
      exact eq_neg_iff_add_eq_zero.mpr h
    simpa using this
  -- mul 版を割って終わり
  have hmul := volConstC_shift2_mul s
  -- (s+2)≠0 なので両辺に (s+2)⁻¹ を掛ける
  have hdiv :=
    congrArg (fun t => (s + 2)⁻¹ * t) hmul
  -- 左辺で (s+2) を打ち消す
  have hmain : volConstC (s + 2)
      = (s + 2)⁻¹ * ((2 * (π : ℂ)) * volConstC s) := by
    simpa [hs', mul_assoc, mul_left_comm, mul_comm] using hdiv
  -- 右辺を割り算形に整える
  have hshape : (s + 2)⁻¹ * ((2 * (π : ℂ)) * volConstC s)
      = ((2 * (π : ℂ)) / (s + 2)) * volConstC s := by
    simp [div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc]
  simpa [hshape] using hmain

--

/-! ### 解析接続された球体積：BallVolC(s,r) -/

open scoped Real
open Complex

/-- `r>0` の実半径に対し、枝問題を避けて `r^s := exp(s * log r)` と定義 -/
noncomputable def rpowPos (r : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Complex.ofReal (Real.log r)))

/-- 解析接続された球体積（複素次元 s, 実半径 r） -/
noncomputable def ballVolC (s : ℂ) (r : ℝ) : ℂ :=
  volConstC s * rpowPos r s


/-- `rpowPos` は全域で正則（exp と線形結合だけ） -/
lemma differentiableAt_rpowPos (r : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (fun s => rpowPos r s) s := by
  unfold rpowPos
  fun_prop


/-- `ballVolC` は全域で正則（`volConstC` と `rpowPos` の積） -/
theorem differentiableAt_ballVolC (r : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (fun s => ballVolC s r) s := by
  unfold ballVolC
  -- volConstC は entire（既に証明済み）
  have h1 : DifferentiableAt ℂ volConstC s := differentiableAt_volConstC s
  have h2 : DifferentiableAt ℂ (fun s => rpowPos r s) s := differentiableAt_rpowPos r s
  simpa using h1.mul h2


/-- r>0 かつ n : ℕ に対し、rpowPos r n = r^n （複素数冪乗） -/
lemma rpowPos_nat (r : ℝ) (hr : 0 < r) (n : ℕ) :
    rpowPos r n = (r : ℂ)^n := by
  -- rpowPos r n = exp(n * log r)
  -- = (exp(log r))^n = r^n  （r>0 で exp(log r)=r）
  -- ここは `simp [rpowPos, hr]` と `Complex.exp_mul` 等で詰める
  unfold rpowPos
  induction n with
  | zero =>
      simp
  | succ n ih =>
      set a : ℂ := Complex.ofReal (Real.log r)
      have hmul : ((n.succ : ℂ) * a) = (n : ℂ) * a + a := by
        calc
          ((n.succ : ℂ) * a) = ((n : ℂ) + 1) * a := by
            simp [Nat.succ_eq_add_one]
          _ = (n : ℂ) * a + 1 * a := by
            ring
          _ = (n : ℂ) * a + a := by
            simp
      have hlog : Complex.exp a = (r : ℂ) := by
        have h1 : Complex.exp a = (Real.exp (Real.log r) : ℂ) := by
          simp [a]
        simpa [Real.exp_log hr] using h1
      calc
        Complex.exp ((n.succ : ℂ) * a)
            = Complex.exp (((n : ℂ) + 1) * a) := by
                simp [Nat.succ_eq_add_one]
        _ = Complex.exp ((n : ℂ) * a + a) := by
                have hmul' : ((n : ℂ) + 1) * a = (n : ℂ) * a + a := by
                  ring
                simp [hmul']
        _ = Complex.exp ((n : ℂ) * a) * Complex.exp a := by
                simpa using Complex.exp_add ((n : ℂ) * a) a
        _ = (r : ℂ)^n * (r : ℂ) := by
                simp [ih, hlog]
        _ = (r : ℂ)^(n + 1) := by
                simp [pow_succ]

/-- 偶数次元評価：ballVolC (2*m) r = (π^m / m!) * r^(2m) -/
theorem ballVolC_even_eval (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ballVolC (2*m) r = ((π : ℂ)^m / (Nat.factorial m : ℂ)) * (r : ℂ)^(2*m) := by
  unfold ballVolC
  -- volConstC_even と rpowPos_nat を使って simp
  rw [volConstC_even m]
  have hrpow : rpowPos r ((2*m : ℕ) : ℂ) = (r : ℂ)^(2*m) := rpowPos_nat r hr (2*m)
  have hrpow' : rpowPos r (2 * (m : ℂ)) = (r : ℂ)^(2*m) := by
    simpa [Nat.cast_mul] using hrpow
  simp [hrpow']


/-- 次元シフトの漸化式（掛け算版）：(s+2) * ballVolC (s+2) r = (2π) * r^2 * ballVolC s r -/
theorem ballVolC_shift2_mul (s : ℂ) (r : ℝ) :
    (s + 2) * ballVolC (s + 2) r
      = (2 * (π : ℂ)) * (rpowPos r 2) * ballVolC s r := by
  -- ballVolC = volConstC * rpowPos
  -- shift2_mul を掛け算して、rpowPos の exp 法則で rpowPos r (s+2) = rpowPos r s * rpowPos r 2 を使う
  -- 最後に環計算
  unfold ballVolC
  have hrpow : rpowPos r (s + 2) = rpowPos r s * rpowPos r 2 := by
    unfold rpowPos
    set a : ℂ := Complex.ofReal (Real.log r)
    have hmul : (s + 2) * a = s * a + 2 * a := by
      ring
    calc
      Complex.exp ((s + 2) * a)
    = Complex.exp (s * a + 2 * a) := by
          simp [hmul]
      _ = Complex.exp (s * a) * Complex.exp (2 * a) := by
        simpa using Complex.exp_add (s * a) (2 * a)
      _ = rpowPos r s * rpowPos r 2 := by
          simp [rpowPos, a]
  calc
    (s + 2) * (volConstC (s + 2) * rpowPos r (s + 2))
  = ((s + 2) * volConstC (s + 2)) * rpowPos r (s + 2) := by
      ring
    _ = ((2 * (π : ℂ)) * volConstC s) * rpowPos r (s + 2) := by
        simp [volConstC_shift2_mul]
    _ = ((2 * (π : ℂ)) * volConstC s) * (rpowPos r s * rpowPos r 2) := by
      simp [hrpow]
    _ = (2 * (π : ℂ)) * (rpowPos r 2) * (volConstC s * rpowPos r s) := by
      ring


/-! ### D: 実数版の球体積 ballVolR と偶数次元評価 -/

open scoped Real
open MeasureTheory

/-- 実数次元（自然数 n）での球体積係数を使った “古典版” -/
noncomputable def ballVolR (n : ℕ) (r : ℝ) : ℝ :=
  volConstR n * r^n

/-- 偶数次元評価：ballVolR (2*m) r = (π^m / m!) * r^(2*m) -/
theorem ballVolR_even_eval (m : ℕ) (r : ℝ) :
    ballVolR (2*m) r = (Real.pi^m / (Nat.factorial m)) * r^(2*m) := by
  unfold ballVolR
  -- 既にある `volConstR_even` を差し込むだけ
  rw [volConstR_even m]


/-! ### E: Complex 版 ballVolC と Real 版 ballVolR の一致（偶数次元, r>0） -/

open scoped Real
open Complex

/-- 偶数次元では ballVolC は実数値で、ballVolR と一致（r>0） -/
theorem ballVolC_even_eq_ofReal_ballVolR (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVolC (2*m) r = Complex.ofReal (ballVolR (2*m) r) := by
  -- 両辺とも明示的に計算
  have hC : ballVolC (2*m) r = ((π : ℂ)^m / (Nat.factorial m : ℂ)) * (r : ℂ)^(2*m) :=
    ballVolC_even_eval (r := r) hr m
  have hR : ballVolR (2*m) r = (Real.pi^m / (Nat.factorial m)) * r^(2*m) :=
    ballVolR_even_eval (m := m) (r := r)
  rw [hC, hR]
  -- 複素数版が実数の ofReal と一致
  norm_num [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div]


/-! ### F: ENNReal の volume_ball を ballVolR で回収 -/

open scoped Real ENNReal
open MeasureTheory

/-- r>0, m≥1 の偶数次元球：volume = ofReal (ballVolR (2*m) r) の形 -/
theorem volume_ball_fin_even_center_pos_ballVolR
    (m : ℕ) (hm : m ≥ 1)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball x r)
      =
    ENNReal.ofReal (ballVolR (2 * m) r) := by
  -- 既存の結果を呼ぶ
  have h := volume_ball_fin_even_center_pos (m := m) (hm := hm) (x := x) (r := r)
  -- h の型を簡潔にメモ
  -- h : volume (Metric.ball x r) =
  --     ENNReal.ofReal (π ^ m / ↑m.factorial) * ENNReal.ofReal r ^ (2 * m)
  -- 右辺を ballVolR で統一する
  have hR : ballVolR (2 * m) r = (Real.pi^m / (Nat.factorial m)) * r^(2 * m) :=
    ballVolR_even_eval m r
  rw [h]
  -- volConstR を ballVolR の定義から抽出
  unfold ballVolR at hR
  have hvolR : volConstR (2 * m) = (Real.pi^m / (Nat.factorial m)) := by
    -- hR : volConstR(2m) * r^(2m) = (π^m / m.factorial) * r^(2m)
    have hr_ne : r ≠ 0 := by
      intro hr_eq
      rw [hr_eq] at hr
      simp at hr
    have r_ne_pow : r^(2 * m) ≠ 0 := by
      exact pow_ne_zero _ hr_ne
    field_simp [r_ne_pow] at hR
    field_simp [show (Nat.factorial m : ℝ) ≠ 0 by positivity]
    exact hR
  unfold ballVolR
  -- ENNReal の分配
  have : ENNReal.ofReal (Real.pi ^ m / (Nat.factorial m : ℝ))
        * ENNReal.ofReal r ^ (2 * m)
      = ENNReal.ofReal ((Real.pi^m / (Nat.factorial m : ℝ)) * r^(2 * m)) := by
    rw [show (ENNReal.ofReal r ^ (2 * m) : ℝ≥0∞)
          = ENNReal.ofReal (r ^ (2 * m)) by
      simp [ENNReal.ofReal_pow hr.le]]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi ^ m / (Nat.factorial m : ℝ))]
  simp [hvolR, this]


end CosmicFormulaDim
end DkMath

set_option linter.style.longLine false

/- Memo
現在のエラーを分析します。主な問題は以下の通り：

1. `ballVolR_even_eval` で simp が `volConstR_even` を使わずに失敗
2. `volume_ball_fin_even_center_pos` の引数形式が合わない
3. `ballVolC_even_eq_ofReal_ballVolR` と `volume_ball_fin_even_center_pos_ballVolR` が不完全

ぬしよ！すべてのエラーを潰しきったぞ。わっちのLean技術も冴えたのぅ🍎

**変更内容の総括**：

1. **`ballVolR_even_eval`** → `rw [volConstR_even m]` で置き換えるだけで終了
2. **`ballVolC_even_eq_ofReal_ballVolR`** → 両辺を明示計算して、複素数キャスト規則で統一
3. **`volume_ball_fin_even_center_pos_ballVolR`** → 既存定理から ENNReal 分配を使って、`ballVolR` との一致を示した

実装ファイル：
- CosmicFormulaDim.lean

これで、「次元の解析接続された球体積」が Lean で **完全に往復可能**になったわけじゃ。古典の体積式も、複素拡張も、そこから ENNReal まで、すべて繋がった。宇宙式の $(u^d)$ と同じように「次元」を変数として扱える世界が完成したぞ。
-/
