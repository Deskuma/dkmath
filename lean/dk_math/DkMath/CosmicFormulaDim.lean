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

/-- 0次元 EuclideanSpace の全空間の体積は 1。 -/
theorem volume_univ_fin0 :
    volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  classical
  haveI : IsEmpty (Fin 0) := ⟨fun x => Fin.elim0 x⟩
  haveI : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
  -- 0次元では Subsingleton より Haar 測度が正規化されて volume univ = 1 になる
  -- Subsingleton な空間では任意の集合の測度が 0 または 1 になり、univ は 1
  have : (volume : Measure (EuclideanSpace ℝ (Fin 0))) Set.univ = 1 := by
    simp [MeasureTheory.measure_univ]
  exact this


theorem volume_ball_fin_even_center_if (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) :
    volume (Metric.ball x r)
      =
    (if 0 < r then
        ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
          * (ENNReal.ofReal r) ^ (2 * m)
     else 0) := by
  classical
  by_cases hr : 0 < r
  · -- r > 0 の場合：m=0 と m≥1 を分岐して回収
    by_cases hm0 : m = 0
    · -- m=0（0次元）ケース：空添字だが空間は一点、球 = univ、体積 = 1
      subst hm0
      -- 添字が空型であることを明示し、空間が Subsingleton であることを使う
      haveI : IsEmpty (Fin (2 * 0)) := ⟨fun x => Fin.elim0 x⟩
      have hball_univ :
          Metric.ball x r
            = (Set.univ : Set (EuclideanSpace ℝ (Fin (2 * 0)))) := by
        ext y
        constructor
        · intro _; trivial
        · intro _
          -- Subsingleton なので任意の y は x に等しい → 距離 0 → 0 < r より ball に入る
          have hyx : y = x := Subsingleton.elim y x
          have hdist : dist y x = 0 := by simp [hyx]
          -- `Metric.mem_ball` で書き換えて示す
          simpa [Metric.mem_ball, hdist] using hr
      -- 体積：univ の測度は 1、かつ右辺の係数も 1
      have hx : (ENNReal.ofReal r) ^ (2 * 0) = 1 := by simp
      have hcoef : ENNReal.ofReal (Real.pi ^ 0 / Nat.factorial 0) = 1 := by simp
      have hvol_one : volume (Metric.ball x r) = 1 := by
        -- ball = univ なので、その体積は 1
        have h_univ : volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := volume_univ_fin0
        simpa [hball_univ] using h_univ
      have :
          volume (Metric.ball x r)
            = ENNReal.ofReal (Real.pi ^ 0 / Nat.factorial 0)
              * (ENNReal.ofReal r) ^ (2 * 0) := by
        simpa [hcoef, hx] using hvol_one
      -- if を剥がした目標へ
      simpa [hr] using this
    · -- m≥1 ケース：既に作った中心一般化補題を使う
      have hm1 : m ≥ 1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
      simpa [hr] using
        (volume_ball_fin_even_center (m := m) (hm := hm1) (x := x) (r := r))
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
theorem volume_ball_fin_even_center_pos (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (2 * m))) (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball x r)
      =
    ENNReal.ofReal (Real.pi^m / (Nat.factorial m))
      * (ENNReal.ofReal r) ^ (2 * m) := by
  simp [volume_ball_fin_even_center_if, hr]


end CosmicFormulaDim
end DkMath

set_option linter.style.longLine false

/- Memo
了解。この賢狼、状況を整理してから手を入れるぞ。

- 方針
  - 問題の根は m=0（0次元）分岐にある。`EuclideanSpace.volume_ball` が型クラスとして `Nonempty (Fin (2*m))` を要求しており、m=0 では `Fin 0` が空型のため適用できない。
  - ぬしの見立て（0次元は一点空間で球の体積は 1）という数学的直感は正しい。ただし Lean の当該定理は 0次元に対して定義されておらぬため、直接の適用ができんのじゃ。
  - 解消策は「m=0 専用の処理を、`EuclideanSpace.volume_ball` を使わずに証明する」か「定理の適用範囲を m≥1 に限定する」かの二択だの。

- 今回の作業
  - m=0 ブランチで `EuclideanSpace.volume_ball` を使わず、空添字から `Subsingleton` を用いて球＝全体（`univ`）であることを示し、体積 1 に落とす証明を試みた。
  - しかし Mathlib 側の `volume` の 0次元既定値（`volume univ = 1`）を `simp` で引けるはずという読みがこの環境では通らず、`volume_univ_fin0` の補題も成立しなかった（`volume Set.univ = 1` を `simp` で閉じられない）。

- 重要な論点
  - 矛盾は「ない」。定理の適用可能性（型クラス制約）が 0次元では満たされないのが本質。つまり「実装上の前提不足」による証明不能じゃ。
  - ぬしが提示した「一般公式で閉じる」案は、`EuclideanSpace.volume_ball` の Nonempty 仮定がある限り Lean では m=0 に適用できない。

提案（次の一手）：
- その1（安全・最小修正）: 定理 `volume_ball_fin_even_center_if` を m≥1 に限定する。m=0 は別補題で扱う。例：
  - `theorem volume_ball_fin_even_center_if (m : ℕ) (hm : 1 ≤ m) …` に変更し、今の m≥1 分岐のみで閉じる。
  - 別途 `theorem volume_ball_fin_zero_pos … : volume (Metric.ball x r) = 1`（r>0）を用意し、こちらは `Subsingleton` と 0次元 Haar/volume の既定値を使う。必要なら Mathlib の補題名を探索して結ぶ。
- その2（補題追加で 0次元を閉じる）: このファイルに 0次元の `volume` の性質を明示的に証明する補題を足す。例えば
  - `Subsingleton (EuclideanSpace ℝ (Fin 0))` から `Metric.ball x r = Set.univ`（r>0）を示す。
  - `volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) = 1` を証明する補助補題（Haar/volume の定義から）。これは Mathlib の既存補題に当たるはずなので、適切な import と補題名が必要。
  - この上で `ENNReal.ofReal (Real.pi^0 / Nat.factorial 0) = 1`、`(ENNReal.ofReal r)^0 = 1` で右辺を 1 に整える。

今のファイルには 0次元の `volume univ = 1` を引き出す決定的な補題名が足りず、ここでこれ以上は進められん。上記の「その1」で API を分けるか、「その2」で必要な補題を特定して import するのが良い。ぬしはどちらを望むかの？

- 追加でできること
  - その2を選ぶなら、Mathlib の `MeasureTheory` 周辺を参照して `volume_univ` の 0次元版の補題名を探索して取り込む。たとえば `Measure.instHaarMeasure` 系の補題から `volume` の 0次元正規化を引ける。
  - その1を選ぶなら、m=0 ケースの等式を別定理としてまとめ、呼び出し側で分岐する形に揃える。

どうするか選んでくりゃれ。わっちは続けて手を入れる準備はできておるぞ。
-/
