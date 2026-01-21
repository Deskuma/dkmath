# DkMath.RH：位相ドリフト骨格（Lean4 + mathlib4）＋ EulerZeta（magnitude/phase）

- Authors: D. and Kenro (ChatGPT-5.2)
- Last updated: 2026/01/21 15:55

このモジュールは、リーマンゼータ関数そのものに踏み込む前段として、

1) 複素関数の位相（角度）を、枝問題を避けて扱うための骨格  
2) その骨格と相性の良い「位相付き Euler 因子」から作る EulerZeta の無限積を、収束・正値まで固める

ことを目的とします。

キーワードは次の 4 つです。

- トルク（torque）：位相が回ろうとする“分子”
- 位相速度（phaseVel）：`Im((f'(t))/f(t))` として定義される角速度
- アンラップ位相（phaseUnwrap）：位相を積分で連続化したもの（`arg` の枝を避ける）
- EulerZeta（magnitude/phase）：`exp((σ+it)log p)-1` を核にした位相付き因子の無限積

---

## 1. ファイル構成

### 位相ドリフト骨格

- `DkMath/RH/Defs.lean`
- `DkMath/RH/Lemmas.lean`
- `DkMath/RH/Theorems.lean`

### EulerZeta

- `DkMath/RH/EulerZeta.lean`
- `DkMath/RH/EulerZetaLemmas.lean`
- `DkMath/RH/EulerZetaConvergence.lean`

---

## 2. 位相ドリフト骨格（既存成果）

### `Defs.lean`：導入した定義

#### `vertical (σ t : ℝ) : ℂ`

縦線パス `σ + i t`。

#### `torque (z dz : ℂ) : ℝ`  

$$
\mathrm{torque}(z,dz)=\Re(z)\Im(dz)-\Im(z)\Re(dz)
$$

#### `denom (z : ℂ) : ℝ`  

`re^2 + im^2`（`normSq` と一致）。

#### `phaseVel (f : ℝ → ℂ) (t : ℝ) : ℝ`  

$$
\mathrm{phaseVel}(f,t)=\Im\Bigl(\frac{f'(t)}{f(t)}\Bigr)
$$

#### `phaseUnwrap (f) (t0 θ0) (t) : ℝ`  

$$
\Theta(t)=\theta_0+\int_{t_0}^{t}\mathrm{phaseVel}(f,u)\,du
$$

### `Lemmas.lean`：確定した主要補題

#### `denom_eq_normSq`

$$
\mathrm{denom}(z)=\mathrm{normSq}(z)
$$

#### `im_div_eq_torque_div_normSq`

$$
\Im\Bigl(\frac{dz}{z}\Bigr)=\frac{\mathrm{torque}(z,dz)}{\mathrm{normSq}(z)}
$$

#### `driftFreeLocal_iff_im_div_eq_zero`（`z≠0`）

$$
\mathrm{torque}(z,dz)=0\iff\Im(dz/z)=0
$$

#### `torque_eq_im_mul_conj`

$$
\mathrm{torque}(z,dz)=\Im(dz\cdot\overline{z})
$$

#### `phaseVel_eq_torque_div_normSq` / `phaseVel_eq_im_mul_conj_div_normSq`

$$
\mathrm{phaseVel}(f,t)=
\frac{\mathrm{torque}(f(t),f'(t))}{\mathrm{normSq}(f(t))}=
\frac{\Im(f'(t)\cdot\overline{f(t)})}{\mathrm{normSq}(f(t))}
$$

#### `driftFreeAt_iff_phaseVel_eq_zero`（`f t ≠ 0`）

$$
\mathrm{driftFreeAt}(f,t)\iff \mathrm{phaseVel}(f,t)=0
$$

### `Theorems.lean`：アンラップ位相が微分できる

`phaseUnwrap_hasDerivAt`（`Continuous (phaseVel f)` を仮定）

$$
(\mathrm{phaseUnwrap})'(t)=\mathrm{phaseVel}(f,t)
$$

---

## 3. EulerZeta（今回の成果）

ここでは「Euler 因子を位相つきで見直し、magnitude と phase を分けて扱う」ための土台を Lean に固定します。

### 3.1 定義（`EulerZeta.lean` / `EulerZetaLemmas.lean`）

#### 分母の核（複素数）

$$
w(p,\sigma,t)=\exp((\sigma+it)\log p)-1
$$

- `eulerZeta_exp_s_log_p_sub_one (p) (σ t) : ℂ`

#### magnitude 因子（実数）

$$
a_p(\sigma,t)=\frac{\exp(\sigma\log p)}{\|w(p,\sigma,t)\|}
$$

- `eulerZetaFactorMag (p) (σ t) : ℝ`

（`‖w‖` を `sqrt(re^2+im^2)` や `sqrt(normSq)` で書いた版も、同値補題込みで整理済み）

#### EulerZeta magnitude（無限積）

$$
\zeta_e^{mag}(\sigma,t)=\prod_{p\ \mathrm{prime}} a_p(\sigma,t)
$$

- `eulerZetaMag (σ t) : ℝ := ∏' p : {p // Nat.Prime p}, eulerZetaFactorMag p.1 σ t`

#### 収束性の器

- `EulerZetaMagMultipliable (σ t) : Prop := Multipliable (...)`

#### 位相（phase）

$$
\mathrm{phase}(p,\sigma,t)=\arg(w(p,\sigma,t))
$$

- `eulerZetaPhase (p) (σ t) : ℝ`

### 3.2 補題（`EulerZetaLemmas.lean` の中心）

#### `w(p,σ,t) ≠ 0`（`p` prime, `σ>1` などの条件下で確定）

近似評価（収束へ落とす心臓部）

$$
\|a_p(\sigma,t)-1\|\le \frac{2}{p^\sigma}\quad(\sigma>1)
$$

これにより、p-series へ比較して

$$
\sum_p \|a_p(\sigma,t)-1\|
$$

の収束（`Summable`）が取れる。

### 3.3 収束と正値（`EulerZetaConvergence.lean` の主定理）

#### 収束（`Multipliable`）

$$
\sigma>1\Rightarrow \text{EulerZeta magnitude は無限積として収束}
$$

- `eulerZetaMag_multipliable_sigma_gt_one`

#### 正値

$$
\sigma>1\Rightarrow 0<\zeta_e^{mag}(\sigma,t)
$$

- `eulerZetaMag_pos_sigma_gt_one`

証明の流れは一貫して

- $\|a_p-1\|$ を $2/p^\sigma$ で上から押さえる
- $\sum 1/n^\sigma$ の収束へ比較
- 一般定理で `Multipliable` と `tprod` の性質へ落とす

です。

---

## 4. `#print axioms` と `sorryAx`（メモ）

ソース（`.lean`）上に `sorry` が見当たらないのに `#print axioms` に `sorryAx` が出る場合、

- 古い `.olean` が残っている（キャッシュ）
- 依存先の環境に由来する

のどちらかが典型です。

切り分けは `lake clean` と `.lake/build` の再生成が確実です。

なお `propext / Classical.choice / Quot.sound` は、Mathlib を通常運用すると出やすい標準的依存です。

---

## 5. 次の拡張（研究として自然）

- EulerZeta の phase を、`phaseUnwrap` に接続して枝問題なしの連続位相として扱う。
- t 方向だけでなく σ 方向のテンプレート（`phaseVelSigma` / `phaseUnwrapSigma`）を整える。
- ゼータ差し込みのための仮定（零点回避・可微分性・可積分性）を整理して「差し込み条件セット」としてまとめる。

---

GitHub Markdown and $\LaTeX$ Style
This document uses GitHub-flavored Markdown and $\LaTeX$ for mathematical expressions. To render the $\LaTeX$ expressions correctly, ensure that your Markdown viewer supports MathJax or a similar library.
