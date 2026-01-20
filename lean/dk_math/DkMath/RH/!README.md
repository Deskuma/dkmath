# DkMath.RH：位相ドリフト骨格（現状の全コード）

このディレクトリは、リーマンゼータ関数に差し込む前に必要な
「複素関数の位相（角度）の変化＝位相速度」を Lean で扱うための骨格を固めたもの。

重要方針はひとつ：

- `arg`（偏角）を直接扱わず、**位相を積分で定義（アンラップ）**して枝問題を回避する。

---

## ファイル構成（現状）

- `Basic.lean`  
  **空ファイル（予約）**。現状では何も定義していない。
  将来、共通設定や再輸出（re-export）を置く候補。

- `Defs.lean`  
  定義置き場（記号・概念の導入のみ）。

- `Lemmas.lean`  
  定義間の関係を示す補題置き場（代数コア、同値、別表現など）。

- `Theorems.lean`  
  積分で定義した位相が、期待通り微分できること（解析骨格）を示す定理置き場。

---

## `Defs.lean`：導入した定義

### 縦線パス

\[
\mathrm{vertical}(\sigma,t)=\sigma+i t
\]

- `vertical (σ t : ℝ) : ℂ`

### トルク（位相回転の分子）

\[
\mathrm{torque}(z,dz)=\Re(z)\Im(dz)-\Im(z)\Re(dz)
\]

- `torque (z dz : ℂ) : ℝ`

### 分母（normSq）

\[
\mathrm{denom}(z)=\Re(z)^2+\Im(z)^2
\]

- `denom (z : ℂ) : ℝ`

### ドリフト消失（局所）

- `driftFreeLocal (z dz : ℂ) : Prop := torque z dz = 0`

### 位相速度（角速度）

\[
\mathrm{phaseVel}(f,t)=\Im\Bigl(\frac{f'(t)}{f(t)}\Bigr)
\]

- `phaseVel (f : ℝ → ℂ) (t : ℝ) : ℝ`（`deriv` 使用）

### アンラップ位相（積分で定義）

\[
\mathrm{phaseUnwrap}(t)=\theta_0+\int_{t_0}^{t}\mathrm{phaseVel}(f,u)\,du
\]

- `phaseUnwrap (f) (t0 θ0) (t) : ℝ`

### 関数版ドリフト消失

- `driftFreeAt (f : ℝ → ℂ) (t : ℝ) : Prop :=
    driftFreeLocal (f t) (deriv f t)`

---

## `Lemmas.lean`：確定した主要補題（何が「Leanで固まったか」）

### 1. 分母の正体

\[
\mathrm{denom}(z)=\mathrm{normSq}(z)
\]

- `denom_eq_normSq`

### 2. 代数コア：\(\Im(dz/z)\) の展開

\[
\Im\Bigl(\frac{dz}{z}\Bigr)
=\frac{\mathrm{torque}(z,dz)}{\mathrm{normSq}(z)}
\]

- `im_div_eq_torque_div_normSq`

これは「位相速度は \(\Im(f'/f)\)」という骨格を代数として固定する心臓部。

### 3. ドリフト消失の同値（\(z\neq0\)）

\[
\mathrm{torque}(z,dz)=0
\iff
\Im(dz/z)=0
\]

- `driftFreeLocal_iff_im_div_eq_zero`

### 4. トルクの共役表現（mathlib4流）

mathlib4 では共役は `Complex.conj` ではなく、

- `open scoped ComplexConjugate` を開いて `conj z`  
- もしくは `star z`

で扱う。

確定した形：

\[
\mathrm{torque}(z,dz)=\Im(dz\cdot\overline{z})
\]

- `torque_eq_im_mul_conj`（`conj` 記法）

### 5. 位相速度とトルクの接続

\[
\mathrm{phaseVel}(f,t)
=\frac{\mathrm{torque}(f(t),f'(t))}{\mathrm{normSq}(f(t))}
\]

- `phaseVel_eq_torque_div_normSq`

さらに自然な別表現：

\[
\mathrm{phaseVel}(f,t)
=\frac{\Im(f'(t)\cdot\overline{f(t)})}{\mathrm{normSq}(f(t))}
\]

- `phaseVel_eq_im_mul_conj_div_normSq`

### 6. ドリフト消失と位相速度ゼロ（関数版）

\(f(t)\neq0\) のもとで

\[
\mathrm{driftFreeAt}(f,t)\iff \mathrm{phaseVel}(f,t)=0
\]

- `driftFreeAt_iff_phaseVel_eq_zero`

---

## `Theorems.lean`：アンラップ位相が微分できる

### `phaseUnwrap_hasDerivAt`

仮定：`Continuous (phaseVel f)`（位相速度が連続）

結論：

\[
\frac{d}{dt}\Bigl(\theta_0+\int_{t_0}^{t}\mathrm{phaseVel}(f,u)\,du\Bigr)
=\mathrm{phaseVel}(f,t)
\]

つまり、**積分定義の位相（アンラップ位相）が、期待通りの導関数を持つ**ことを Lean 上で固定した。

---

## この段階の到達点（短く）

- 位相速度 \(\Im(f'/f)\) を、`torque / normSq` として代数的に扱えるようにした。
- 「ドリフト消失」は「位相速度ゼロ」と同値になった（零点回避 \(f(t)\neq0\) を条件に）。
- `arg` を使わず、位相を積分で定義した上で、微分が正しく戻ることを示した。

---

## 次にやると自然な拡張（予定メモ）

- σ方向（横方向）でも同じテンプレ：`phaseVelSigma` / `phaseUnwrapSigma` を作る。
- ゼータ差し込みに必要な条件（零点回避、可微分性など）を整理して仮定としてまとめる。
- 最終的に \(\Delta_\sigma(T)\) の積分表示へ合流する。
