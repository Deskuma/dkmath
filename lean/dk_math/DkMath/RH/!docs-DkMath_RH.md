# DkMath.RH：位相ドリフト骨格（Lean4 + mathlib4）

このモジュールは、リーマンゼータ関数そのものに踏み込む前段として、  
「複素関数の位相（角度）を、枝問題を避けて扱うための骨格」を Lean で固めたものです。

キーワードは次の 3 つです。

- **トルク（torque）**：位相が回ろうとする“分子”
- **位相速度（phaseVel）**：\(\Im\bigl((f'(t))/f(t)\bigr)\) として定義される角速度
- **アンラップ位相（phaseUnwrap）**：位相を積分で連続化したもの（`arg` の枝を避ける）

---

## ファイル構成

### `DkMath/RH/Defs.lean`

位相ドリフトの基本定義だけを置く。

- `vertical (σ t : ℝ) : ℂ`  
  縦線パス \(s=\sigma+it\) のパラメータ化。

- `torque (z dz : ℂ) : ℝ`  
  複素数 \(z\) とその変化 \(dz\) に対し、

  \[
  \mathrm{torque}(z,dz)=\Re(z)\Im(dz)-\Im(z)\Re(dz)
  \]

- `denom (z : ℂ) : ℝ`  
  分母としての \(\Re(z)^2+\Im(z)^2\)。これは `Complex.normSq z` と一致する。

- `driftFreeLocal (z dz : ℂ) : Prop`  
  局所ドリフト消失条件：`torque z dz = 0`

- `phaseVel (f : ℝ → ℂ) (t : ℝ) : ℝ`（noncomputable）  
  位相速度を

  \[
  \mathrm{phaseVel}(f,t)=\Im\Bigl(\frac{f'(t)}{f(t)}\Bigr)
  \]

  として定義（Lean では `deriv` を使う）。

- `phaseUnwrap (f : ℝ → ℂ) (t0 θ0 : ℝ) (t : ℝ) : ℝ`（noncomputable）  
  位相を **積分で定義**して連続化する：

  \[
  \Theta(t)=\theta_0+\int_{t_0}^{t}\mathrm{phaseVel}(f,u)\,du
  \]

  `arg` を直接扱わず、枝（2πジャンプ）問題を避けるのが狙い。

- `driftFreeAt (f : ℝ → ℂ) (t : ℝ) : Prop`  
  関数版の局所ドリフト消失：`driftFreeLocal (f t) (deriv f t)`。

---

### `DkMath/RH/Lemmas.lean`

定義同士の関係を、代数として確定する。

#### 1) 分母 `denom` の正体

`denom_eq_normSq` により、

\[
\mathrm{denom}(z)=\Re(z)^2+\Im(z)^2=\mathrm{normSq}(z)
\]

が確定する。

#### 2) 代数コア：\(\Im(dz/z)\) の展開

`im_div_eq_torque_div_normSq` により、

\[
\Im\Bigl(\frac{dz}{z}\Bigr)=\frac{\mathrm{torque}(z,dz)}{\mathrm{normSq}(z)}
\]

が得られる。  
これは「位相の微分公式」の骨格（\(\frac{d}{dt}\arg f=\Im(f'/f)\)）に直結する。

#### 3) ドリフト消失条件の同値

`driftFreeLocal_iff_im_div_eq_zero` により、\(z\neq0\) のもとで

\[
\mathrm{torque}(z,dz)=0\iff\Im\Bigl(\frac{dz}{z}\Bigr)=0
\]

が確定する。  
ここで \(z\neq0\) を仮定するのは、\(\mathrm{normSq}(z)\neq0\) を保証して分母を払うため。

#### 4) トルクの“共役表現”

`torque_eq_im_mul_conj` により（`open scoped ComplexConjugate` 使用）、

\[
\mathrm{torque}(z,dz)=\Im(dz\cdot\overline{z})
\]

が確定する。  
同内容の `star` 版として `torque_eq_im_mul_conj'` もある。

※mathlib4 では共役は `Complex.conj` ではなく、`conj z`（スコープ）または `star z`。

#### 5) 位相速度とトルクの接続

`phaseVel_eq_torque_div_normSq` により、

\[
\mathrm{phaseVel}(f,t)
=\frac{\mathrm{torque}(f(t),f'(t))}{\mathrm{normSq}(f(t))}
\]

が確定する（ここで \(f'(t)\) は `deriv f t`）。

さらに `phaseVel_eq_im_mul_conj_div_normSq` により、

\[
\mathrm{phaseVel}(f,t)
=\frac{\Im(f'(t)\cdot\overline{f(t)})}{\mathrm{normSq}(f(t))}
\]

という、より自然な複素表現も確定した。

#### 6) ドリフト消失と位相速度ゼロの同値（関数版）

`driftFreeLocal_iff_phaseVel_eq_zero` と `driftFreeAt_iff_phaseVel_eq_zero` により、\(f(t)\neq0\) のもとで

\[
\mathrm{driftFreeAt}(f,t)\iff\mathrm{phaseVel}(f,t)=0
\]

が確定する。  
以後、「ドリフト消失」を位相速度の言葉で扱える。

---

### `DkMath/RH/Theorems.lean`

積分で定義した位相が、本当に位相速度を微分として持つことを示す。

#### `phaseUnwrap_hasDerivAt`

仮定：`Continuous (phaseVel f)`（位相速度が連続）

結論：

\[
\frac{d}{dt}\Bigl(\theta_0+\int_{t_0}^{t}\mathrm{phaseVel}(f,u)\,du\Bigr)
=\mathrm{phaseVel}(f,t)
\]

Lean では `HasDerivAt` で形式化している。

証明の中身は次の通り。

- `phaseUnwrap` を展開し、`intervalIntegral` の「右端微分定理」を使う  
  `intervalIntegral.integral_hasDerivAt_right` を核にしている。
- 連続性から `IntervalIntegrable` と `StronglyMeasurableAtFilter` を作り、
  微分定理に必要な条件を満たす。
- 最後に「定数を足しても微分は変わらない」を `add_const` で処理する。

これにより、「アンラップ位相＝積分で作った連続位相」は、期待通りに位相速度を導関数として持つ、
という解析的な骨格が Lean 上で固定された。

---

## この段階で確定したこと（要点）

1. **局所の位相変化**は、純代数として

\[
\Im(dz/z)=\mathrm{torque}(z,dz)/\mathrm{normSq}(z)
\]

で表せる。

1. **ドリフト消失**は、\(z\neq0\) のもとで

\[
\mathrm{torque}=0\iff\Im(dz/z)=0
\]

つまり「位相速度が 0」と同値になる。

1. **位相を積分で定義**すると、連続性の仮定のもとで

\[
(\mathrm{phaseUnwrap})'=\mathrm{phaseVel}
\]

が成立する（枝問題を回避したまま、微分が正しく取れる）。

---

## 次に進むときの自然な拡張

- `phaseUnwrap_hasDerivAt` の仮定を `ContinuousAt` や局所可積分へ弱める（必要に応じて）。
- 縦方向（t）だけでなく、横方向（σ）でも同じテンプレートを作り、
  \(\Im((\partial/\partial\sigma)\log f)\) の積分として「σドリフト」を定義する。
- その後に \(f(t)=\zeta(\sigma+it)\) を差し込み、ゼータ側の解析条件（零点回避など）を整理する。

このモジュールは「ゼータを入れる前に、位相の計算基盤を Lean で固める」段階として位置付ける。
