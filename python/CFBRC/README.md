# CosmicComplex (CC)

CosmicComplex は、複素数値関数

$$
G(\theta) = (x + i\theta)^d
$$

（およびその拡張）を **値としてではなく構造として観測** するための実験用モジュールである。

本モジュールの目的は、複素和の内部に現れる

- 項の支配構造
- 位相（arg）の運動
- 位相速度（位相微分）
- 部分和の幾何（polygon）
- 寄与率とエントロピー

を **可視化・数値化し、演算前後の変化（Motion）として比較可能にする** ことにある。

---

## 1. 基本思想

### 1.1 回転は「与えない」、勝手に生まれる

CosmicComplex は

- 三角関数（sin, cos）
- 指数関数（exp(iθ)）
- 円周率 π

に **一切依存しない**。

それにもかかわらず、複素平面上では明確な「回転（位相）」と
「位相速度」が観測される。

これは回転が **解析的に注入されたものではなく**、
複素数の加法・乗法という代数構造から **自発的（emergent）に生じる**
ことを示している。

π は位相の *ラベル整理（unwrap）* にのみ使われ、
構造定義そのものには関与しない。

---

## 2. モジュール構成

### 2.1 CosmicComplex クラス

```python
cc = CosmicComplex(d=8, x=4.0, mode="even")
```

#### パラメータ

- `d` : 次元（解像度）。偶数推奨。運用上は `d = 2^n` が扱いやすい
- `x` : 実軸スケール
- `mode` :
  - `"any"` : 制限なし
  - `"even"` : d を偶数に制限
  - `"dyadic"` : d = 2^n に制限

---

### 2.2 観測（Observation）

```python
obs = cc.observe(theta)
```

1 点 θ において、以下を同時に取得する：

- `G` : 複素値 \(G(\theta)\)
- `terms[k]` : 各項 \(T_k(\theta)\)
- `abs_terms[k]` : 各項の大きさ
- `contrib[k]` : 寄与率
- `dominant_k` : 支配項インデックス
- `partial_sums` : 部分和多角形
- `arg` : 位相
- `entropy` : 寄与率エントロピー

---

### 2.3 位相速度（位相微分）

\[
\omega(\theta) = \frac{d}{d\theta} \arg G(\theta)
\]

は、`observe` を θ グリッド上で評価し、

1. `arg` を unwrap
2. 数値微分

することで得られる。

これは **構造の回転慣性・安定性** を測る主要指標である。

---

## 3. 演算モノイドと Motion

CosmicComplex は「演算」をモノイドとして扱う。

### 3.1 Op（演算）

例：

- `ScaleX(a)` : x のスケーリング
- `FlipTheta()` : θ → −θ
- `ShiftTheta(t0)` : θ シフト
- `ChangeD(d)` : 次元変更

演算は合成可能：

```python
op = FlipTheta().then(ScaleX(1.25))
```

---

### 3.2 Motion（演算前後差分）

```python
motion = cc.motion(theta, op)
```

- before / after の Observation
- 差分：
  - ΔG
  - Δarg
  - 支配項遷移
  - Δentropy
  - 寄与率差分

を同時に記録する。

これは **構造の運動学的比較** を行うための中核機能である。

---

## 4. スケーリングと歪み（拡張予定）

本設計は π 非依存のため、以下の拡張が自然に可能：

- 虚軸スケール変更
  \[
  G(\theta) = (x + i\alpha\theta)^d
  \]

- 斜交化（直交破壊）
  \[
  z = x + (\beta + i\alpha)\theta
  \]

これにより

- 支配項階段の移動
- 位相速度の変形
- 部分和多角形の歪み

を系統的に観測できる。

---

## 5. 研究的背景（メモ）

- 位相微分は
  \[
  \frac{d}{d\theta}\arg G
  = \operatorname{Im}\!\left(\frac{G'}{G}\right)
  \]

  に対応し、ζ関数の \(\zeta'/\zeta\) と同型の構造を持つ。
- 本モジュールは
  - RH における「σ=1/2 の安定性」
  - OOL-KND（Only One Line Knows No Drift）
  の観測的検証のための **制御可能モデル** として設計されている。

---

## 6. 注意

- 本モジュールは証明器ではない
- 観測・実験・構造理解のためのツールである
- 数値結果は近似であり、解釈は慎重に行うこと

---

## 7. 最後に

CosmicComplex は

> **「複素解析を最小限まで剥がした状態で、位相と構造の運動を読むための計器」**

である。

---
