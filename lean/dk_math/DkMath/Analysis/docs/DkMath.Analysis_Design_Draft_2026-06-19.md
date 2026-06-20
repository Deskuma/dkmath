# DkMath.Analysis 実数解析層 設計書ドラフト

作成日: 2026-06-19  
対象: Lean `DkMath.Analysis.*` 実装準備 / Codex 作業指示用  
状態: Draft 0.1 + implementation checkpoint

## 0.1. 2026-06-19 implementation checkpoint

This draft began as a pre-implementation design. The Route B algebraic core is
now implemented beyond the original second milestone:

```text
GapInterval
  exact rational closed intervals, width, separation, addition,
  nonnegative multiplication, and nonnegative powers

DkReal
  nested rational intervals with width tending to zero

DkReal.Equiv
  vanishing-separation equivalence and Setoid

DkNNReal
  nonnegative representation wrapper

DkNNRealQ
  quotient by representation equivalence
  Zero / One / Add / Mul / Pow / NatCast
  CommSemiring
```

The following design boundary is now authoritative:

```text
Computable algebraic layer:
  DkReal, DkNNReal, DkNNRealQ
  rational endpoint computation
  convergence and congruence certificates
  no selected Mathlib real value

Semantic bridge layer:
  future DkNNRealQ -> NNReal / Real
  representative independence
  preservation and reflection of order
  may be noncomputable
```

The next independent tasks are:

1. **Ordered algebra.** `DkReal.Order` now defines order by vanishing positive
   lower-endpoint defect, proves invariance under `Equiv`, and installs a
   `PartialOrder` on `DkNNRealQ`. Addition, multiplication, and natural powers
   are monotone. Next prove that zero is least, inspect the ordered-algebra
   hierarchy, and investigate totality before claiming a `LinearOrder`.
2. **Semantic evaluation.** In a separate `BridgeNNReal.lean` or
   `BridgeReal.lean`, extract the unique real point of a nested interval
   representation and prove independence from representatives.
3. **Bridge comparison.** Prove `Equiv x y -> eval x = eval y`; investigate
   the converse from the nested-width hypotheses.
4. **General signed arithmetic.** General multiplication requires minimum and
   maximum over four endpoint products and must not reuse the name
   `mulNonneg`.

The earlier future-tense file lists below are retained as historical planning
records. The implemented module list in `Analysis-Initial-Layer.md` is the
current source of truth.

## 0. 目的

`DkMath.Analysis` は、Mathlib の解析基盤を置き換える層ではなく、DkMath の宇宙式語彙で実数解析を再解釈し、Lean で扱える API 群として整備する層である。

主語は次の 3 つである。

1. Gap: 単位・基準・保存される出力値。
2. Body: 2 点間・差分区間・観測点間を埋める多項式的内部。
3. GN: Gap と Body を接続する差分補正核。

第一原理は次の式でよい。

$$
(u+\delta)^d-u^d=\delta\,GapGN_d(u,\delta)
$$

ここで `GapGN` は、既存の `GN` の引数順・定義と衝突しないために置く解析層 wrapper とする。既存側で `GN d x u` が `$ (x+u)^d-u^d = x * GN d x u $` 型なら、設計上は

```lean
GapGN d u δ := GN d δ u
```

として接続する。

## 1. 会話ログから抽出された最終成分

### 1.1. CF2D: 連続より前にある保存核

三角関数実装から得た核は、二成分平方質量

$$
Q(x,y)=x^2+y^2
$$

と積

$$
(a,b)\star(x,y)=(ax-by,ay+bx)
$$

である。主定理は

$$
Q(r\star z)=Q(r)Q(z)
$$

であり、`Q(r)=1` の `UnitKernel` が `Q(z)` を保存する。ここから三角関数型の加法公式は、解析的奇跡ではなく保存核の座標射影として出る。

この層の実装上の意味は次である。

```text
Vec.q2       = 二成分平方質量
Vec.star     = 質量を乗法的に運ぶ合成則
UnitKernel   = q2 = 1 の単位核
KernelFamily = 加法パラメータから単位核への保存写像
cfcos/cfsin  = 保存核族の Core/Beam 座標
```

`DkMath.Analysis` はここから「保存核を連続パラメータで走査する層」へ進む。

### 1.2. 実数 $\mathbb{R}$ の位置づけ

標準数学の $\mathbb{R}$ は、観測点そのものではなく、切れ目や極限を閉じるための完成空間である。DkMath 側では、実数を単に「切れ目がない点集合」と見るのではなく、離散観測点の間を保存核・差分核・補正核で埋められる完成空間として読む。

従って、`DkMath.Analysis` は次の二重構造を持つ。

```text
Route A: Mathlib ℝ への橋
  標準実数上で Gap / Body / GN が正しく動くことを示す。

Route B: DkReal / GapReal
  観測可能な近似と GN/Body 補正を持つ計算可能実数構造を作る。
```

Route A は外部数学・Mathlib との安全な接続である。Route B が DkMath の本丸である。

### 1.3. 単位宇宙式のゼロドリフト解析

単位宇宙式の基本残差を次で定義する。

$$
E(x,u)=(x+u)^2-x(x+2u)-u^2
$$

理想状態では

$$
E(x,u)=0
$$

である。2 点 drift は

$$
D_E(x,y;u)=E(x,u)-E(y,u)
$$

で、理想状態では任意の $x,y$ で $D_E(x,y;u)=0$ となる。

重要な区別は次である。

```text
絶対誤差ゼロ:
  E(x,u) = 0

二点 drift ゼロ:
  E(x,u) = E(y,u)
```

2 点 drift ゼロだけでは、全点に同じ bias が乗った場合を検出できない。そのため `Residual` と `Drift` は API として分ける。

### 1.4. Gap 伸長と完全補正

有限精度で $\tilde u=u+\varepsilon$ を扱うと、Gap の誤差は

$$
\tilde u^d-u^d=(u+\varepsilon)^d-u^d
$$

である。DkMath ではこれを Taylor の主項で丸めず、全階層を GN で保持する。

$$
(u+\varepsilon)^d-u^d=\varepsilon\,GapGN_d(u,\varepsilon)
$$

よって補正式は

$$
u^d=(u+\varepsilon)^d-\varepsilon\,GapGN_d(u,\varepsilon)
$$

ではなく、正しくは観測値 $\tilde u=u+\varepsilon$ を使って

$$
u^d=\tilde u^d-\varepsilon\,GapGN_d(u,\varepsilon)
$$

である。実装では変数名の混乱を避けるため、次の形を採用する。

$$
u^d = observed^d - err \cdot GapGN_d(base,err)
$$

ただし `observed = base + err` である。

### 1.5. GapFill: 2 点間の穴埋め

2 点 $u_1,u_2$ の間を

$$
u(t)=u_1+t(u_2-u_1),\quad 0\le t\le 1
$$

で走査し、Gap 側を

$$
GapFill_d(u_1,u_2,t)=\nu(t)^d
$$

とする。端点差分は

$$
u(1)^d-\nu(0)^d=(u_2-u_1)GapGN_d(u_1,u_2-u_1)
$$

である。これが離散観測点 $u_1^d,u_2^d$ の間を埋める Body である。

### 1.6. Pascal / Petal / GN の接続

パスカルの三角形は、単純な 2 分岐木ではなく、左右にずらした自己を重ねる構造である。

```text
(1,2,1,0) + (0,1,2,1) = (1,3,3,1)
```

これは `OverlapTwoPetal`、すなわち重畳相対 2 花弁構造として読める。

`Pascal cell (n,k)` は、Petal 側では次の意味を持つ。

```text
depth n       = 成長深度
address k     = 到達住所 / channel
choose n k    = その住所への重畳 multiplicity
```

weighted 版は

$$
W(n,k;x,u)=\binom nk x^k u^{n-k}
$$

であり、

$$
\sum_{k=0}^n W(n,k;x,u)=(x+u)^n
$$

を与える。`k=0` を Gap として切り出すと、残りが GN Body になる。

$$
(x+u)^n-u^n=\sum_{k=1}^{n}\binom nk x^k u^{n-k}=x\,GN_n(x,u)
$$

## 2. 実装方針

### 2.1. 方針 A: Mathlib ℝ への橋

目的は、標準実数解析の上で DkMath の GapFill / GN / Body が正しく動くことを示すことである。

最初に閉じる定理は、実は多くを `CommRing` で閉じられる。

```lean
theorem gapGN_sub_eq_delta_mul
    [CommRing R] (d : ℕ) (u δ : R) :
    (u + δ)^d - u^d = δ * GapGN R d u δ
```

ただし `d = 0` の場合は左辺が `0` で、右辺も `0` になるよう `GapGN` を定義する。

実数固有の定理は後段に分ける。

```lean
theorem gapFill_mem_Icc_of_nonneg
    {u₁ u₂ t : ℝ} {d : ℕ}
    (h01 : 0 ≤ t ∧ t ≤ 1)
    (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
    gapFill d u₁ u₂ t ∈ Set.Icc (u₁^d) (u₂^d)
```

この形なら、代数恒等式と順序・連続の橋が分離できる。

### 2.2. 方針 B: DkReal / GapReal

いきなり標準実数全体を再構成しない。最初は有限区間近似 `GapInterval` から始める。

```lean
structure GapInterval where
  lo : ℚ
  hi : ℚ
  le_lo_hi : lo ≤ hi
```

正の区間に限定した冪写像を先に作る。

```lean
def GapInterval.powNonneg (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) : GapInterval :=
  { lo := I.lo ^ d
    hi := I.hi ^ d
    le_lo_hi := by
      -- monotonicity of pow on nonnegative rationals
      ... }
```

次に幅の厳密式を証明する。

```lean
theorem GapInterval.pow_width_eq
    (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
    (I.hi^d - I.lo^d) =
      (I.hi - I.lo) * GapGN ℚ d I.lo (I.hi - I.lo)
```

`DkReal` は次段階で、入れ子区間列として定義する。

```lean
structure DkReal where
  lo : ℕ → ℚ
  hi : ℕ → ℚ
  valid : ∀ n, lo n ≤ hi n
  nested : ∀ n, lo n ≤ lo (n+1) ∧ hi (n+1) ≤ hi n
  width_tends_zero : Tendsto (fun n => hi n - lo n) atTop (𝓝 0)
```

ただし `DkReal → ℝ` の意味論写像 `eval` は `noncomputable` になる可能性が高い。従って初期実装では、`DkReal` の値そのものではなく、区間演算と幅評価を先に閉じる。

## 3. 推奨ファイル構成

### 3.1. Analysis 本体

```text
DkMath/Analysis/
  Basic.lean
  CosmicResidual.lean
  GapGN.lean
  GapFill.lean
  ErrorKernel.lean
  Interval.lean
  RealBridge.lean
  TaylorBridge.lean
  ScaledPascal.lean
```

役割:

```text
Basic.lean
  namespace、共通 notation、軽量 import。

CosmicResidual.lean
  E(x,u)、Drift、bias、x 方向不感性、u 方向感度。

GapGN.lean
  GapGN wrapper、既存 GN との接続、差分恒等式。

GapFill.lean
  gapLine、gapFill、端点、差分、正区間上の mem Icc。

ErrorKernel.lean
  observed/base/error、exact correction、residual recovery。

Interval.lean
  ℝ / ℚ 区間上の GapFill、幅評価、monotonicity。

RealBridge.lean
  Mathlib の continuous / differentiable / HasDerivAt との橋。

TaylorBridge.lean
  GapGN の先頭項が d*u^(d-1) であること、Taylor 主項との接続。

ScaledPascal.lean
  scaledPascal、weightedBinomTerm、Vandermonde、GN tail 接続。
```

### 3.2. DkReal サブパッケージ

```text
DkMath/Analysis/DkReal/
  Basic.lean
  Interval.lean
  Order.lean
  Algebra.lean
  Pow.lean
  GapFill.lean
  BridgeReal.lean
```

初期の優先順位:

```text
1. Interval.lean
   GapInterval と幅評価。

2. Pow.lean
   非負区間の pow 写像。

3. GapFill.lean
   区間 GapFill と GN 幅補正。

4. Basic.lean
   DkReal 入れ子区間列の定義。

5. BridgeReal.lean
   eval : DkReal → ℝ は後回し。必要なら noncomputable として分離。
```

### 3.3. Petal 側ブリッジ

Pascal-Petal は `Analysis` 内部だけでなく、`DkMath.Petal` からも使いたい。従って橋ファイルは Petal 側に置くのが自然である。

```text
DkMath/Petal/PascalBridge.lean
```

内容:

```lean
def pascalMass (n k : ℕ) : ℕ :=
  if k ≤ n then Nat.choose n k else 0

def pascalPetalMass (depth address : ℕ) : ℕ :=
  pascalMass depth address
```

主定理:

```lean
theorem pascalMass_succ :
  pascalMass (n+1) k = pascalMass n (k-1) + pascalMass n k
```

実際には `k = 0` の扱いが面倒なので、最初は `Nat.choose` の既存補題を直接使うか、`getD` 形式で padded row を実装する。

## 4. API 一覧

### 4.1. CosmicResidual API

```lean
def cosmicGap (x u : R) : R :=
  (x + u)^2 - x * (x + 2*u)

lemma cosmicGap_eq_sq [CommRing R] (x u : R) :
  cosmicGap x u = u^2

def cosmicResidual (x u : R) : R :=
  cosmicGap x u - u^2

lemma cosmicResidual_eq_zero [CommRing R] (x u : R) :
  cosmicResidual x u = 0

def cosmicDrift (x y u : R) : R :=
  cosmicResidual x u - cosmicResidual y u

lemma cosmicDrift_eq_zero [CommRing R] (x y u : R) :
  cosmicDrift x y u = 0
```

補助観測:

```lean
def outputBiasResidual (bias : R) (x u : R) : R :=
  cosmicGap x u - (u^2 + bias)

def beamPerturbedGap (η x u : R) : R :=
  (x + u)^2 - x * (x + 2*u + η)

lemma beamPerturbedGap_eq :
  beamPerturbedGap η x u = u^2 - η*x
```

### 4.2. GapGN API

```lean
def gapGN [CommSemiring R] (d : ℕ) (u δ : R) : R :=
  ∑ k in Finset.range d,
    (Nat.choose d (k+1) : R) * u^(d-1-k) * δ^k
```

注意: `d-1-k` は Nat 減算の扱いがあるため、Lean では `Fin d` で書く方が安全な可能性がある。

候補:

```lean
def gapGN [CommSemiring R] (d : ℕ) (u δ : R) : R :=
  ∑ j in Finset.Icc 1 d,
    (Nat.choose d j : R) * u^(d-j) * δ^(j-1)
```

主定理:

```lean
theorem pow_add_sub_pow_eq_delta_mul_gapGN
    [CommRing R] (d : ℕ) (u δ : R) :
    (u + δ)^d - u^d = δ * gapGN d u δ
```

同値な加法版:

```lean
theorem pow_add_eq_pow_add_delta_mul_gapGN
    [CommSemiring R] (d : ℕ) (u δ : R) :
    (u + δ)^d = u^d + δ * gapGN d u δ
```

### 4.3. ErrorKernel API

```lean
def observedGapError [CommRing R] (d : ℕ) (base err : R) : R :=
  (base + err)^d - base^d

lemma observedGapError_eq_err_mul_gapGN
    [CommRing R] (d : ℕ) (base err : R) :
    observedGapError d base err = err * gapGN d base err

lemma exactCorrection
    [CommRing R] (d : ℕ) (base err : R) :
    (base + err)^d - err * gapGN d base err = base^d
```

### 4.4. GapFill API

```lean
def gapLine (u₁ u₂ t : R) : R :=
  u₁ + t * (u₂ - u₁)

def gapFill (d : ℕ) (u₁ u₂ t : R) : R :=
  (gapLine u₁ u₂ t)^d

lemma gapLine_zero : gapLine u₁ u₂ 0 = u₁
lemma gapLine_one  : gapLine u₁ u₂ 1 = u₂
lemma gapFill_zero : gapFill d u₁ u₂ 0 = u₁^d
lemma gapFill_one  : gapFill d u₁ u₂ 1 = u₂^d

lemma gapFill_endpoint_sub_eq
    [CommRing R] (d : ℕ) (u₁ u₂ : R) :
    gapFill d u₁ u₂ 1 - gapFill d u₁ u₂ 0 =
      (u₂ - u₁) * gapGN d u₁ (u₂ - u₁)
```

実数順序版:

```lean
lemma gapLine_mem_Icc
    {u₁ u₂ t : ℝ}
    (h : t ∈ Set.Icc 0 1) (hle : u₁ ≤ u₂) :
    gapLine u₁ u₂ t ∈ Set.Icc u₁ u₂

lemma gapFill_mem_Icc_of_nonneg
    {d : ℕ} {u₁ u₂ t : ℝ}
    (h : t ∈ Set.Icc 0 1) (h0 : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
    gapFill d u₁ u₂ t ∈ Set.Icc (u₁^d) (u₂^d)
```

### 4.5. ScaledPascal API

```lean
def scaledPascal [CommSemiring R] (u : R) (d k : ℕ) : R :=
  (Nat.choose d k : R) * u^k

def weightedBinomTerm [CommSemiring R] (x u : R) (d k : ℕ) : R :=
  (Nat.choose d k : R) * x^k * u^(d-k)
```

主定理:

```lean
theorem sum_weightedBinomTerm_eq_pow
    [CommSemiring R] (x u : R) (d : ℕ) :
    (∑ k in Finset.range (d+1), weightedBinomTerm x u d k) = (x+u)^d

theorem weightedBinom_tail_eq_sub
    [CommRing R] (x u : R) (d : ℕ) :
    (∑ k in Finset.Icc 1 d, weightedBinomTerm x u d k) = (x+u)^d - u^d

theorem weightedBinom_tail_eq_x_mul_GN
    [CommRing R] (x u : R) (d : ℕ) :
    (∑ k in Finset.Icc 1 d, weightedBinomTerm x u d k) = x * GN d x u
```

### 4.6. DkReal prototype API

```lean
structure GapInterval where
  lo : ℚ
  hi : ℚ
  le_lo_hi : lo ≤ hi

def GapInterval.width (I : GapInterval) : ℚ :=
  I.hi - I.lo

def GapInterval.powNonneg (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) : GapInterval :=
  ...

theorem GapInterval.pow_width_eq
    (d : ℕ) (I : GapInterval) (hlo : 0 ≤ I.lo) :
    (GapInterval.powNonneg d I hlo).width =
      I.width * gapGN d I.lo I.width
```

`DkReal` は後段:

```lean
structure DkReal where
  lo : ℕ → ℚ
  hi : ℕ → ℚ
  valid : ∀ n, lo n ≤ hi n
  nested : ∀ n, lo n ≤ lo (n+1) ∧ hi (n+1) ≤ hi n
  width_tends_zero : Tendsto (fun n => hi n - lo n) atTop (𝓝 0)
```

## 5. 実装順序

### 5.1. Phase 0: 現コード確認

Codex は最初に現ワークスペースを確認する。

```text
確認対象:
- 既存 GN の名前、namespace、引数順
- WeightedBinomial / powerKernel / Petal / Trig の import path
- `DkMath.lean` の公開 import 方針
```

現時点でこちらにあるのは `__snapshot-dk_math-lean-code-260617-0327.tar.gz.sha256` のみで、アーカイブ本体は確認できていない。実装に入る前に `.tar.gz` 本体があるか確認する。

### 5.2. Phase 1: 代数核を閉じる

追加ファイル:

```text
DkMath/Analysis/Basic.lean
DkMath/Analysis/CosmicResidual.lean
DkMath/Analysis/GapGN.lean
```

閉じる定理:

```text
cosmicGap_eq_sq
cosmicResidual_eq_zero
cosmicDrift_eq_zero
pow_add_eq_pow_add_delta_mul_gapGN
pow_add_sub_pow_eq_delta_mul_gapGN
exactCorrection
```

### 5.3. Phase 2: GapFill 区間

追加ファイル:

```text
DkMath/Analysis/GapFill.lean
DkMath/Analysis/Interval.lean
```

閉じる定理:

```text
gapLine_zero / gapLine_one
gapFill_zero / gapFill_one
gapFill_endpoint_sub_eq
gapLine_mem_Icc
gapFill_mem_Icc_of_nonneg
```

### 5.4. Phase 3: ErrorKernel

追加ファイル:

```text
DkMath/Analysis/ErrorKernel.lean
```

閉じる定理:

```text
observedGapError_eq_err_mul_gapGN
exactCorrection
beamPerturbedGap_eq
x_input_perturbation_invariant
u_perturbation_sensitivity
```

### 5.5. Phase 4: ScaledPascal / GN tail

追加ファイル:

```text
DkMath/Analysis/ScaledPascal.lean
```

または既存 WeightedBinomial が十分なら、薄い bridge のみにする。

閉じる定理:

```text
sum_weightedBinomTerm_eq_pow
weightedBinom_tail_eq_sub
weightedBinom_tail_eq_x_mul_GN
scaledPascal_row_mul_vandermonde
```

### 5.6. Phase 5: Pascal-Petal bridge

追加ファイル:

```text
DkMath/Petal/PascalBridge.lean
```

閉じる定理:

```text
pascalMass_eq_choose_of_le
pascalMass_eq_zero_of_lt
pascalMass_succ
pascalPetalMass_eq_pascalMass
weightedPascalPetal_sum_eq_pow
pascal_gap_cell_eq_u_pow
pascal_body_cells_eq_x_mul_GN
```

### 5.7. Phase 6: DkReal prototype

追加ファイル:

```text
DkMath/Analysis/DkReal/Basic.lean
DkMath/Analysis/DkReal/Interval.lean
DkMath/Analysis/DkReal/Pow.lean
DkMath/Analysis/DkReal/GapFill.lean
```

最初は `ℚ` 区間演算のみでよい。

閉じる定理:

```text
GapInterval.width_nonneg
GapInterval.powNonneg_valid
GapInterval.pow_width_eq
GapInterval.pow_width_le_of_bound
```

`BridgeReal.lean` は後回しにする。

## 6. Codex への作業指示テンプレート

```text
目的:
DkMath.Analysis 実数解析層の最小核を実装する。
最初の対象は、GapGN による冪差分の完全補正式と、GapFill の端点差分である。

制約:
- 既存 GN / WeightedBinomial / powerKernel の名前と引数順を必ず確認する。
- 既存定理がある場合は再実装せず bridge theorem として薄く接続する。
- 代数恒等式は可能な限り `[CommSemiring R]` / `[CommRing R]` で閉じる。
- 実数順序・連続性・微分は `RealBridge.lean` へ分離する。
- `DkReal` は最初から標準 `ℝ` 全体を再実装しない。`GapInterval` から開始する。

実装順:
1. `DkMath/Analysis/Basic.lean` を作る。
2. `GapGN.lean` で `gapGN` wrapper と冪差分定理を作る。
3. `CosmicResidual.lean` で残差と drift を作る。
4. `GapFill.lean` で `gapLine` / `gapFill` / endpoint theorem を作る。
5. `ErrorKernel.lean` で exact correction を作る。
6. 既存 WeightedBinomial があれば `ScaledPascal.lean` は bridge に留める。
7. すべて `lake build DkMath.Analysis...` で確認する。
```

## 7. 成功条件

最小成功条件:

```text
- `DkMath.Analysis.Basic` が import できる。
- `cosmicResidual_eq_zero` が通る。
- `(u+δ)^d = u^d + δ*gapGN d u δ` が通る。
- `exactCorrection` が通る。
- `gapFill` の端点と端点差分が通る。
```

第一マイルストーン:

```text
- Mathlib ℝ 上で正区間 GapFill が `[u₁^d,u₂^d]` に入る。
- `GapInterval` の `pow_width_eq` が ℚ で通る。
- Pascal tail と GN が bridge される。
```

第二マイルストーン:

```text
- `DkReal` 入れ子区間列が定義される。
- GapInterval 演算が DkReal の近似列へ持ち上がる。
- 必要なら noncomputable な `eval : DkReal → ℝ` を別ファイルに隔離する。
```

## 8. 注意点

1. `$|u_1-u_2|=δ$` から一般に `$|u_1^d-u_2^d|=δ^d$` は出ない。正しくは差分核が必要である。

    $$
    u_2^d-u_1^d=(u_2-u_1)\sum_{k=0}^{d-1}u_2^{d-1-k}u_1^k
    $$

2. `GapGN d u δ` の定義と既存 `GN d x u` の引数順を混同しない。解析層では wrapper を置く。

3. `DkReal` に `DecidableEq` を要求しない。計算可能実数では等号判定は一般に重い。

4. `DkReal → ℝ` の意味論写像は必要だが、初期実装では後回しでよい。ここは `noncomputable` を避けられない可能性がある。

5. CF2D は三角関数の全解析を証明したものではない。Phase 1 は三角関数型の座標恒等式の代数的発生源である。連続性・微分・周期性・角度復元は解析層の後段で扱う。

## 9. 結論

`DkMath.Analysis` の核は、標準実数解析の再実装ではなく、DkMath の語彙で解析対象を次のように再構成することである。

```text
離散観測点
  ↓
Gap 差分
  ↓
Body による区間補完
  ↓
GN による完全補正
  ↓
Mathlib ℝ への意味論 bridge
  ↓
DkReal / GapReal による計算可能実数 prototype
```

最初に Lean で閉じるべき旗印はこれである。

$$
(u+\delta)^d=u^d+\delta\,GapGN_d(u,\delta)
$$

これは近似ではない。多項式恒等式による完全補正である。DkMath.Analysis はここから始める。
