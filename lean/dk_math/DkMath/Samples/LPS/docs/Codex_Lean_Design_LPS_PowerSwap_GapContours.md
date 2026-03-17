# Codex 向け Lean 実装設計図  

## LPS / PowerSwap / GapContours / Exchange

## 1. 目的

本設計図の目的は、深みに潜りすぎる前に、ここまでで **確定している内容** と **仮説段階の内容** を分離し、Lean へ安全に落とせる最小核を Codex 担当者へ渡すことである。

対象は主に次の 4 系統である。

- `BigFamily` / `BigFamilyInt`
- `PowerSwap`
- `Exchange`
- `GapContours`
- `GapFillRank` / `BigFamilyExamples`

狙いは、一般理論をいきなり完成させることではなく、**戻り道を確保する局所核** を Lean に固定することにある。

---

## 2. 基本方針

### 2.1. 実装原則

- 先に **定義** を固定する
- 次に **基本補題** を追加する
- その後で **サンプル定理** を通す
- 一般理論・強い主張は後回しにする

### 2.2. 数学的立場

本件は「完全理論の証明」を狙う段階ではなく、現時点で見えている構造を Lean 上で再利用可能な骨格にする段階である。

---

## 3. モジュール構成

推奨配置は次の通り。

```text
DkMath/Samples/LPS/BigFamily.lean
DkMath/Samples/LPS/BigFamilyInt.lean
DkMath/Samples/LPS/PowerSwap.lean
DkMath/Samples/LPS/GapFillRank.lean
DkMath/Samples/LPS/BigFamilyExamples.lean
DkMath/Samples/LPS/Exchange.lean
DkMath/Samples/LPS/PowerSwapBranch.lean
DkMath/Samples/LPS/GapContours.lean
```

### 各ファイルの役目

#### `BigFamily.lean`

自然数版の Big / Body / Gap / Core / Beam の定義と基本恒等式。

#### `BigFamilyInt.lean`

整数版の差分観測。`Nat` 減算の切り捨て問題を避ける本命土台。

#### `PowerSwap.lean`

\(
a^b=b^a
\)
の離散標本、対称性、基本例。

#### `GapFillRank.lean`

`FillableByPowSumExact` など、同次数冪和充填の観測述語。

#### `BigFamilyExamples.lean`

same Big / different Body / different observed minimum profile の標本群。

#### `Exchange.lean`

\(
A=a^t \Rightarrow A^m=a^{tm}
\)
型の粗視化↔微視化交換補題群。

#### `PowerSwapBranch.lean`

\(
x^y=y^x,\ x\ne y
\)
の正実数 branch のパラメータ表示と、その幾何的性質。

#### `GapContours.lean`

\(
F(x,y)=x^y-y^x
\)
と、その局所座標
\(
U=y\log x,\ V=x\log y
\)
および
\(
p=(U+V)/2,\ q=U-V
\)
の整理。

---

## 4. 確定層として Lean 化する対象

## 4.1. BigFamily 基本定義

### 定義

\[
\mathcal{B}_0(d;x,u) := (x+u)^d
\]

\[
\mathcal{B}_1(d;x,u) := \mathcal{B}_0(d;x,u)-u^d
\]

\[
\mathcal{B}_2(d;x,u) := u^d
\]

\[
\mathcal{B}_3(d;x,u) := x^d
\]

\[
\mathcal{B}_4(d;x,u) := \mathcal{B}_1(d;x,u)-\mathcal{B}_3(d;x,u)
\]

### 基本定理

\[
\mathcal{B}_0 = \mathcal{B}_1 + \mathcal{B}_2
\]

\[
\mathcal{B}_1 = \mathcal{B}_3 + \mathcal{B}_4
\]

\[
\mathcal{B}_0 = \mathcal{B}_3 + \mathcal{B}_4 + \mathcal{B}_2
\]

---

## 4.2. Exchange の最小条件

### 確定済み補題

\[
A=a^t \Rightarrow A^m=a^{tm}
\]

Lean 名の推奨:

```lean
exchange_condition_minimal_nat
exchange_condition_minimal_int
```

### この補題の意味

- 粗い基底 \(A\) が細かい基底 \(a\) の \(t\) 束である
- 次数 \(m\) の粗視化表示が
- 次数 \(tm\) の微視化表示へ変換できる

これは Beam 解像度上昇の最小核である。

---

## 4.3. PowerSwap 実数 branch

### 確定式

\[
x^y=y^x,\ x\ne y
\]

の正実数解は

\[
x=t^{1/(t-1)},\qquad y=t^{t/(t-1)},\qquad t>0,\ t\ne 1
\]

で与えられる。

### Lean 化対象

まずは theorem 本体より、**定義と correctness lemma** を優先する。

```lean
def powerSwapBranchX (t : ℝ) : ℝ := t ^ (1 / (t - 1))
def powerSwapBranchY (t : ℝ) : ℝ := t ^ (t / (t - 1))
```

必要条件:

- \(t>0\)
- \(t\ne 1\)

主補題候補:

\[
\bigl(powerSwapBranchX(t)\bigr)^{powerSwapBranchY(t)}=
\bigl(powerSwapBranchY(t)\bigr)^{powerSwapBranchX(t)}
\]

実数冪が絡むので、最初は definition/comment 優先でもよい。

---

## 4.4. 非自明 branch 上の特別点

### Lean で固定すべき事実

\[
(2,4),\ (4,2)
\]

は nontrivial branch 上の整数格子点である。

基本例:

```lean
theorem powerSwap_two_four : 2 ^ 4 = 4 ^ 2
theorem powerSwap_four_two : 4 ^ 2 = 2 ^ 4
```

parameter 表示と接続するなら、将来候補として

```lean
theorem powerSwap_branch_at_two :
  powerSwapBranchX 2 = 2 ∧ powerSwapBranchY 2 = 4
```

---

## 4.5. \((e,e)\) の中心性

### 確定している幾何

\((e,e)\) は

- 自明枝 \(y=x\)
- 非自明枝 \(x^y=y^x,\ x\ne y\)

の交会中心である。

局所座標

\[
x=e+u,\quad y=e+v
\]

で

\[
F(x,y)=x^y-y^x
\]

を展開すると、一次項が消え、局所主部は
\[
v^2-u^2
\]
型になる。

### Lean 実装方針

ここは今すぐ完全 theorem 化しなくてよい。  
`GapContours.lean` に

- 定義
- comment
- 証明方針メモ

を置く。

---

## 4.6. Gap 等高線の正規化写像

### 定義

\[
U := y\ln x,\qquad V := x\ln y
\]

\[
p := \frac{U+V}{2},\qquad q := U-V
\]

### 確定関係

\[
x^y=e^U,\qquad y^x=e^V
\]

\[
F=x^y-y^x=e^U-e^V
\]

\[
F = 2e^p \sinh\!\left(\frac q2\right)
\]

### Lean 実装方針

まずは定義のみ。

```lean
def gapU (x y : ℝ) : ℝ := y * Real.log x
def gapV (x y : ℝ) : ℝ := x * Real.log y
def gapP (x y : ℝ) : ℝ := (gapU x y + gapV x y) / 2
def gapQ (x y : ℝ) : ℝ := gapU x y - gapV x y
```

確定補題候補:

\[
gapQ(x,y)=xy\left(\frac{\ln x}{x}-\frac{\ln y}{y}\right)
\]

必要なら

```lean
def harmonicCoord (x : ℝ) : ℝ := Real.log x / x
```

を導入する。

---

## 4.7. ObservedMin サンプル群

### 既存の局所定義

\[
ObservedMinOne(d,n)
\]

\[
ObservedMinTwo(d,n)
\]

### 現段階での扱い

`BigFamilyExamples.lean` 内に局所維持でよい。  
一般 API への昇格は保留。

### Lean で固定済み標本

立方 \(d=3\) で少なくとも 3 標本。

- \(216 \to 91 / 64\)
- \(64 \to 35 / 27\)
- \(125 \to 65 / 64\)

および平方 \(d=2\) の 1 標本。

### 総括定理

```lean
cube_observed_min_split_reproduced_three_samples
```

---

## 5. 仮説層として comment 化する対象

以下は theorem ではなく、design comment / TODO / conjecture に留める。

### 5.1. Beam 解像度仮説

次数 \(d\) が上がると Beam 層数が増え、形状変形と filling の自由度が増す。

### 5.2. GN 構造因子仮説

profile 分岐の本体は素数因子より先に
\[
x\cdot GN
\]
という構造因子に現れる。

### 5.3. profile 地形仮説

fixed Big において

- single \(d\)-power compressible な rigid 島
- two \(d\)-power fillable な diffuse 島

が共存する。

### 5.4. DHNT 指数再配分仮説

\[
n=e^k
\]
を標準座標と見た時、same Big / residual の profile は
単位系宇宙への着地可能性で分類できる。

### 5.5. アイゼンシュタイン整数様マッピング

\(|x^y-y^x|=N\) の等高線束は、適切な正規化変換で三角格子・アイゼンシュタイン整数的構造へ写る可能性がある。

---

## 6. Codex 担当者向け補題群リスト

以下、**実装優先順** で並べる。

## 6.1. Phase A. 既存強化

### A1

```lean
exchange_condition_minimal_nat
```

### A2

具体例補題

```lean
example : 4 ^ 2 = 2 ^ 4
example : 8 ^ 2 = 2 ^ 6
example : 9 ^ 2 = 3 ^ 4
example : 27 ^ 2 = 3 ^ 6
```

### A3

整数版

```lean
exchange_condition_minimal_int
```

---

## 6.2. Phase B. PowerSwap branch

### B1

```lean
def powerSwapBranchX
def powerSwapBranchY
```

### B2

```lean
theorem powerSwap_branch_correct
```

内容:
\[
x(t)^{y(t)} = y(t)^{x(t)}
\]

### B3

```lean
theorem powerSwap_branch_limit_to_e
```

これは重ければ comment でもよい。

### B4

```lean
theorem powerSwap_branch_at_two
theorem powerSwap_branch_at_half
```

---

## 6.3. Phase C. GapContours

### C1

```lean
def gapU
def gapV
def gapP
def gapQ
```

### C2

```lean
theorem gapQ_eq_xy_mul_Hdiff
```

内容:
\[
gapQ(x,y)=xy\left(\frac{\ln x}{x}-\frac{\ln y}{y}\right)
\]

### C3

```lean
theorem gapF_eq_expU_sub_expV
```

内容:
\[
x^y-y^x=e^{gapU}-e^{gapV}
\]

### C4

```lean
theorem gapF_eq_soft_hyperbolic_form
```

内容:
\[
F = 2e^p \sinh(q/2)
\]

最初は theorem でなく comment でもよい。

---

## 6.4. Phase D. LPS / ObservedMin 整理

### D1

現行 `ObservedMinOne/Two` は局所維持

### D2

補題名の整理

```lean
candidate_same_big_observed_min_profile
candidate_cube₂_same_big_observed_min_profile
candidate_cube₃_same_big_observed_min_profile
cube_observed_min_split_reproduced_three_samples
```

### D3

将来候補

```lean
def ObservedMin (d n r : ℕ) : Prop := ...
```

ただし今は保留。

---

## 7. リレーショナルマップ

```text
BigFamily / BigFamilyInt
   ├─ Big, Body, Gap, Core, Beam
   ├─ residual
   └─ examples

PowerSwap
   ├─ a^b = b^a (discrete examples)
   └─ (2,4), (4,2)

Exchange
   ├─ A = a^t → A^m = a^(tm)
   └─ coarse ↔ fine base exchange

PowerSwapBranch
   ├─ x(t), y(t)
   ├─ x(t)^y(t) = y(t)^x(t)
   ├─ (2,4), (4,2)
   └─ limit t → 1 gives (e,e)

GapContours
   ├─ F(x,y) = x^y - y^x
   ├─ U = y log x, V = x log y
   ├─ p = (U+V)/2, q = U - V
   ├─ F = e^U - e^V
   └─ q = xy(H(x)-H(y))

GapFillRank / BigFamilyExamples
   ├─ FillableByPowSumExact
   ├─ ObservedMinOne/Two
   ├─ same Big, different Body
   └─ profile split samples
```

---

## 8. 実装優先順位

### 最優先

- `Exchange.lean`
- `PowerSwapBranch.lean` の定義部
- `GapContours.lean` の定義部
- `gapQ_eq_xy_mul_Hdiff`

### 次点

- `powerSwap_branch_correct`
- `gapF_eq_expU_sub_expV`
- 具体例補題群

### 後回し

- \((e,e)\) の局所二次近似
- 一般 `ObservedMin`
- アイゼンシュタイン整数様マッピング
- GN 構造との一般接続

---

## 9. Codex 担当者への注意点

### 9.1. Real 冪は重い

`Real.rpow` が絡むと証明コストが上がる。  
最初は theorem より definition/comment を優先してよい。

### 9.2. Nat 減算は避ける

差分観測は可能なら `BigFamilyInt` 側で扱う。

### 9.3. サンプル層を壊さない

`Samples/LPS` は理論完成版ではなく、戻り道を残す実験層である。  
大改造より、最小補題追加を優先する。

---

## 10. Codex 向け短い依頼文

今回の実装では、

- \(
x^y=y^x
\)
の実数 branch
- \(
A=a^t \Rightarrow A^m=a^{tm}
\)
の交換補題
- \(
F(x,y)=x^y-y^x
\)
の等高線正規化座標

を Lean に固定し、既存の `Samples/LPS` の observed minimum profile 実験群と接続したい。

一般理論はまだ狙わず、戻り道のある局所核を固めることを優先する。
