# Boundary Zero Principle 設計書

## 1. 目的

本設計書は、宇宙式における Gap 構造を次の二つの視点に分離して Lean 形式化するための設計である。

1. 離散内部視点
   各離散宇宙では単位 \(u\) が存在し、構造上 \(u \neq 0\) が成立する。

2. 連続境界視点
   離散単位列 \(u_n > 0\) を取り、\(u_n \to 0\) とすることで、連続化・閉包・極限において \(u=0\) が境界点として現れる。

核心命題は次である。

\[
\forall n,\; u_n \neq 0
\]

でありながら、

\[
\lim_{n\to\infty} u_n = 0
\]

が成立する。

したがって、

\[
\mathrm{Gap}=0
\]

は離散宇宙内部の点ではなく、離散宇宙列の連続化された境界点として現れる。

---

## 2. 基本思想

宇宙式の単位つき基本形を考える。

\[
(x+u)^2 - x(x+2u) = u^2
\]

このとき、離散単位 \(u\) を Gap の源泉とみなす。

\[
\mathrm{Gap}(u) := u
\]

または二次宇宙式では、

\[
\mathrm{Gap}_2(u) := u^2
\]

と観測できる。

離散内部では \(u \neq 0\) であるため、

\[
\mathrm{Gap}(u) \neq 0
\]

が成立する。

一方、単位列 \(u_n\) が

\[
u_n > 0,\qquad u_n \to 0
\]

を満たすなら、

\[
\mathrm{Gap}(u_n) \to 0
\]

が成立する。

したがって、Gap は各離散宇宙内部では非零でありながら、連続境界では 0 に接続される。

---

## 3. 主要概念

### 3.1. Discrete Fiber

各 \(u > 0\) によって定まる離散宇宙を \(\mathcal U_u\) と呼ぶ。

\[
\mathcal U_u
\]

この内部では \(u\) は最小単位であり、

\[
u \neq 0
\]

が構造条件として固定される。

Lean では、まず型として宇宙を定義するよりも、単位条件を仮定として扱う。

```lean
variable {u : ℝ}

def IsDiscreteUnit (u : ℝ) : Prop :=
  0 < u
```

このとき、

```lean
theorem discreteUnit_ne_zero
    {u : ℝ} (hu : IsDiscreteUnit u) :
    u ≠ 0 := by
  exact ne_of_gt hu
```

を基本補題とする。

---

### 3.2. Gap

最小版では Gap を恒等関数として定義する。

\[
\mathrm{Gap}(u) := u
\]

```lean
def Gap (u : ℝ) : ℝ :=
  u
```

二次宇宙式向けには平方 Gap も定義する。

\[
\mathrm{GapSq}(u) := u^2
\]

```lean
def GapSq (u : ℝ) : ℝ :=
  u ^ 2
```

基本補題は次である。

```lean
theorem gap_pos_of_discreteUnit
    {u : ℝ} (hu : IsDiscreteUnit u) :
    0 < Gap u := by
  exact hu

theorem gap_ne_zero_of_discreteUnit
    {u : ℝ} (hu : IsDiscreteUnit u) :
    Gap u ≠ 0 := by
  exact ne_of_gt hu
```

平方 Gap については、

```lean
theorem gapSq_pos_of_discreteUnit
    {u : ℝ} (hu : IsDiscreteUnit u) :
    0 < GapSq u := by
  dsimp [GapSq]
  exact sq_pos_of_ne_zero (ne_of_gt hu)
```

を目標とする。

---

## 4. 連続境界視点

### 4.1. 標準単位列

最初の実装では、標準列を用いる。

\[
u_n := \frac{1}{n+1}
\]

Lean では自然数から実数へ埋め込む。

```lean
def unitSeq (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹
```

基本性質は次である。

\[
u_n > 0
\]

\[
u_n \neq 0
\]

\[
u_n \to 0
\]

Lean theorem 候補：

```lean
theorem unitSeq_pos (n : ℕ) :
    0 < unitSeq n := by
  -- positivity

theorem unitSeq_ne_zero (n : ℕ) :
    unitSeq n ≠ 0 := by
  exact ne_of_gt (unitSeq_pos n)

theorem tendsto_unitSeq_zero :
    Tendsto unitSeq atTop (𝓝 0) := by
  -- use tendsto_inv_atTop_zero_nat or related lemma
```

---

### 4.2. Gap の極限

Gap が恒等関数なら、

\[
\mathrm{Gap}(u_n) \to 0
\]

はただちに従う。

```lean
theorem tendsto_gap_unitSeq_zero :
    Tendsto (fun n => Gap (unitSeq n)) atTop (𝓝 0) := by
  simpa [Gap] using tendsto_unitSeq_zero
```

平方 Gap なら、

\[
u_n^2 \to 0
\]

を示す。

```lean
theorem tendsto_gapSq_unitSeq_zero :
    Tendsto (fun n => GapSq (unitSeq n)) atTop (𝓝 0) := by
  dsimp [GapSq]
  exact tendsto_unitSeq_zero.pow 2
```

---

## 5. 第一中核定理

### 5.1. 非零単位・境界零原理

各 \(n\) では Gap は非零である。

\[
\forall n,\; \mathrm{Gap}(u_n) \neq 0
\]

しかし極限では 0 に収束する。

\[
\mathrm{Gap}(u_n) \to 0
\]

これを次の名前で固定する。

```lean
theorem nonzero_gap_but_tendsto_zero :
    (∀ n : ℕ, Gap (unitSeq n) ≠ 0) ∧
    Tendsto (fun n => Gap (unitSeq n)) atTop (𝓝 0) := by
  constructor
  · intro n
    exact gap_ne_zero_of_discreteUnit (unitSeq_pos n)
  · exact tendsto_gap_unitSeq_zero
```

理論名：

```text
Nonzero Unit, Zero Boundary Principle
非零単位・境界零原理
```

意味：

\[
\forall n,\; \mathrm{Gap}(u_n)>0
\]

かつ

\[
\lim_{n\to\infty}\mathrm{Gap}(u_n)=0
\]

つまり、Gap は各離散宇宙内部では消えないが、連続境界では 0 に接続される。

---

## 6. 第二中核定理

### 6.1. 正 Gap・下限零原理

より構造的には、次を示したい。

\[
\forall n,\; 0 < \mathrm{Gap}(u_n)
\]

かつ

\[
\inf \{\mathrm{Gap}(u_n)\mid n\in\mathbb N\}=0
\]

Lean では最初から infimum を使わず、任意の正の \(\varepsilon\) に対して十分小さい Gap が存在することを示す。

\[
\forall \varepsilon>0,\;\exists n,\; \mathrm{Gap}(u_n)<\varepsilon
\]

```lean
theorem exists_gap_lt_of_pos
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, Gap (unitSeq n) < ε := by
  -- follows from tendsto_gap_unitSeq_zero
```

これにより、

```text
Gap は常に正だが、任意に小さくできる。
```

という構造を得る。

---

## 7. 宇宙式との接続

単位付き宇宙式：

\[
(x+u)^2 - x(x+2u) = u^2
\]

ここで右辺 \(u^2\) は二次 Gap である。

\[
\mathrm{GapSq}(u)=u^2
\]

したがって、

\[
u \neq 0
\]

ならば、

\[
\mathrm{GapSq}(u)>0
\]

一方で、\(u_n\to 0\) なら、

\[
\mathrm{GapSq}(u_n)\to 0
\]

が成立する。

このことにより、宇宙式は次の二層構造を持つ。

```text
離散内部:
  u > 0
  GapSq(u) > 0

連続境界:
  u_n > 0 for all n
  u_n → 0
  GapSq(u_n) → 0
```

---

## 8. 未解決問題との関係

FLT や ABC などの未解決問題では、単に実数的に Gap が小さいことでは足りない。

必要なのは、

\[
\mathrm{Gap}=0
\]

への算術的到達である。

しかし離散単位 \(u\) が残る限り、

\[
u \neq 0
\]

であるため、内部 Gap は消えない。

よって未解決問題の硬さは、次の差として現れる。

\[
\inf \mathrm{Gap}=0
\]

と

\[
\exists u,\; \mathrm{Gap}(u)=0
\]

の差である。

この差を宇宙式では BoundaryGap と呼ぶ。

---

## 9. Lean モジュール案

最初の実装場所：

```text
DkMath/CosmicFormula/BoundaryZero/Basic.lean
```

構成案：

```text
DkMath/CosmicFormula/BoundaryZero/Basic.lean
  - IsDiscreteUnit
  - Gap
  - GapSq
  - unitSeq
  - discreteUnit_ne_zero
  - gap_pos_of_discreteUnit
  - gap_ne_zero_of_discreteUnit
  - tendsto_unitSeq_zero
  - tendsto_gap_unitSeq_zero
  - tendsto_gapSq_unitSeq_zero

DkMath/CosmicFormula/BoundaryZero/CosmicBridge.lean
  - cosmic quadratic identity with GapSq
  - GapSq as unit-square remainder
  - tendsto cosmic remainder to zero

DkMath/CosmicFormula/BoundaryZero/Main.lean
  - public exports
```

---

## 10. 推奨 theorem 名

```lean
def IsDiscreteUnit
def Gap
def GapSq
def unitSeq

theorem discreteUnit_ne_zero
theorem gap_pos_of_discreteUnit
theorem gap_ne_zero_of_discreteUnit
theorem gapSq_pos_of_discreteUnit

theorem unitSeq_pos
theorem unitSeq_ne_zero
theorem tendsto_unitSeq_zero

theorem tendsto_gap_unitSeq_zero
theorem tendsto_gapSq_unitSeq_zero

theorem nonzero_gap_but_tendsto_zero
theorem positive_gap_but_tendsto_zero
theorem exists_gap_lt_of_pos
```

理論名としては以下を採用する。

```text
Boundary Zero Principle
境界ゼロ原理
```

副題：

```text
Nonzero Unit, Zero Boundary
非零単位・境界零
```

---

## 11. 実装順序

### Step 1. 最小定義

```lean
def IsDiscreteUnit (u : ℝ) : Prop := 0 < u
def Gap (u : ℝ) : ℝ := u
def GapSq (u : ℝ) : ℝ := u ^ 2
```

### Step 2. 離散内部補題

```lean
theorem discreteUnit_ne_zero
theorem gap_pos_of_discreteUnit
theorem gap_ne_zero_of_discreteUnit
theorem gapSq_pos_of_discreteUnit
```

### Step 3. 標準単位列

```lean
def unitSeq (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
```

### Step 4. 極限補題

```lean
theorem tendsto_unitSeq_zero
theorem tendsto_gap_unitSeq_zero
theorem tendsto_gapSq_unitSeq_zero
```

### Step 5. 中核定理

```lean
theorem nonzero_gap_but_tendsto_zero
theorem positive_gap_but_tendsto_zero
```

### Step 6. 宇宙式接続

既存の宇宙式補題：

\[
(x+u)^2 - x(x+2u) = u^2
\]

と `GapSq u` を接続する。

```lean
theorem cosmic_quadratic_gapSq
    (x u : ℝ) :
    (x + u)^2 - x * (x + 2*u) = GapSq u := by
  ring
```

---

## 12. 期待される効果

この形式化により、宇宙式理論に次の明確な区別が導入される。

```text
離散内部の非零性:
  u ≠ 0
  Gap(u) ≠ 0

連続境界の零性:
  u_n → 0
  Gap(u_n) → 0
```

これにより、未解決問題における困難を次の形で表現できる。

```text
実数的には Gap を 0 に近づけられる。
しかし離散構造内部では、単位 u が非零である限り Gap は 0 にならない。
```

したがって、未解決問題の本質は、

```text
連続境界で見える 0 を、離散内部の算術的到達点として実現できるか
```

という問いに再構成される。

---

## 13. 要約

Boundary Zero Principle は次を主張する。

\[
\forall n,\; u_n \neq 0
\]

でありながら、

\[
u_n \to 0
\]

が成立する。

したがって、

\[
\mathrm{Gap}=0
\]

は離散内部の点ではなく、連続化された境界点である。

宇宙式における Gap は、離散単位 \(u\) の存在により内部では非零である。

しかし、離散単位列を連続極限へ送ることで、Gap は境界において 0 と接続される。

これが、離散構造と連続構造を結ぶ第一の橋である。
