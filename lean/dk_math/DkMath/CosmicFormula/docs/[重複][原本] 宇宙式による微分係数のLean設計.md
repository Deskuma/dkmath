# 微分係数の宇宙式 Lean 形式化 Design 設計書

cid: 69bc0bd9-f1f4-83a4-8143-a5fadcd20045
file: CosmicFormula_Design_Lean_Formal_of_differential_coefficients.md

Design Document for the Lean Formalization of the Cosmic Formula for Differential Coefficients

## 1. 目標

本設計の最終目標は、微分係数の定義

\[
f'(x)=\lim_{u\to 0}\frac{f(x+u)-f(x)}{u}
\]

を宇宙式スタイルの差分核として再構成し、Lean 上で

- 一般 kernel の定義
- limit による derivative の記述
- 冪関数 \( x^d \) への適用
- 宇宙式本体との橋

を段階的に整備することである。

---

## 2. 設計原理

本設計は次の 4 原理に従う。

### 2.1. まず ℝ 上で閉じる

最初から一般の normed field や normed ring へ抽象化しすぎない。  
初版は \( \mathbb{R} \to \mathbb{R} \) で固定する。

### 2.2. exact factorization と limit theorem を分離する

- exact な差分分解
- 極限定理

を別ファイル・別補題群として分離する。

### 2.3. 穿たれた近傍を明示する

\[
\frac{f(x+u)-f(x)}{u}
\]

は \( u=0 \) で未定義的なので、必ず \( \mathcal{N} \) を使う。

### 2.4. 冪関数は一般 kernel の特例として置く

\( x^d \) 専用理論から始めるのでなく、

\[
\Delta_u f(x), \qquad K_f(x,u)
\]

を先に定義し、power case は後から差し込む。

---

## 3. モジュール構成案

以下のような段階的ファイル構成を提案する。

```text
DkMath/
  Analysis/
    CosmicLimitCore.lean
    CosmicDifferenceKernel.lean
    CosmicDerivativeBasic.lean
    CosmicDerivativePower.lean
    CosmicDerivativePolynomial.lean
    CosmicFormulaDerivativeBridge.lean
  Docs/
    CosmicDerivative_Explanation.md
    CosmicDerivative_Design.md
```

各ファイルの責務は次の通り。

### 3.1. `CosmicLimitCore.lean`

- `𝓝[≠]` を用いる極限補題
- `u ↦ 0` の穿たれた極限の基本補題
- `Tendsto` の小道具

### 3.2. `CosmicDifferenceKernel.lean`

- 差分 `delta`
- kernel `cosmicKernel`
- 加法・スカラー倍・積に関する差分恒等式
- power kernel へ進む前の一般骨格

### 3.3. `CosmicDerivativeBasic.lean`

- `HasDerivAt` と kernel limit の対応
- 微分係数の宇宙式的再記述
- 一般関数に対する基本定理

### 3.4. `CosmicDerivativePower.lean`

- \( (x+u)^d-x^d=uG_d(x,u) \)
- `powerKernel`
- `powerKernel` の極限
- `HasDerivAt` for `fun x => x^d`

### 3.5. `CosmicDerivativePolynomial.lean`

- 多項式一般への拡張
- 有限和の微分
- 構造核不変性の多項式版

### 3.6. `CosmicFormulaDerivativeBridge.lean`

- 宇宙式
  \[
  (x+u)^2-x(x+2u)=u^2
  \]

  との関係整理
- 一次 kernel と二次補正核の橋
- 将来の積分設計への導線

---

## 4. 定義設計

まず一般差分を定義する。

```lean
def delta (f : ℝ → ℝ) (x u : ℝ) : ℝ := f (x + u) - f x
```

次に宇宙式的 kernel を定義する。

```lean
def cosmicKernel (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  delta f x u / u
```

これは `u = 0` でも Lean 上は値を持つが、理論的には穿たれた近傍でのみ使う。

### 4.1. 注意

`cosmicKernel f x 0` の値を理論上の意味としては使わない。  
実際の定理は常に

```lean
Tendsto (fun u => cosmicKernel f x u) (𝓝[≠] (0 : ℝ)) ...
```

の形で書く。

---

## 5. 一般補題群

最初に用意すべき補題は次の通り。

### 5.1. 差分の基本補題

```lean
@[simp] theorem delta_zero_right (f : ℝ → ℝ) (x : ℝ) :
    delta f x 0 = 0
```

```lean
theorem delta_add (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y + g y) x u = delta f x u + delta g x u
```

```lean
theorem delta_sub (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y - g y) x u = delta f x u - delta g x u
```

```lean
theorem delta_mul (f g : ℝ → ℝ) (x u : ℝ) :
    delta (fun y => f y * g y) x u
      = f (x + u) * delta g x u + g x * delta f x u
```

この `delta_mul` は product rule への入口になる。

### 5.2. kernel の基本補題

```lean
theorem cosmicKernel_eq (f : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel f x u = (f (x + u) - f x) / u
```

```lean
theorem cosmicKernel_add (f g : ℝ → ℝ) (x u : ℝ) :
    cosmicKernel (fun y => f y + g y) x u
      = cosmicKernel f x u + cosmicKernel g x u
```

ただし `u = 0` の扱いに不要な枝が増えるなら、`hu : u ≠ 0` を仮定した版から始めるのが安全である。

---

## 6. derivative と kernel limit の接続

このファイル群の中核命題は次である。

```lean
theorem hasDerivAt_iff_tendsto_cosmicKernel
    {f : ℝ → ℝ} {x L : ℝ} :
    HasDerivAt f L x ↔
      Tendsto (fun u : ℝ => cosmicKernel f x u)
        (𝓝[≠] (0 : ℝ)) (𝓝 L)
```

これは既存の `HasDerivAt` を宇宙式語彙へ翻訳する基本橋である。

### 6.1. 実装方針

この定理は mathlib 側の既存 characterization を使ってもよいし、独立に組んでもよい。  
ただし初版では「新定義の健全性確認」が主眼なので、既存定理への変換証明として実装するのが良い。

---

## 7. power kernel の exact 設計

power case では kernel を exact に定義する。

```lean
def powerKernel (d : ℕ) (x u : ℝ) : ℝ :=
  ∑ j in Finset.range d,
    ((Nat.choose d (j + 1) : ℝ) * x^(d - 1 - j) * u^j)
```

狙いは次の exact theorem である。

```lean
theorem sub_pow_eq_u_mul_powerKernel (d : ℕ) (x u : ℝ) :
    (x + u)^d - x^d = u * powerKernel d x u
```

### 7.1. 証明方針

証明は次のいずれか。

1. 二項展開から直接組む  
2. 既存の `sub_eq_sum` 型の冪差補題を利用する  
3. `ring_nf` が効く低次数版を先に作り、一般 \( d \) は finite sum で上げる

初版は 1 または 3 が安全。

---

## 8. power kernel の極限定理

exact factorization の次は極限定理である。

```lean
theorem tendsto_powerKernel_zero (d : ℕ) (x : ℝ) :
    Tendsto (fun u : ℝ => powerKernel d x u)
      (𝓝 (0 : ℝ)) (𝓝 ((d : ℝ) * x^(d - 1)))
```

### 8.1. 証明戦略

`powerKernel` は有限和であるから、各項ごとに

- \( j = 0 \) 項は一定値へ
- \( j \ge 1 \) 項は \( u^j \to 0 \)

を示せばよい。

したがって証明は

1. 有限和の `Tendsto`
2. \( u^j \to 0 \)
3. 定数倍・積の `Tendsto`

の合成になる。

この構成は Beam 剥離の厳密版そのものじゃ。

---

## 9. 冪関数の微分定理

上の 2 本

- exact factorization
- kernel limit

が揃えば、微分定理は短く落ちる。

```lean
theorem hasDerivAt_pow_cosmic (d : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y^d) ((d : ℝ) * x^(d - 1)) x
```

### 9.1. 推奨構成

この定理の証明は

1. `hasDerivAt_iff_tendsto_cosmicKernel` へ帰着
2. `cosmicKernel` が `powerKernel` と一致
3. `tendsto_powerKernel_zero` を適用

の 3 段で組むと美しい。

---

## 10. 宇宙式本体との橋

宇宙式本体

\[
(x+u)^2 - x(x+2u) = u^2
\]

は derivative kernel と別物に見えるが、設計上は重要である。

### 10.1. 位置づけ

- `delta` は一次 Gap の差分核
- 宇宙式本体は二次補正核

### 10.2. 目標補題

```lean
theorem cosmic_formula_basic (x u : ℝ) :
    (x + u)^2 - x * (x + 2 * u) = u^2
```

この補題はすぐ証明できるが、意味づけとして

- 微分は一次剥離
- 宇宙式は二次閉包

の対応をドキュメントに明示しておく。

---

## 11. 段階的実装計画

### 11.1. Phase 1. 差分核の基礎

- `delta`
- `cosmicKernel`
- 基本恒等式
- `u ≠ 0` 仮定つきの補題群

### 11.2. Phase 2. derivative bridge

- `hasDerivAt_iff_tendsto_cosmicKernel`
- 線形関数の簡単な例
- `fun x => x`
- `fun x => c`

### 11.3. Phase 3. power kernel

- `powerKernel`
- `sub_pow_eq_u_mul_powerKernel`
- `tendsto_powerKernel_zero`
- `hasDerivAt_pow_cosmic`

### 11.4. Phase 4. 多項式一般

- 有限和
- スカラー倍
- 多項式微分
- 将来の `Polynomial` 型との接続

### 11.5. Phase 5. 宇宙式 bridge

- 一次差分核と二次補正核の関係文書化
- CFBRC / GN 系へ繋ぐ補題の設計

---

## 12. 非目標

初版では次を非目標とする。

- 一般 normed field への即時抽象化
- Fréchet 微分や Banach 空間版
- 積分の本格実装
- 自動微分系の構築
- 全既存微分定理の宇宙式版置換

まずは「定義が立ち、冪関数が通る」ことに集中する。

---

## 13. リスクと回避策

### 13.1. `u = 0` の扱いが混線する

回避策として、定理は常に穿たれた近傍ベースで書く。  
`cosmicKernel` 自体は全域定義でも、意味論は `u ≠ 0` に置く。

### 13.2. power kernel の添字が煩雑

最初は `j` を \( 0 \) から \( d-1 \) まで回す定義で固定する。  
添字変換を増やしすぎない。

### 13.3. exact theorem と limit theorem が混ざる

ファイルを分離し、依存方向を一方通行にする。

```text
DifferenceKernel → DerivativeBasic → DerivativePower → DerivativePolynomial
```

---

## 14. 完成条件

この設計が一応完成したと言える条件は次である。

1. `delta`, `cosmicKernel` が定義済み
2. `hasDerivAt_iff_tendsto_cosmicKernel` が証明済み
3. `sub_pow_eq_u_mul_powerKernel` が証明済み
4. `tendsto_powerKernel_zero` が証明済み
5. `hasDerivAt_pow_cosmic` が通る
6. 宇宙式本体との橋が文書化されている

---

## 15. 最終要約

本設計の核は次の 1 行に尽きる。

\[
\boxed{
f(x+u)-f(x)=u \cdot K_f(x,u)
}
\]

ここで

- 左辺が Big-Core
- \( u \) が Gap
- \( K_f(x,u) \) が Gap を剥いだ Body

である。

そして微分係数は

\[
\boxed{
f'(x)=\lim_{u\to 0} K_f(x,u)
}
\]

である。

Lean 形式化の仕事は、この 2 行を

- exact theorem
- limit theorem
- derivative theorem

の三段構造へ分解し、再利用可能な基盤として固定することにある。
