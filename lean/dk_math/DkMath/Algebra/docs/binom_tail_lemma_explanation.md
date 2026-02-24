# BinomTail.lean 解説

## 概要

`BinomTail.lean` は、二項展開における **尾項（k ≥ 2 部分）** が必ず $a^2$ を因子に持つことを一般化した補題群である。

特に次の構造を形式化している：

$$
(a+b)^n = b^n + n b^{n-1} a + a^2 H
$$

ここで $H$ は明示的な有限和で与えられる。

この補題は、フェルマー型の議論や差の冪の因数分解、宇宙式構造の $u^2$ 因子抽出などで再利用される基盤補題である。

---

## 数学的内容

### 1. 二項展開の分解

二項定理より

$$
(a+b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}
$$

これを

- $k=0$ の項
- $k=1$ の項
- $k \ge 2$ の項

に分解すると：

$$
(a+b)^n = b^n + n b^{n-1} a + \sum_{k=2}^{n} \binom{n}{k} a^k b^{n-k}
$$

ここで $k = x+2$ と置き換えると

$$
\sum_{k=2}^{n} \binom{n}{k} a^k b^{n-k} =
\sum_{x=0}^{n-2} \binom{n}{x+2} a^{x+2} b^{n-(x+2)}
$$

さらに

$$
a^{x+2} = a^2 a^x
$$

より

$$
(a+b)^n = b^n + n b^{n-1} a + a^2
\sum_{x=0}^{n-2} \binom{n}{x+2} a^x b^{n-2-x}
$$

従って尾項は必ず $a^2$ を因子に持つ。

---

## Lean における実装

### 1. CommSemiring 版

```lean
lemma add_pow_tail_exists
  [CommSemiring α] (a b : α) {n : ℕ} (hn : 2 ≤ n) :
  ∃ H : α,
    (a + b)^n = b^n + (n : α) * b^(n-1) * a + a^2 * H
```

この補題では、尾項部分を明示的な有限和として witness $H$ を返す。

ポイント：

- `add_pow` により二項展開を取得
- `k ≥ 2` 部分を `Finset.Ico` → `Finset.range` に再添字化
- $a^{x+2}$ から $a^2$ を因数分解

---

### 2. Nat 上の割り切り版

```lean
lemma binom_tail_nat_dvd
  (u y : ℕ) {n : ℕ} (hn : 2 ≤ n) :
  u^2 ∣ ((u+y)^n - y^n - n*y^(n-1)*u)
```

この証明は `add_pow_tail_exists` を直接利用する：

1. 存在補題から witness $H$ を取得
2. 等式を変形して

   $$
   (u+y)^n - y^n - n y^{n-1} u = u^2 H
   $$

3. `use H` により割り切りを即座に示す

この形により、Nat 版では二項展開を再構成する必要がなくなり、証明は非常に短く保守性が高い。

---

## この補題の役割

この補題は以下の場面で再利用される：

- フェルマー型不可能性証明の補助
- 差の冪の構造解析
- $u^2$ 因子の抽出
- 宇宙式における二次厚みの分離

特に

$$
(u+y)^n - y^n - n y^{n-1} u
$$

の形は多くの数論的議論で現れ、二次以上の寄与を分離するための標準形となる。

---

## 設計思想

- 抽象層（CommSemiring）で構造を確立
- 具体層（Nat）で割り切りへ橋渡し
- 再利用性を優先し、二項展開の再証明を避ける

このモジュールは、二項展開の尾部構造を「共通道具」として外部化することを目的としている。

---

VSCode Style Markdown and \(\LaTeX\) Extensions

This document uses VSCode style markdown with \(\LaTeX\) extensions for mathematical notation.
Ensure your markdown viewer supports these features for optimal readability.
