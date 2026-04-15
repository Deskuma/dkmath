# 微小単位による平方閉包構造と補正核の一般理論

General theory of square closure structures and correction kernels using infinitesimal units

## 1. 概要

本稿では、二次構造
\[
N = P(P + 2\varepsilon)
\]
と平方完成
\[
\mathrm{Big} = (P + \varepsilon)^2
\]
の関係を統一的に扱い、その差分が微小単位 \(\varepsilon\) の冪として現れることを示す。

特に、
\[
(P + \varepsilon)^2 - P(P + 2\varepsilon) = \varepsilon^2
\]
という恒等式により、「わずかな単位の導入」が閉包構造において高次補正として現れる原理を明確化する。

---

## 2. 基本定義

### 2.1 微小単位

\[
\varepsilon \in \mathbb{R}
\]

を「微小単位」と呼ぶ。

### 2.2 Body 構造

\[
N := P(P + 2\varepsilon)
\]

を Body と呼ぶ。

### 2.3 Big（平方閉包）

\[
\mathrm{Big} := (P + \varepsilon)^2
\]

を平方閉包構造と呼ぶ。

### 2.4 閉包差分（Gap 核）

\[
\Delta(\varepsilon) := \mathrm{Big} - N
\]

---

## 3. 基本定理（平方閉包差分）

次が成り立つ：

\[
(P + \varepsilon)^2 - P(P + 2\varepsilon) = \varepsilon^2
\]

すなわち

\[
N + \varepsilon^2 = (P + \varepsilon)^2
\]

### 証明

展開により

\[
(P + \varepsilon)^2 = P^2 + 2\varepsilon P + \varepsilon^2
\]

\[
P(P + 2\varepsilon) = P^2 + 2\varepsilon P
\]

よって差分は

\[
\varepsilon^2
\]

である。□

---

## 4. 解釈

### 4.1 一次項の一致と二次差分

Body と Big は一次項まで完全に一致し、差は常に

\[
\varepsilon^2
\]

という二次項のみである。

### 4.2 微小単位の効果

微小な変位

\[
P \mapsto P + \varepsilon
\]

は、閉包構造においては単なる一次変化ではなく

\[
\varepsilon^2
\]

という二次補正として現れる。

---

## 5. 幾何学的解釈

- \(P(P + 2\varepsilon)\)：長方形
- \((P + \varepsilon)^2\)：正方形

両者の差は

\[
\varepsilon \times \varepsilon = \varepsilon^2
\]

であり、これは正方形の角に対応する最小セルである。

---

## 6. 特殊例（整数単位）

\[
\varepsilon = 1
\]

とすると

\[
N = P(P + 2)
\]

\[
N + 1 = (P + 1)^2
\]

となる。

従って従来の式は、一般式の特殊場合である。

---

## 7. 一般次元への拡張

一般に \(d \in \mathbb{N}\) に対し、

\[
(P + \varepsilon)^d - \mathrm{Body}_d(P,\varepsilon) = \varepsilon^d
\]

となる構造を考える。

このとき

- \(\varepsilon\)：単位長
- \(\varepsilon^d\)：\(d\) 次元補正核

である。

---

## 8. 原理（微小単位閉包原理）

微小単位 \(\varepsilon\) による構造変位は、閉包構造においては単純な一次差ではなく、次元 \(d\) に応じて

\[
\varepsilon^d
\]

の補正核として現れる。

したがって、任意の閉包構造において

\[
\text{微小変位} \Rightarrow \text{高次補正}
\]

が成立する。

---

## 9. 結論

\[
N = P(P + 2\varepsilon)
\]

は未閉包構造であり、

\[
\varepsilon^2
\]

を加えることで平方閉包

\[
(P + \varepsilon)^2
\]

へ到達する。

このとき \(\varepsilon^2\) は単なる補正ではなく、

- 閉包に必要な最小単位
- Gap 核
- 相対完成境界

として機能する。

---
