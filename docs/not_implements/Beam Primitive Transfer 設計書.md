# Beam Primitive Transfer 設計書

## 1. 概要

本設計書では、差の冪構造

\[
(x+u)^d - x^d
\]

に対して、因数分解および p-進付値 \( \nu_p \) を用いた解析を行い、

- 差分に現れる素因子の起源
- 境界（Gap）と内部（Beam）の分離
- 原始素因子の内部化

を体系的に整理する。

特に、差分に現れる素因子が、境界ではなく内部多項式 \( GN(d,x,u) \) に帰着する構造を明確化する。

---

## 2. 基本定義

### 2.1 差分構造

\[
\Delta_d(x,u) := (x+u)^d - x^d
\]

### 2.2 Beam 多項式

\[
GN(d,x,u) =
\sum_{k=0}^{d-1}
\binom{d}{k+1} x^k u^{d-1-k}
\]

### 2.3 基本分解（Gap-Body 分解）

\[
(x+u)^d - x^d = u \cdot GN(d,x,u)
\]

ここで

- Gap := \( u \)
- Beam := \( GN(d,x,u) \)

とする。

---

## 3. p-進付値

### 3.1 定義

\[
\nu_p(n) := \max \{ k \in \mathbb{Z}_{\ge 0} \mid p^k \mid n \}
\]

### 3.2 基本性質

\[
\nu_p(ab) = \nu_p(a) + \nu_p(b)
\]

---

## 4. 付値分解

### 命題 4.1（valuation 分解）

\[
\nu_p\bigl((x+u)^d - x^d\bigr) =
\nu_p(u) + \nu_p(GN(d,x,u))
\]

### 証明

\[
(x+u)^d - x^d = u \cdot GN(d,x,u)
\]

に対して、積の付値性質を適用する。

---

## 5. 因子移送補題

### 命題 5.1（境界非整除なら内部整除）

\[
p \mid ((x+u)^d - x^d), \quad p \nmid u
\Rightarrow
p \mid GN(d,x,u)
\]

### 証明

Euclid の補題より直ちに従う。

---

## 6. Beam-新規素因子

### 定義 6.1（Beam-新規素因子）

素数 \( p \) が \( \Delta_d(x,u) \) の Beam-新規素因子であるとは：

\[
p \mid \Delta_d(x,u), \quad p \nmid u
\]

を満たすこと。

### 拡張定義（原始版）

\[
p \mid \Delta_d(x,u),
\quad
p \nmid \Delta_m(x,u) \quad (1 \le m < d)
\]

---

## 7. 内部化定理

### 定理 7.1（Beam Primitive Transfer）

\[
p \mid ((x+u)^d - x^d), \quad p \nmid u
\Rightarrow
p \mid GN(d,x,u)
\]

### 解釈

境界に属さない素因子は、必ず Beam 内部に属する。

---

## 8. d = 3 の特別化

### 8.1 分解

\[
z^3 - y^3 = (z-y)(z^2 + zy + y^2)
\]

### 8.2 Beam 同一視

\[
GN(3,z-y,y) = z^2 + zy + y^2
\]

### 8.3 命題

\[
p \mid (z^3 - y^3), \quad p \nmid (z-y)
\Rightarrow
p \mid z^2 + zy + y^2
\]

### 8.4 付値版

\[
\nu_p(z^3-y^3) =
\nu_p(z-y) + \nu_p(z^2+zy+y^2)
\]

---

## 9. 原始素因子との接続

### 観点

- 差分に現れる素因子の「存在」は Zsigmondy 型定理が担う
- 本構造は「その素因子がどこに属するか」を決定する

### 結論

原始素因子 \( p \) が

\[
p \nmid u
\]

を満たす場合、

\[
p \mid GN(d,x,u)
\]

となるため、

> 原始素因子は Beam 内部に着地する

---

## 10. 構造図

\[
(x+u)^d - x^d =
\underbrace{u}_{Gap}
\cdot
\underbrace{GN(d,x,u)}_{Beam}
\]

\[
\nu_p(\text{差分}) =
\nu_p(\text{Gap})
+
\nu_p(\text{Beam})
\]

---

## 11. 意味論的解釈

- Gap は外部から与えられる構造
- Beam は内部干渉により生成される構造
- p-進付値は、その寄与を指数層で分解する

したがって

> p-進付値は差分構造の「素数方向の層分解」である

---

## 12. 今後の展開

- Zsigmondy 定理との統合
- GN 多項式の平方自由性（squarefree）との接続
- FLT および ABC 予想への応用
- valuation を用いた原始性の再定義

---
