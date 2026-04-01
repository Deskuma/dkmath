# GN 路線による FLT Branch A descent kernel の孤立化

GN-native isolation of the FLT Branch A descent kernel via Cosmic Formula

## 概要

本稿は、DkMath における Fermat の最終定理（FLT）の Branch A 証明路線において、
非循環 mainline の genuine open kernel を **GN 多項式（Gcd-Next polynomial）の因数分解問題**
として 1 行に孤立させた成果を記録するものである。

具体的には、元来

\[
\exists\, z',\quad x'^p + y^p = z'^p
\]

という **p 乗根の存在問題** として表現されていた open kernel を、
Cosmic Formula の核恒等式を橋として、

\[
\exists\, g',\quad g' \cdot GN_p(g', y) = p^p \cdot (t \cdot s')^p
\]

という **GN Body の一致問題** に翻訳し、全ての橋を no-sorry で確立した。

これにより、DkMath のコア理論である宇宙式（Cosmic Formula）が
FLT 形式化の最後の門に直接関与する構造が実現した。

---

## 1. 背景

### 1.1. FLT Branch A の証明戦略

素数 \(p \ge 5\) に対する Fermat の最終定理

\[
x^p + y^p = z^p,\quad x, y, z \in \mathbb{N},\quad xyz \ne 0
\]

の否定を示すにあたり、DkMath では **無限降下法（infinite descent）** を採用する。
Branch A は \(p \mid (z - y)\) の場合に対応し、normal form として

\[
z - y = p^{p-1} \cdot t^p, \quad
GN_p(z-y,\, y) = p \cdot s^p, \quad
x = p \cdot (t \cdot s)
\]

が確立されている。ここで \(GN_p(x, u)\) は DkMath のコア概念であるGcd-Next 多項式

\[
GN_p(x, u) := \sum_{k=0}^{p-1} \binom{p}{k+1}\, x^k\, u^{p-1-k}
\]

であり、宇宙式（Cosmic Formula）の中核を担う。

### 1.2. Descent の構造

witness prime \(q\) を取る。すなわち \(q \mid s,\; q \ne p\) なる素数で、以下を満たす:

- \(q \mid x,\; q \nmid y,\; q \nmid z,\; q \nmid (z-y)\)
- \(p \mid (q - 1)\)
- \(q^p \mid GN_p(z-y,\, y)\)

\(x' := x / q\) と置くと \(x' = p \cdot (t \cdot s')\)（ここで \(s' = s / q\)）。
**Descent の 1 step** は「\(x'^p + y^p = z'^p\) を満たす smaller counterexample \((x', y, z')\) の構成」である。

### 1.3. 問題の所在

この descent 1 step の核心は、

\[
x'^p + y^p \quad \text{が完全 } p \text{ 乗であること}
\]

の証明にある。古典的には Kummer の円分整数環
\(\mathbb{Z}[\zeta_p]\) での理想分解に依るが、
Lean 4 / Mathlib のインフラでは形式化に年単位を要する。

---

## 2. Kernel Isolation の 3 段階

### 2.1. 第 1 段階: RealizationSeedTarget の二分

`RealizationSeedTarget` は descent seed から smaller counterexample の候補 triple
\((x', y', z')\) を構成する target であり、6 つのフィールドを持つ:

| フィールド | 内容 | 難易度 |
|-----------|------|--------|
| `hSeed` | descent seed | 入力 |
| `x'` | \(x / q\) | concrete |
| `y'` | \(y\) | concrete |
| `z'` | p 乗根 | **hard** |
| `hxMul` | \(x = q \cdot x'\) | concrete |
| `hyEq` | \(y' = y\) | concrete |
| `hzEq` | \(x'^p + y'^p = z'^p\) | **hard** |

6 フィールドのうち genuine に hard なのは `hzEq` のみ。
これを `PthRootTarget` として孤立させた:

\[
\texttt{PthRootTarget}:\quad
\exists\, z',\quad (x/q)^p + y^p = z'^p
\]

残りの quotient side（`x'`, `y'`, `hxMul`, `hyEq`）は concrete に構成可能であり、
橋定理 `RealizationSeed_of_pthRoot` が no-sorry で確立された。

### 2.2. 第 2 段階: Reduced Form への還元

\(x' = p \cdot (t \cdot s')\) の特殊構造を利用し、
`PthRootTarget` を等価な reduced form に変換した:

\[
\texttt{PthRootReducedTarget}:\quad
\exists\, z',\quad p^p \cdot (t \cdot s')^p + y^p = z'^p
\]

双方向の橋定理が no-sorry で確立されている。

**補助 identity.** 元の FLT equation から直接:

\[
z^p = q^p \cdot \bigl(p^p \cdot (t \cdot s')^p\bigr) + y^p
\]

### 2.3. 第 3 段階: GN Reduced Gap Target への翻訳

ここが本稿の核心である。

\(g' := z' - y\) と置くと、**宇宙式の核恒等式**:

\[
(g' + y)^p = g' \cdot GN_p(g',\, y) + y^p \qquad \text{(Big = Body + Gap)}
\]

により、

\[
z'^p = g' \cdot GN_p(g',\, y) + y^p
\]

したがって \(z'^p - y^p = g' \cdot GN_p(g',\, y)\) が成立し、
`PthRootReducedTarget` は以下と等価になる:

\[
\boxed{
\texttt{GNReducedGapTarget}:\quad
\exists\, g',\quad g' \cdot GN_p(g',\, y) = p^p \cdot (t \cdot s')^p
}
\]

橋は `cosmic_id_csr'`（Cosmic Formula: \((x+u)^d = x \cdot GN_d(x,u) + u^d\)）そのものである。

---

## 3. Chain 構造

### 3.1. GN Mainline（非循環 canonical route）

全て no-sorry で確立された chain:

\[
\begin{aligned}
&\texttt{GNReducedGapTarget} & &\text{(GN native open kernel)}\\
&\quad \xrightarrow{\text{cosmic\_id\_csr'}} \texttt{PthRootReducedTarget}\\
&\quad \xrightarrow{x'=p(ts')} \texttt{PthRootTarget}\\
&\quad \xrightarrow{\text{quotient concrete}} \texttt{RealizationSeedTarget}\\
&\quad \to \texttt{WithProvenanceTarget}\\
&\quad \to \texttt{CoreStrong} \to \texttt{PacketPackagingStrong}\\
&\quad \to \texttt{RestoreFromArithmeticStrong}\\
&\quad \to \texttt{StrongProvider} \to \texttt{FringeDescentToRefuter}
\end{aligned}
\]

### 3.2. 矛盾路線（fallback / oracle）

矛盾路線との互換:

\[
\texttt{ContradictionTarget} \to \texttt{PthRootTarget}
\to \texttt{PthRootReduced} \to \texttt{GNReducedGap}
\]

全て vacuously true（矛盾から任意の命題が従う）として no-sorry で確立。

### 3.3. 等価性の完全性

以下の 3 つの target は全て等価であり、双方向の橋が no-sorry で通っている:

\[
\texttt{GNReducedGapTarget}
\iff
\texttt{PthRootReducedTarget}
\iff
\texttt{PthRootTarget}
\]

---

## 4. 実装の詳細

### 4.1. 定理一覧

本成果で実装された主要定理を以下に列挙する。
全て `TriominoCosmicBranchARestoreArithmeticStrong.lean` 内に配置され、
**sorry = 0** である。

#### Kernel Isolation 層

| 定理名 | 型 | 役割 |
|--------|-----|------|
| `PthRootTarget` | `abbrev ... : Prop` | p 乗根の存在 target |
| `PthRootReducedTarget` | `abbrev ... : Prop` | reduced form |
| `GNReducedGapTarget` | `abbrev ... : Prop` | GN native target |

#### 等価性 Bridge

| 定理名 | 方向 |
|--------|------|
| `RealizationSeed_of_pthRoot` | PthRoot → RealizationSeed |
| `PthRoot_of_reduced` | Reduced → PthRoot |
| `PthRootReduced_of_pthRoot` | PthRoot → Reduced |
| `PthRootReduced_of_gnReducedGap` | GNReducedGap → Reduced |
| `GNReducedGap_of_pthRootReduced` | Reduced → GNReducedGap |

#### 一気通貫 Bridge

| 定理名 | 効果 |
|--------|------|
| `WithProvenance_of_pthRoot` | PthRoot → WithProvenance |
| `RestoreFromArithmeticStrong_of_pthRoot` | PthRoot → 全 chain |
| `PthRoot_of_gnReducedGap` | GN → PthRoot |
| `RestoreFromArithmeticStrong_of_gnReducedGap` | GN → 全 chain |

#### 矛盾互換

| 定理名 | 効果 |
|--------|------|
| `PthRoot_of_contradiction` | Contradiction → PthRoot |
| `GNReducedGap_of_contradiction` | Contradiction → GN |

### 4.2. 使用した Cosmic Formula の定理

橋の構成で使用した DkMath コア定理:

- **`cosmic_id_csr'`** (CommSemiring 版):
  \[
  (x + u)^d = x \cdot GN_d(x, u) + u^d
  \]
  `GNReducedGap → PthRootReduced` 方向の橋で、
  \(z' := g' + y\) として \(z'^p = g' \cdot GN_p(g', y) + y^p\) を得る。

- **逆方向** では \(g' := z' - y\) と `Nat.sub_add_cancel` を使い、
  \(z'^p = g' \cdot GN_p(g', y) + y^p\) から \(g' \cdot GN_p(g', y) = p^p(ts')^p\) を導出。

### 4.3. ビルド状態

| ファイル | sorry | ビルド |
|---------|-------|--------|
| `RestoreArithmeticStrong.lean` | 0 | ✅ |
| `StrongProvider.lean` | 0 | ✅ |
| `FringeDescent.lean` | 0 | ✅ |
| `BranchA.lean` | 1 (別系統: NePCoprimeKernel) | ✅ |

---

## 5. 数学的意義

### 5.1. p 乗根問題から GN 因数分解問題への変換

従来、FLT の descent kernel は「\(x'^p + y^p\) が完全 p 乗であるか」という
**存在定理**の顔をしていた。この形式では攻略の手がかりが少ない。

本稿の変換により、kernel は

\[
g' \cdot GN_p(g', y) = p^p \cdot (t \cdot s')^p
\]

という **GN Body の等式**になった。ここでは

- 左辺が **差の冪の因数分解構造**（Cosmic Formula の核概念）
- 右辺が **Branch A descent data の特殊形**

として、DkMath の既存資産（GN の tail 構造、q-adic valuation、Beam/Gap 分解）が
直接適用可能な形になっている。

### 5.2. 「p 乗根を取る」から「新 gap を構成する」へ

数学的に言い換えると:

- **旧形式**: 和 \(x'^p + y^p\) の p 乗根 \(z'\) を取れ
- **新形式**: 差 \(z'^p - y^p\) の因数 \(g'\) と \(GN_p(g', y)\) を構成せよ

後者は宇宙式の言葉でまさに
「新しい gap \(g'\) が存在して、その Body が reduced RHS に一致する」
ことを問うており、これは DkMath における Cosmic Formula の
**Big = Body + Gap** 分解の直接的な応用である。

### 5.3. GN が家主、q-adic/Hensel は補助

本稿の構造により、今後の攻略は:

- **GN mainline**: `GNReducedGapTarget` を `g' * GN p g' y` の因数分解構造で攻める
- **q-adic/Hensel**: GN の q-adic valuation が集中する側補題として使用
- **Kummer**: 必要になった場合の escalation route として保持

という **GN が家主、q-adic は補助兵** の構成が自然に確立される。

---

## 6. 今後の展望

### 6.1. q-adic 剥離層の定理化

\(q^p \mid GN_p(z-y, y)\) と \(q \nmid (z-y)\) から、
q の power が GN 側に集中する構造を必要条件補題群として固定する。

### 6.2. GN 局所存在の攻略

関数 \(F(g) := g \cdot GN_p(g, y) - p^p(ts')^p\) の零点 \(g'\) を、
Branch A descent data の特殊構造を活用して構成する。
Hensel 的手法は、この GN-native function に対する**特殊形専用の局所持ち上げ**として適用する。

### 6.3. Cosmic Formula の応用展開

GN が FLT 形式化の最後の門に直接関与したことは、
DkMath のコア理論としての宇宙式の有効性を実証するものである。
GN の tail 構造（GTail）、多変数化（Cell 空間）、
および高次元宇宙式への自然な拡張が、今後の研究の基盤となる。

---

## 付録 A. 記号表

| 記号 | 定義 | 備考 |
|------|------|------|
| \(GN_p(x, u)\) | \(\sum_{k=0}^{p-1} \binom{p}{k+1} x^k u^{p-1-k}\) | Gcd-Next 多項式 |
| \(g'\) | \(z' - y\) | descent 後の新 gap |
| \(s'\) | \(s / q\) | witness prime で割った quotient |
| \(x'\) | \(x / q = p \cdot (t \cdot s')\) | descent 後の新 x |

## 付録 B. 開発ブランチ

- ブランチ: `dev/FLT-BAFCT-260401-v2`
- 日付: 2026年4月1日〜2日
- 対象ファイル: `DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestoreArithmeticStrong.lean`

---

VSCode Style Markdown and \(\LaTeX\) Extensions

This document uses VSCode style markdown with \(\LaTeX\) extensions for mathematical notation.
Ensure your markdown viewer supports these features for optimal readability.
