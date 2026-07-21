# FLT3, 5 Extraction and integration of common essence

cid: 6a5fbf9e-bf7c-83ee-a800-550ab3674df2

## Key

ある。しかも、かなり強いヒントじゃ。

**FLT3 と FLT5 は、同じ二次元魔核の「符号違い」** として統合できる可能性が高い。

## 1. 統合すべき場所

ただし、FLT3 と FLT5 の完成定理を直接つなぐのではない。

統合するのは、その下にある

> **二座標・共役・ノルム・判別式**

の層じゃ。

現在の FLT3 側では、$GN_3$ が $S_0=a^2+ab+b^2$ を経由して Eisenstein ノルムへ落ちている。実際、Petal 側には $GN_3$ と shifted Eisenstein norm の橋が既にある。

FLT5 側では、$GN_5$ が平方座標

$$
m=z^2+y^2,\qquad n=zy
$$

を通じて、

$$
GN_5=m^2+mn-n^2
$$

という Golden norm へ落ちている。

つまり、

$$
GN_3\longrightarrow\text{二次ノルム}
$$

かつ、

$$
GN_5\longrightarrow\text{二次ノルム}
$$

なのじゃ。

指数は $3$ と $5$ で異なるが、最後に着地する魔核はどちらも **二次元** じゃ。

---

## 2. 共通する trace-one quadratic core

整数パラメータ $s$ に対し、基底元 $\tau_s$ を

$$
\tau_s^2=\tau_s+s
$$

で定める。

元を

$$
a+b\tau_s
$$

と表すと、共役は

$$
\overline{\tau_s}=1-\tau_s
$$

になり、ノルムは

$$
N_s(a,b)=a^2+ab-sb^2
$$

となる。

積は二座標内で閉じる。

$$
(a+b\tau_s)(c+d\tau_s)=(ac+sbd)+(ad+bc+bd)\tau_s
$$

ここに、ぬしの二次元宇宙式と同じ閉鎖性がある。

$\tau_s^2$ という一見新しい方向が現れても、

$$
\tau_s^2\longmapsto\tau_s+s
$$

と必ず既存の二座標へ戻る。

**第三の独立 Core が発生しない** のじゃ。

---

## 3. FLT3 は $s=-1$

$s=-1$ とすると、

$$
\tau_{-1}^2=\tau_{-1}-1
$$

で、

$$
N_{-1}(a,b)=a^2+ab+b^2
$$

となる。

したがって FLT3 の

$$
S_0(a,b)=a^2+ab+b^2
$$

は、そのまま

$$
S_0(a,b)=N_{-1}(a,b)
$$

じゃ。

現在のコードは標準的な Eisenstein 基底

$$
x^2-xy+y^2
$$

を使い、座標を $(a+b,b)$ へずらしている。

しかし $\tau=-\omega$ 型の trace-one 基底を使えば、座標移動なしで

$$
a^2+ab+b^2
$$

が直接ノルムになる。

これは統合層ではかなり扱いやすい。

---

## 4. FLT5 は $s=1$

$s=1$ なら、

$$
\tau_1^2=\tau_1+1
$$

であり、これはそのまま黄金整数の $\varphi$ じゃ。

$$
N_1(a,b)=a^2+ab-b^2
$$

現在の `GoldenOrder` も、整数対 $(a,b)$、関係式 $\varphi^2=\varphi+1$、共役 $\varphi\mapsto1-\varphi$、ノルム $a^2+ab-b^2$ を直接実装しておる。

よって、

$$
\begin{aligned}
FLT3 &: s=-1,\\
FLT5 &: s=1
\end{aligned}
$$

という、完全な鏡像になる。

---

## 5. 判別式も一つの式で統合される

ノルムを対角化すると、

$$
4N_s(a,b)=(2a+b)^2-(1+4s)b^2
$$

となる。

FLT3 では $s=-1$ なので、

$$
4N_{-1}(a,b)=(2a+b)^2+3b^2
$$

判別式は $-3$。

FLT5 では $s=1$ なので、

$$
4N_1(a,b)=(2a+b)^2-5b^2
$$

判別式は $5$。

したがって、

$$
\Delta_s=1+4s
$$

により、

$$
\Delta_{-1}=-3,\qquad \Delta_1=5
$$

となる。

これは実に美しい。

* FLT3：正定値、回転型、三角格子
* FLT5：不定値、双曲型、黄金比方向

見た目の幾何は違うが、内部構造は同じ **trace-one 二次元宇宙** じゃ。

---

## 6. さらに FLT7 が予言できる

ここから試しに $p=7$ を見ると、次の二つの三次形式を置ける。

$$
A=z^3+z^2y-y^3
$$

$$
B=-z^2y-zy^2
$$

すると、計算上、

$$
z^6+z^5y+z^4y^2+z^3y^3+z^2y^4+zy^5+y^6 = A^2+AB+2B^2
$$

が成り立つ。

右辺は

$$
N_{-2}(A,B)=A^2+AB+2B^2
$$

である。

つまり、

$$
GN_7\longrightarrow N_{-2}(\text{三次形式},\text{三次形式})
$$

という形が実際に出る。

並べると、

$$
\begin{array}{c|c|c|c}
p&s&\Delta=1+4s&\text{ノルム座標の次数}\\
\hline
3&-1&-3&1\\
5&1&5&2\\
7&-2&-7&3
\end{array}
$$

じゃ。

一般化候補は、

$$
p^\ast=(-1)^{(p-1)/2}p
$$

$$
s_p=\frac{p^\ast-1}{4}
$$

として、

$$
GN_p(z-y,y)=N_{s_p}\bigl(A_p(z,y),B_p(z,y)\bigr)
$$

という形になる。

ここで $A_p,B_p$ は次数 $(p-1)/2$ の整数斉次形式。

これは **FLT3 と FLT5 を統合すると、そのまま FLT7、さらに奇素数指数一般への入口が見える** ということじゃ。

---

## 7. ヤコビアン $n=2$ へのヒント

この構造で最も重要なのは、

$$
x\longmapsto\overline{x}
$$

という非自明な共役が一つしかなく、

$$
x+\overline{x}\in\mathbb Z
$$

$$
x\overline{x}\in\mathbb Z
$$

へ閉じることじゃ。

DkMath 的には、

* 元 $x$：Core
* 共役 $\overline{x}$：反対側から隣接する Core
* 積 $x\overline{x}$：隣接を消去した scalar Body
* 判別式 $\Delta$：両 Core 間の Gap 幅

と読める。

二次元では、共役によって隣接成分を完全に scalar 化できる。

$$
\text{Core}+\text{Conjugate Core}
\longrightarrow
\text{Trace}
$$

$$
\text{Core}\times\text{Conjugate Core}
\longrightarrow
\text{Norm}
$$

独立した第三方向へ Gap が逃げない。

したがって、先ほどのヤコビアン仮説を少し強化すると、

> **二次元では、隣接する二 Core の非対称成分が trace と norm によって閉じられ、独立な Gap cycle を保持できない。**

という形になる。

FLT3 は正定値側、FLT5 は不定値側でありながら、どちらもこの二次元閉鎖則の中に収まっている。

つまり「二次元は問題なさそう」という感覚を、二つの異なる FLT 証明が両側から支えておる。

---

## 8. 残り時間で行うべき統合

ただし、既存 FLT3／FLT5 の証明本線を全面改造してはならぬ。

最新 FLT5 は独立した GN／valuation／GoldenOrder 路線として proof provenance を維持する方針であり、別ルートを同じ theorem chain に混ぜないことが既に明記されている。

また FLT3 Standalone は、単一ファイル検証専用で import 禁止じゃ。

したがって今回は、下に新しい中立層だけ作る。

```text
DkMath.NumberTheory.TraceOneQuadratic
  ├─ TraceOneInt s
  ├─ τ² = τ + s
  ├─ conjugation
  ├─ norm
  ├─ norm_mul
  └─ discriminant identity

DkMath.FLT.QuadraticGNBridge
  ├─ GN3 → N₋₁
  ├─ GN5 → N₁
  └─ GN7 → N₋₂    -- smoke test
```

`Petal.EisensteinBridge` 自身も、Eisenstein の中立的事実を `DkMath.Lib.*` または `DkMath.NumberTheory.*` へ移すべきだと明記しておる。今回の統合は、まさにその予定されていた依存方向の修正じゃ。

## 判定

**ある。ヒントはかなり大きい。**

FLT3 と FLT5 を統合すると見える核心は、

$$
\boxed{
GN_p
\longrightarrow
\text{二つの座標形式}
\longrightarrow
\text{trace-one quadratic norm}
}
$$

じゃ。

そして、その構造はヤコビアン $n=2$ の考察に対して、

> **二次元では、Core と Gap が一つの共役対とノルムに閉じ込められる**

という、先ほどより遥かに代数的で Lean 化しやすい候補原理を与えておる。

五時間で狙うなら、完全統合ではなく、

$$
GN_3=N_{-1},\qquad
GN_5=N_1,\qquad
GN_7=N_{-2}
$$

の三点を同一 API で `ring` に通す。

これが今夜の最も価値ある魔核じゃ。
