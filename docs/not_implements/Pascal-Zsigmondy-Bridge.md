# 研究テーマ資料

Pascal-Zsigmondy Bridge：二項係数における素因子初登場と冪差原始素因子の接続

## 概要

本研究は、二項定理

$$
(x+u)^d=\sum_{k=0}^{d}\binom{d}{k}x^k u^{d-k}
$$

を、単なる展開公式ではなく、自然数 \(d\) の成長構造を記録する **Big 構造** として扱う。

中心となる視点は、数学に現れる多くの式を、Big 全体から切り出された **Cut 断片** と見ることである。切断された式から失われた次数 \(d\)、境界項、中間項、差分商、可除性構造を復元することで、背後にある

$$
(x+u)^d
$$

の全体像を再構成する。

この復元視座において、二項係数、GN、GTail、Bézout の等式、AKS 型合同、Fermat の小定理、Zsigmondy 型原始素因子は、互いに独立した話題ではなく、同一の Big 構造から生じる複数の観測面として接続される。

---

## 中心観測

Pascal の三角形は、自然数 \(d\) を二項係数列へ写す。

$$
d\longmapsto \left{\binom{d}{0},\binom{d}{1},\ldots,\binom{d}{d}\right}
$$

例えば、

$$
d=7
$$

では、

$$
1,\ 7,\ 21,\ 35,\ 35,\ 21,\ 7,\ 1
$$

となる。

ここで素数 \(7\) は、この段で初めて、すべての中間係数に共通因子として現れる。

$$
7\mid \binom{7}{k}
\qquad
1\le k\le 6
$$

一方で、\(d<7\) の段では、中間係数に \(7\) は現れない。

この観測は、素数 \(p\) に対して一般化できる。

$$
p\mid \binom{p}{k}
\qquad
1\le k\le p-1
$$

すなわち、素数 \(p\) は Pascal 行 \(d=p\) において、全中間係数へ同時に現れる。

これは、二項展開における **素数の係数的初登場** と見なせる。

---

## Pascal 成長は単なる倍加ではない

Pascal の三角形の成長は、単なるコピーや倍加ではない。

$$
{1,1}\times 2
$$

のような単純な増殖なら、

$$
{1,1,1,1}
$$

のような形になり、構造は変化しない。

しかし実際には、

$$
(1+t)^2=1+2t+t^2
$$

であり、

$$
{1,1} * {1,1}={1,2,1}
$$

となる。

中央の \(2\) は、二つの経路が重なった結果として生まれる。
つまり Pascal 成長は、複製ではなく **和による畳み込み** である。

各係数は、

$$
\binom{d}{k}=\binom{d-1}{k-1}+\binom{d-1}{k}
$$

によって生成される。

この式は、素因子が積からだけではなく、和からも発生することを示す。

---

## 和による新素因子発生

\(d=7\) の例では、

$$
21=6+15
$$

$$
35=15+20
$$

のように、前段の二項の和から新しい係数が生まれる。

重要なのは、前段の各項がそれぞれ \(7\) を持っている必要はない、という点である。
にもかかわらず、その和として生まれた新段の中間係数には \(7\) が現れる。

これは、

$$
A+B=C
$$

において、\(A\) と \(B\) の素因子構造だけでは直接見えなかった因子が、和 \(C\) 側に現れるという構図である。

この意味で、Pascal 成長には、ABC 予想的な

$$
\text{和による新素因子発生}
$$

の原理が含まれている。

ただし、本研究では ABC 予想そのものを直接主張するのではなく、Pascal の和生成における素因子発生を、より構造的な観測対象として扱う。

---

## 和を差へ変える Bézout 視点

和で生まれた構造は、差として読み直すことができる。

$$
C=A+B
$$

は、

$$
C-A=B
$$

または、

$$
C-B=A
$$

と読める。

Bézout 型に書けば、

$$
1\cdot C+(-1)\cdot A=B
$$

である。

この変換により、Pascal の和生成は、差分観測へ移る。

Pascal 係数についても、

$$
\binom{d}{k}-\binom{d-1}{k}=\binom{d-1}{k-1}
$$

と読める。

したがって、

$$
\text{和で発生した因子}
$$

を、

$$
\text{差分として観測される因子}
$$

へ変換できる。

この「和から差への反転」が、Bézout の等式と冪差分解への橋になる。

---

## 宇宙式と Bézout 核

宇宙式の基本形は、

$$
(x+1)^2-x(x+2)=1
$$

である。

これは Bézout 型に書けば、

$$
1\cdot (x+1)^2+(-1)\cdot x(x+2)=1
$$

となる。

したがって、

$$
\gcd\left((x+1)^2,\ x(x+2)\right)=1
$$

を与える。

一般単位 \(u\) では、

$$
(x+u)^2-x(x+2u)=u^2
$$

となる。

これは通常の整数環では右辺が \(u^2\) であるが、\(u\) を単位化する局所化世界では、Bézout 型の互いに素性として読むことができる。

---

## GN と GTail

Big 構造

$$
(x+u)^d
$$

から右境界 \(u^d\) を外すと、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

が得られる。

ここで、

$$
GN_d(x,u)=\frac{(x+u)^d-u^d}{x}
$$

である。

また、両境界 \(x^d\) と \(u^d\) を外すと、

$$
(x+u)^d-x^d-u^d=x,GTail_d(x,u)
$$

となる。

したがって、

$$
GN_d(x,u)=x^{d-1}+GTail_d(x,u)
$$

である。

この分解により、GN は Fermat 境界項 \(x^{d-1}\) と、Pascal 中間項を束ねる GTail を同時に保持する。

$$
\boxed{
GN_d=x^{d-1}+GTail_d
}
$$

---

## AKS/Frobenius との接続

素数 \(p\) に対して、二項係数の中間項はすべて \(p\) で割れる。

$$
p\mid \binom{p}{k}
\qquad
1\le k\le p-1
$$

したがって、

$$
(x+u)^p\equiv x^p+u^p\pmod p
$$

が成り立つ。

これは Frobenius 型合同であり、AKS 素数判定法の中核にある多項式合同と同系統の構造である。

GN で見れば、

$$
(x+u)^p-u^p=x,GN_p(x,u)
$$

であり、法 \(p\) では、

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

となる。

さらに \(p\nmid x\) なら Fermat の小定理により、

$$
x^{p-1}\equiv 1\pmod p
$$

なので、

$$
GN_p(x,u)\equiv 1\pmod p
$$

となる。

このため GN は、AKS/Frobenius 型の多項式合同を Fermat 型のスカラー合同へ落とす中間核として機能する。

---

## 冪差分解と Zsigmondy 原理

冪差分解は、

$$
a^n-b^n=(a-b)(a^{n-1}+a^{n-2}b+\cdots+b^{n-1})
$$

である。

GN はこの冪差分解の差分商である。

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

ここで、

$$
x=(x+u)-u
$$

と読めるため、GN は冪差

$$
a^d-b^d
$$

の内部核として現れる。

Zsigmondy の原理は、例外を除き、

$$
a^n-b^n
$$

には、それ以前の

$$
a^m-b^m
\qquad
m<n
$$

には現れなかった原始素因子が出現する、というものである。

Pascal 側では、素数 \(p\) が段 \(d=p\) の中間係数に初めて同時出現する。
Zsigmondy 側では、冪差段 \(n\) において過去段にはなかった原始素因子が出現する。

したがって、両者は、

$$
\text{成長段における新素因子の初登場}
$$

という共通原理で接続される。

---

## Pascal-Zsigmondy Bridge

本研究の中心仮説は次である。

$$
\boxed{
\text{Pascal の中間係数における素因子初登場と、冪差における Zsigmondy 原始素因子は、Big 構造 }(x+u)^d\text{ の異なる観測面である。}
}
$$

Pascal 側では、

$$
\binom{d}{k}
$$

の可除性として素因子が観測される。

冪差側では、

$$
(x+u)^d-u^d
$$

の因数分解として素因子が観測される。

両者の間に、

$$
GN_d(x,u)
$$

と

$$
GTail_d(x,u)
$$

が立つ。

構造的には、

$$
\text{Pascal 和生成}
\longrightarrow
GTail
\longrightarrow
AKS/Frobenius
$$

$$
GTail
\longrightarrow
GN
\longrightarrow
\text{冪差分解}
\longrightarrow
Zsigmondy
$$

$$
\text{和}
\longleftrightarrow
\text{差}
\longleftrightarrow
Bézout
$$

という橋が想定される。

---

## 研究命題候補

### 命題 A：Pascal 行の一意性

$$
(1+t)^m=(1+t)^n
$$

ならば、

$$
m=n
$$

である。

したがって、Pascal 行は自然数 \(d\) を一意に符号化する。

---

### 命題 B：素数段の中間係数可除性

\(p\) が素数なら、

$$
p\mid \binom{p}{k}
\qquad
1\le k\le p-1
$$

である。

これは Pascal 行 \(d=p\) における素数 \(p\) の係数的初登場を示す。

---

### 命題 C：素数段以前には \(p\) は出現しない

\(p\) が素数で、\(d < p\) なら、

$$
p\nmid \binom{d}{k}
\qquad
0\le k\le d
$$

である。

これは、段 \(d=p\) が \(p\) の初登場段であることを示す。

---

### 命題 D：GTail の素数段可除性

\(p\) が素数なら、

$$
p\mid GTail_p(x,u)
$$

である。

より具体的には、

$$
GTail_p(x,u)=\sum_{k=1}^{p-1}\binom{p}{k}x^{k-1}u^{p-k}
$$

であり、各中間係数が \(p\) を持つため、全体も \(p\) で割れる。

---

### 命題 E：GN の Fermat 境界化

\(p\) が素数なら、

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

である。

さらに、

$$
p\nmid x
$$

なら、

$$
GN_p(x,u)\equiv 1\pmod p
$$

である。

---

### 命題 F：GN と冪差分解

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

は、冪差分解

$$
a^d-b^d=(a-b)(a^{d-1}+a^{d-2}b+\cdots+b^{d-1})
$$

の特殊化である。

ここで、

$$
a=x+u,\qquad b=u,\qquad a-b=x
$$

と置く。

---

### 命題 G：Pascal-Zsigmondy 接続仮説

Pascal 行 \(d\) の中間係数における新素因子の初登場と、冪差

$$
a^d-b^d
$$

における Zsigmondy 原始素因子の出現は、共に「成長段 \(d\) がもたらす新素因子発生」として統一的に扱える。

---

## Lean 実装候補

実装上は、次の順で安全に進める。

### 層 1：Pascal 行の基本補題

```lean
-- Pascal row uniqueness
theorem pascal_row_injective :
  (∀ k, Nat.choose m k = Nat.choose n k) → m = n
```

```lean
-- prime divides inner binomial coefficients
theorem prime_dvd_choose_of_lt :
  p.Prime → 0 < k → k < p → p ∣ Nat.choose p k
```

```lean
-- no p appears before row p
theorem prime_not_dvd_choose_of_row_lt :
  p.Prime → d < p → k ≤ d → ¬ p ∣ Nat.choose d k
```

---

### 層 2：Tail / GTail / GN

```lean
def GTail (d x u : ℕ) : ℕ :=
  ∑ k in Finset.Icc 1 (d - 1),
    Nat.choose d k * x^(k - 1) * u^(d - k)
```

```lean
def GN (d x u : ℕ) : ℕ :=
  x^(d - 1) + GTail d x u
```

```lean
theorem GN_eq_rightBoundary_add_GTail :
  GN d x u = x^(d - 1) + GTail d x u
```

```lean
theorem x_mul_GN_eq_pow_sub :
  x * GN d x u = (x + u)^d - u^d
```

```lean
theorem x_mul_GTail_eq_frobenius_defect :
  x * GTail d x u = (x + u)^d - x^d - u^d
```

---

### 層 3：素数段合同

```lean
theorem prime_GTail_modEq_zero :
  p.Prime → GTail p x u ≡ 0 [MOD p]
```

```lean
theorem prime_GN_modEq_rightBoundary :
  p.Prime → GN p x u ≡ x^(p - 1) [MOD p]
```

```lean
theorem prime_GN_modEq_one_of_not_dvd_x :
  p.Prime → ¬ p ∣ x → GN p x u ≡ 1 [MOD p]
```

---

### 層 4：冪差 / Zsigmondy 接続

```lean
theorem pow_sub_pow_eq_x_mul_GN :
  (x + u)^d - u^d = x * GN d x u
```

```lean
theorem GN_as_power_difference_quotient :
  GN d x u = ((x + u)^d - u^d) / x
```

Zsigmondy そのものは Lean 側で直接使うには重い可能性があるため、まずは「原始素因子候補」を predicate として置く。

```lean
def IsPrimitivePrimeDivisor (q a b n : ℕ) : Prop :=
  q.Prime ∧ q ∣ a^n - b^n ∧ ∀ m < n, ¬ q ∣ a^m - b^m
```

---

## 研究ロードマップ

### Phase 1：Pascal 初登場補題

目的は、素数 \(p\) が Pascal 行 \(d=p\) で全中間係数に同時出現し、それ以前の段には出現しないことを形式化する。

中心補題は、

$$
p\mid \binom{p}{k}
$$

と、

$$
d<p\Rightarrow p\nmid \binom{d}{k}
$$

である。

---

### Phase 2：GTail 教授の定式化

GTail を Pascal 中間項の束として定義する。

$$
GTail_d(x,u)=\sum_{k=1}^{d-1}\binom{d}{k}x^{k-1}u^{d-k}
$$

素数段では、

$$
GTail_p(x,u)\equiv 0\pmod p
$$

を示す。

---

### Phase 3：GN 助教の定式化

GN を、

$$
GN_d(x,u)=x^{d-1}+GTail_d(x,u)
$$

として定義し、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

を証明する。

素数段では、

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

を得る。

---

### Phase 4：AKS/Fermat への橋

Frobenius 型合同

$$
(x+u)^p\equiv x^p+u^p\pmod p
$$

と GN 合同を結ぶ。

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

さらに Fermat の小定理により、

$$
p\nmid x\Rightarrow GN_p(x,u)\equiv 1\pmod p
$$

を得る。

---

### Phase 5：Zsigmondy への橋

冪差

$$
(x+u)^d-u^d
$$

を GN によって表し、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

を Zsigmondy 型の原始素因子出現と接続する。

まずは Zsigmondy 定理そのものではなく、原始素因子 predicate を置き、既存定理へ接続可能な API を作る。

---

## 研究テーマ名候補

### 候補 1

$$
\text{Pascal-Zsigmondy Bridge}
$$

### 候補 2

$$
\text{NewPrime Birth Bridge}
$$

### 候補 3

$$
\text{Binomial Primitive Factor Bridge}
$$

### 候補 4

$$
\text{GN/GTail Primitive Divisibility Bridge}
$$

### 候補 5

$$
\text{Big Reconstruction and Primitive Prime Emergence}
$$

---

## 短い要約

本研究は、二項定理

$$
(x+u)^d
$$

を自然数 \(d\) の Big 構造と見なし、そこから切り出された Pascal 係数、GTail、GN、冪差分解を統一的に扱う。

素数 \(p\) は Pascal 行 \(d=p\) において、全中間係数に初めて同時出現する。これは係数側の新素因子発生である。

一方、Zsigmondy の原理は、冪差

$$
a^n-b^n
$$

に過去段にはない原始素因子が現れることを述べる。

本研究の中心は、これらを

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

および

$$
(x+u)^d-x^d-u^d=x,GTail_d(x,u)
$$

を通じて接続し、Pascal 側の素因子初登場と冪差側の原始素因子出現を、同一の Big 成長構造の二つの観測面として捉えることである。
