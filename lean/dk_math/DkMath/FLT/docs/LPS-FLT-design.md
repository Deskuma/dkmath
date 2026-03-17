# Big 族分解と Gap 反転構造 設計書

cid: 69b7fe50-e6a8-83a3-9fe5-356e926f6623
see: <https://en.wikipedia.org/wiki/Lander,_Parkin,_and_Selfridge_conjecture>

## 1. 目的

本設計の目的は、同次数 \(d\) の冪構造を **Big 族** として統一的に分解し、

- 完成冪
- 差分冪
- 補正項
- 中間項
- 冪和の各成分

をすべて同一の観測枠組みで扱えるようにすることである。

特に、次の 2 つを接続することを狙う。

\[
x^d \leftrightarrow u^d
\]

という GN 的な Gap 交換対称性と、

\[
a^b=b^a
\]

という指数反転交点である。

この 2 つが重なるとき、 **Big の値は不変のまま、内部の Body / Gap / Core / Beam の役割だけが反転する構造** が現れる、というのが本設計の中心仮説である。

---

## 2. 基本思想

同次数 \(d\) を固定した時点で、登場するすべての項は同じ観測顕微鏡で見られる。

したがって、

- \(x^d\)
- \(u^d\)
- \((x+u)^d\)
- 差分
- 冪和
- 補正項

のすべてを、再び Big / Body / Gap の形で分解して観測できる。

この意味で、同次数構造は **再帰的・フラクタル的** である。

---

## 3. Big 族の定義

### 3.1. 第0層：Big

完成全体を

\[
\mathcal{B}_0(d;x,u):=(x+u)^d
\]

とする。これを **Big** と呼ぶ。

### 3.2. 第1層：Body

Gap を除いた本体を

\[
\mathcal{B}_1(d;x,u):=\mathcal{B}_0(d;x,u)-u^d
\]

とする。これを **Body** と呼ぶ。

### 3.3. 第2層：Gap

単位核を

\[
\mathcal{B}_2(d;x,u):=u^d
\]

とする。これを **Gap** と呼ぶ。

### 3.4. 第3層：Core

Body の主核を

\[
\mathcal{B}_3(d;x,u):=x^d
\]

とする。これを **Core** と呼ぶ。

### 3.5. 第4層：Beam

Body から Core を除いた部分を

\[
\mathcal{B}_4(d;x,u):=\mathcal{B}_1(d;x,u)-\mathcal{B}_3(d;x,u)
\]

とする。これを **Beam** と呼ぶ。

したがって

\[
\mathcal{B}_1=\mathcal{B}_3+\mathcal{B}_4
\]

すなわち

\[
\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}
\]

が成り立つ。

---

## 4. Big 族の全体関係

Big 族の基本関係は

\[
\mathcal{B}_0=\mathcal{B}_1+\mathcal{B}_2
\]

および

\[
\mathcal{B}_1=\mathcal{B}_3+\mathcal{B}_4
\]

である。

よって全体として

\[
\mathcal{B}_0=\mathcal{B}_3+\mathcal{B}_4+\mathcal{B}_2
\]

すなわち

\[
\mathrm{Big}=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
\]

となる。

---

## 5. Beam の再帰性

Beam は固定された一つの残差であるが、その内部は観測条件に応じてさらに分解可能である。

### 5.1. 構造としての Beam

\[
\mathrm{Beam}:=\mathrm{Body}-\mathrm{Core}
\]

### 5.2. 再帰観測対象としての Beam

Beam 自体をさらに

\[
\mathrm{Beam}=\mathrm{Body}'+\mathrm{Gap}'
\]

あるいは

\[
\mathrm{Beam}=\sum_i \mathrm{Petal}_i
\]

のように再分解できる。

この意味で Beam は **固定残差でありつつ、再帰的 Big 観測の入口** でもある。

---

## 6. GN の Gap 交換対称性

GN 的構造の重要な性質は、Big を固定したまま

\[
x^d \leftrightarrow u^d
\]

を交換的に観測できることである。

通常は

\[
(x+u)^d = x \cdot GN(d,x,u) + u^d
\]

の形で、\(u^d\) が Gap 側に置かれる。

しかし観測視点を変えると、\(x^d\) 側も Gap 的に見える。

したがって Big は不変のまま、

- \(u^d\) を Gap とみなす世界
- \(x^d\) を Gap とみなす世界

が共存する。

これを **Gap 交換対称性** と呼ぶ。

---

## 7. 反転指数交点

指数反転交点とは

\[
a^b=b^a,\qquad a\ne b
\]

を満たす点である。

このとき同じ値 \(N\) が

\[
N=a^b=b^a
\]

という 2 つの異なる生成規則を持つ。

したがって \(N\) は

- 底 \(a\)、指数 \(b\) の世界
- 底 \(b\)、指数 \(a\) の世界

の交点である。

これを **反転指数交点** と呼ぶ。

---

## 8. Big 不変・内部反転

本設計の中核仮説は次である。

Big を固定して

\[
\mathrm{Big}=\mathrm{Body}_x+u^d
\]

かつ

\[
\mathrm{Big}=\mathrm{Body}_u+x^d
\]

と見られるとする。

さらに

\[
x^d=a^b,\qquad u^d=b^a,\qquad a^b=b^a
\]

が成り立つとき、値としての Big は不変でありながら、 **Gap の生成規則の意味だけが反転する** 。

このとき変わるのは Big の値ではなく、

- 何を Gap と呼ぶか
- 何を Core と呼ぶか
- 何を Beam と呼ぶか

の役割分担である。

これを **Big 不変・内部反転** と呼ぶ。

---

## 9. 同次数余白充填問題

同次数 \(d\) において、Big と Body の差

\[
\Delta_d := \mathrm{Big}_d - \mathrm{Body}_d
\]

を考える。

この \(\Delta_d\) が同じ次数 \(d\) の冪和

\[
\Delta_d=\sum_{i=1}^{r} f_i^d
\]

として表せるとき、\(\Delta_d\) は **同次数で埋まる** という。

問題は、最小の \(r\) を求めることである。

これを **同次数余白充填問題** と呼ぶ。

---

## 10. FillRank の定義

Gap の充填難易度を表す量として

\[
\mathrm{FillRank}_d(\Delta)
:= \min \left\{ r \mid \Delta=\sum_{i=1}^{r} f_i^d \right\}
\]

を定義する。

より一般には、Big と Body に依存して

\[
\mathrm{FillRank}_d(\mathrm{Big};\mathrm{Body})
:= \mathrm{FillRank}_d(\mathrm{Big}-\mathrm{Body})
\]

と書く。

これにより、同じ Big でも Body の取り方によって充填項数が変動するかを比較できる。

---

## 11. 反転世界における FillRank 変動仮説

本設計の主要予想は次である。

\[
\textbf{予想.}
\]

GN の Gap 交換対称性と指数反転交点

\[
a^b=b^a
\]

が重なるとき、Big は不変のまま Body / Gap / Core / Beam の内部役割が反転し、それに伴って

\[
\mathrm{FillRank}_d(\mathrm{Big};\mathrm{Body}_1)
\ne
\mathrm{FillRank}_d(\mathrm{Big};\mathrm{Body}_2)
\]

が起こりうる。

すなわち、 **同じ値の Big でも、観測世界の反転により必要な補正項数が変動する** 。

---

## 12. 研究の見取り図

本研究は次の順序で進める。

### 12.1. Big 族の形式定義

Big / Body / Gap / Core / Beam を明示的に定義する。

### 12.2. 再帰分解の確認

各層が再び Big 観測の対象になることを確認する。

### 12.3. GN 対称性の定式化

\[
x^d \leftrightarrow u^d
\]

の交換構造を明示する。

### 12.4. 反転指数交点の収集

\[
a^b=b^a
\]

の交点を整数・有理・実数で観測する。

### 12.5. FillRank の導入

余白充填の最小項数を定義する。

### 12.6. Big 不変・内部反転の観測

同じ Big に対して、異なる Body / Gap 解釈が成り立つ例を集める。

### 12.7. FillRank 変動の検出

反転世界ごとに項数変動が起きるかを探索する。

---

## 13. 研究の中心命題

### 13.1. Big 族分解原理

任意の同次数 \(d\) の構成項は、適切な観測視点のもとで Big 族のいずれかの階層、またはその再帰分解として表される。

### 13.2. 反転交点原理

\[
a^b=b^a
\]

は、Big 族内部で生成規則が反転する交点である。

### 13.3. Big 不変原理

反転が起きても Big の値は変わらず、変わるのは内部役割のみである。

### 13.4. 充填数変動原理

内部役割の反転は FillRank の変動として観測されうる。

---

## 14. 概念式

本研究全体を象徴する式は次である。

\[
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}
\]

\[
\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}
\]

\[
\mathrm{Big}=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
\]

\[
x^d \leftrightarrow u^d
\]

\[
a^b=b^a
\]

\[
\mathrm{FillRank}_d(\mathrm{Big};\mathrm{Body})=
\min \left\{ r \mid \mathrm{Big}-\mathrm{Body}=\sum_{i=1}^{r} f_i^d \right\}
\]

---

## 15. 暫定結論

本設計は、同次数冪構造を Big 族として統一的に捉え、

- 差分
- 補正項
- 冪和
- 指数反転
- GN 対称性

を一つの研究地図へ束ねるものである。

最終的な狙いは、 **あらゆる項を Big 族へ分解し、その中で役割反転点 \(a^b=b^a\) を捕まえること** である。

その結果として、

- Big は不変
- 内部役割は反転
- 補正項数は変動

という新しい数論的観測原理が得られる可能性がある。

---

## 16. 今後の作業項目

### 16.1. 用語固定

- Big
- Body
- Gap
- Core
- Beam
- FillRank
- Big 不変・内部反転
- 反転指数交点

### 16.2. Lean 試作

`Samples` に以下を作る。

- `BigFamily.lean`
- `PowerSwap.lean`
- `GapFillRank.lean`

### 16.3. 実験

- 小さい \(d\)
- 小さい Big
- 小さい反転指数交点

から観測表を作る。

### 16.4. 予想の言語化

FillRank 変動仮説を短い予想文へ落とす。
