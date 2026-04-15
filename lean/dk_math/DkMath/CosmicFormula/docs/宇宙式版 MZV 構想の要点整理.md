# 宇宙式版 MZV 構想の要点整理

cid: 69bce1b4-934c-83ab-a8bd-e60b263ef11b

## 1. 目的

多重ゼータ値を参考にする意味は、式の見た目を似せることではない。
本質は、

\[
\text{値そのもの}
\quad\text{ではなく}\quad
\text{分解の仕方・深さ・順序・多層構造}
\]

を観測することにある。

宇宙式版でも同様に、単に \(1/G\) を書くだけでは不足である。
本当に見たいのは、

\[
\text{Big の値}
\quad\text{ではなく}\quad
\text{Big を生み出す Body / Beam の分解地形}
\]

である。

---

## 2. 宇宙式側の基本構造

宇宙式族の基本分解は

\[
\mathrm{Big}(d;x,u)=(x+u)^d,
\qquad
\mathrm{Gap}(d;u)=u^d,
\qquad
\mathrm{Body}(d;x,u)=(x+u)^d-u^d
\]

である。

2 次元の最小手本では

\[
(x+u)(y+v)-uv = xy + xv + uy
\]

となり、Body は 3 要素へ分解される。
これは「あと 1 ピースで完成する平方完成の差分構造」が、具体的な Beam 群として現れている例とみなせる。

したがって、宇宙式版 MZV 構想の主役は、まず

\[
\text{Body を構成する Beam 群}
\]

である。

---

## 3. 本当に主役にすべきもの

主役は \(1/G\) ではない。
まず定義すべき対象は

\[
\mathcal{B}(d;x,u)
:=
\text{Body を構成する Beam 項の集合}
\]

である。

ただし普通の集合ではなく、次を区別できる形が望ましい。

- どの Beam 項が現れるか
- 何回現れるか
- どの次数層に属するか
- どの unit 組み合わせから生じるか

ゆえに実際には

\[
\mathcal{B}(d;x,u)=
\text{Beam の support 付き多重集合}
\]

とみなすのが自然である。

---

## 4. \(1/G\) の役割

\[
\frac{1}{G_d(x,u)}
\]

は主役そのものではなく、Beam 構造を測るための **調和的スカラー観測量** である。

流れとしては

\[
\text{Big}
\to
\text{Body}
\to
\text{Beam support}
\to
\text{harmonic observable}
\]

である。

したがって、

\[
\boxed{
1/G \text{ は Beam 集合そのものではなく、Beam 集合の調和的 summary である}
}
\]

という理解が適切である。

---

## 5. 宇宙式版で見えるようにしたいもの

宇宙式版 MZV 的構成が意味を持つのは、少なくとも次を区別できるときである。

### 5.1. same Big / different Body

同じ Big に着地しても、Body や Beam の分解が異なる場合を識別できること。

### 5.2. profile split

同じ Big でも、Beam の組み合わせ深さ・残差・最小 profile が異なる場合を検出できること。

### 5.3. 値が潰れても構造が残ること

可視値が一致したり 0 になったりしても、support / blueprint として構造情報が保持されること。

---

## 6. KUS / GKUS との接続

この「値が潰れても構造が残ること」は、KUS / GKUS の思想と一致する。

KUS / GKUS では、

- `coeff` = 可視係数
- `unit + blueprint` = 構造保持側

が分離されており、係数が 0 になっても support は消えない。
この設計は、Beam 構造を主役にして \(1/G\) を観測量とする考え方と相性がよい。

したがって宇宙式版でも、

\[
\text{可視値}
\quad+\quad
\text{構造保持側}
\]

の二層を分けるべきである。

---

## 7. 交換補題の意味

ここで必要なのは、単純な「和を積へ変える補題」ではない。
本当に必要なのは、

\[
\boxed{
\text{加法表示のまま、積構造 shadow を失わずに運ぶ交換補題}
}
\]

である。

つまり外側の総和 \(\sum\) はそのまま残しつつ、
内側の加法引数や Beam 分解に対して multiplicative shadow を付与し、その情報を調和化後にも保持したい。

この交換補題が成立すれば、宇宙式側でも

- 圧縮
- shadow 化
- 調和化

を経ても分解構造を失わない観測器が得られる。

---

## 8. いま定義すべき 3 層

今後の設計では、次の 3 層を順に定義するのがよい。

### 8.1. BeamSupport

\[
\texttt{BeamSupport}
\]

Body を構成する Beam 項の集合、または多重集合。
これは幾何的・組合せ的な主役である。

### 8.2. BeamShadow

\[
\texttt{BeamShadow}
\]

BeamSupport を、因数構造・support・blueprint つきで保持したもの。
KUS / GKUS 的な構造保持層に相当する。

### 8.3. BeamHarmonic

\[
\texttt{BeamHarmonic}
\]

BeamSupport / BeamShadow を要約する調和的観測量。候補は

\[
\frac{1}{G_d(x,u)}
\quad\text{または}\quad
\sum_{B\in\mathcal B}\frac{1}{B}
\]

である。

---

## 9. 多重ゼータ値との橋渡しが可能になる条件

多重ゼータ値との橋渡しが意味を持つのは、次が成立した後である。

- BeamSupport が定義される
- BeamShadow が定義される
- 加法表示から shadow を失わず transport できる
- 調和化しても Beam の分解情報を recover できる

この段階に至って初めて、

\[
\text{単一核}
\to
\text{多重核}
\]

の比較が、単なる読み替えではなく、実質的な観測器比較になる。

---

## 10. 現時点での設計判断

今回の議論から得られた設計判断は、次の 2 行に要約できる。

\[
\boxed{
\text{宇宙式版 MZV で見たいのは、Big の値ではなく、Big を生む Beam 分解の多層 profile 幾何である}
}
\]

\[
\boxed{
1/G \text{ はその profile を測る観測量であって、主役は Beam support / Beam shadow である}
}
\]

---

## 11. 次の実装方針

実装順序は次でよい。

\[
\texttt{BeamSupport}
\to
\texttt{BeamShadow}
\to
\texttt{BeamHarmonic}
\]

その上で、次を検証する。

### A. same Big / different Body を BeamSupport が区別できるか

### B. BeamShadow が profile split を保持できるか

### C. BeamHarmonic が有意味な観測量として振る舞うか

### D. 値が潰れても構造側が保持されるか

---

## 12. 最終まとめ

多重ゼータ値を参考にする理由は、「多重和」という見た目ではない。
その真価は、**多層分解の不変量** を作るところにある。

宇宙式版でも同様に、目指すべきは

\[
\text{Big の背後にある Beam 分解の集合的幾何}
\]

を観測することである。

よって、今後の主眼は

- Beam の組み合わせパターン的集合を定義すること
- その shadow を保持すること
- \(1/G\) をその構造を測る観測量として位置づけること

にある。

これが出来て初めて、宇宙式版 MZV は **ただの翻訳ではなく、新しい観測器** となる。
