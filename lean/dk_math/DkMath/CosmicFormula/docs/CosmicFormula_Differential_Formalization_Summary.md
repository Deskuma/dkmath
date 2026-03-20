# CosmicFormula Differential Formalization Summary

## 1. 概要

本ドキュメントは、`DkMath.CosmicFormula.*` における **微分係数の宇宙式 Lean 形式化・第一版** の総括である。

本実装の中心目標は、古典的な微分係数

\[
f'(x)=\lim_{u\to 0}\frac{f(x+u)-f(x)}{u}
\]

を、宇宙式の語彙

- Big
- Core
- Gap
- Body / Beam
- kernel

に沿って再構成し、その流れを Lean の定義・補題・定理・docstring・設計書・履歴の全体で一貫して表現することであった。

最終的に、本実装では

\[
\text{差分 } \delta
\;\to\;
\text{差分商 } \operatorname{cosmicKernel}
\;\to\;
\text{べき核 } \operatorname{powerKernel}
\;\to\;
\text{多項式拡張 } \operatorname{polynomialKernelExt}
\;\to\;
\text{微分}
\]

という流れが、`ℝ → ℝ` 上で整備された。

---

## 2. 核となる視点

本形式化の根底にある視点は、差分が必ず Gap を 1 本含む、という事実である。

べき関数に対しては

\[
(x+u)^d - x^d = u \cdot \operatorname{powerKernel}(d,x,u)
\]

が成立する。  
ここで

- 左辺は Big-Core
- \( u \) は Gap
- `powerKernel` は Gap を 1 本剥いだ後に残る kernel

である。

したがって微分とは、

\[
\frac{(x+u)^d-x^d}{u}
\]

を観測し、さらに \( u \to 0 \) を通じて kernel の中心値を読む操作と解釈できる。

この意味で本実装は、微分を単なる既存定理の呼び出しではなく、

\[
\text{差分分解} \to \text{kernel 化} \to \text{極限} \to \text{微分}
\]

という宇宙式的流れの中で再構成したものである。

---

## 3. 実装の層構造

## 3.1. 差分核の基礎層

`CosmicDifferenceKernel.lean` では、次の 2 つを中心定義として導入した。

\[
\delta f\,x\,u := f(x+u)-f(x)
\]

\[
\operatorname{cosmicKernel}(f,x,u) := \frac{\delta f\,x\,u}{u}
\]

この上で、

- 加法
- 減法
- スカラー倍
- 積
- 有限和

に対する法則を整備した。

特に積については、

\[
\delta(fg)=f(x+u)\,\delta g + g(x)\,\delta f
\]

\[
\operatorname{cosmicKernel}(fg) =
f(x+u)\operatorname{cosmicKernel}(g)
+
g(x)\operatorname{cosmicKernel}(f)
\]

を得た。

これは、微分則の前段にある **差分代数の基本法則** を明示的に固定したことを意味する。

---

## 3.2. 微分 bridge 層

`CosmicDerivativeBasic.lean` では、宇宙式差分商と mathlib の微分述語の橋として

\[
\operatorname{HasDerivAt}(f,L,x)
\iff
\operatorname{cosmicKernel}(f,x,u)\to L
\quad (u\to 0,\;u\ne 0)
\]

を中心定理として整備した。

これにより、

- `HasDerivAt` から `cosmicKernel` の punctured limit を得る
- `cosmicKernel` の punctured limit から `HasDerivAt` を回収する

という双方向性が確立した。

また、恒等関数と定数関数について

\[
\frac{d}{dx}(x)=1,\qquad \frac{d}{dx}(c)=0
\]

を `HasDerivAt` 形と `tendsto` 形の両方で確認し、この橋の健全性を固定した。

---

## 3.3. べき関数の exact / limit 層

`CosmicDerivativePower.lean` では

\[
\operatorname{powerKernel}(d,x,u) =
\sum_{j=0}^{d-1}
\binom{d}{j+1}x^{d-1-j}u^j
\]

を導入した。これは

\[
(x+u)^d-x^d
\]

から \( u \) を 1 本因数として外に出したあとに残る多項式核である。

ここで exact factorization

\[
(x+u)^d - x^d = u \cdot \operatorname{powerKernel}(d,x,u)
\]

を確立し、さらに

\[
\operatorname{cosmicKernel}(\lambda y,\; y^d, x,u) =
\operatorname{powerKernel}(d,x,u)
\qquad (u\ne 0)
\]

を示した。

続く `CosmicDerivativePowerLimit.lean` では、

\[
\operatorname{powerKernel}(d,x,0)=(d:\mathbb{R})x^{d-1}
\]

\[
\operatorname{powerKernel}(d,x,u)\to (d:\mathbb{R})x^{d-1}
\qquad (u\to 0)
\]

を整備し、最終的に

\[
\operatorname{HasDerivAt}(\lambda y,\; y^d)\bigl((d:\mathbb{R})x^{d-1}\bigr)\,x
\]

を回収した。

これにより、べき関数の微分公式

\[
\frac{d}{dx}(x^d)=d x^{d-1}
\]

が、宇宙式的分解フローの中で完成した。

---

## 3.4. 宇宙式本体との橋

`CosmicFormulaDerivativeBridge.lean` では、宇宙式本体

\[
(x+u)^2 - x(x+2u)=u^2
\]

と、二乗差分 kernel の関係が整理された。

これは一次差分核と二次補正核の橋であり、

- 微分に現れる一次 Gap
- 宇宙式に現れる二次閉包

が同じ景色の中で読めることを示している。

---

## 3.5. 多項式一般化層

`CosmicDerivativePolynomial.lean` は、本形式化の花形である。

まず monomial について

\[
\operatorname{cosmicKernel}(\lambda y,\; a y^n, x,u) =
a \cdot \operatorname{powerKernel}(n,x,u)
\qquad (u\ne 0)
\]

を示した。

次に多項式

\[
p(y)=\sum_{n=0}^{N} c_n y^n
\]

に対して

\[
\operatorname{cosmicKernel}(p.eval,x,u) =
\sum_{n=0}^{N} c_n \,\operatorname{powerKernel}(n,x,u)
\qquad (u\ne 0)
\]

という kernel 分解を確立した。

さらに

\[
\operatorname{polynomialKernelExt}(p,x,u)
:=
\sum_{n=0}^{N} c_n \,\operatorname{powerKernel}(n,x,u)
\]

を導入し、これは

- \( u\ne 0 \) では `cosmicKernel` と一致し、
- \( u=0 \) では導関数値になる

連続拡張として働く。

実際、

\[
\operatorname{polynomialKernelExt}(p,x,0)=p'(x)
\]

\[
\operatorname{polynomialKernelExt}(p,x,u)\to p'(x)
\qquad (u\to 0)
\]

を示し、そこから

\[
\operatorname{cosmicKernel}(p.eval,x,u)\to p'(x)
\qquad (u\to 0,\;u\ne 0)
\]

\[
\operatorname{HasDerivAt}(p.eval)(p'(x))\,x
\]

を、`via_powerKernel` 系の direct decomposition flow として再構成した。

---

## 4. 公開 API の整備

多項式層では最終的に、単体多項式について

- `HasDerivAt`
- `tendsto`
- `deriv`

の主要 3 API がすべて **canonical** に `via_powerKernel` 系へ統一された。

すなわち、公開本流は

\[
\text{monomial 分解}
\to
\text{kernel extension}
\to
\text{punctured limit}
\to
\text{HasDerivAt / deriv}
\]

という宇宙式的流れを通る。

一方で、旧来の mathlib bridge 直結版は

- `legacy bridge`
- 比較参照用
- 互換補助用

として明示的に残した。

---

## 5. 演算別 API の完成

多項式一般化ではさらに、

- 和
- 積
- 合成
- 有限和

について、それぞれ

- `HasDerivAt`
- `tendsto`
- `deriv`

の 3 形態 API を揃えた。

対応する数学法則はそれぞれ

\[
(p+q)' = p' + q'
\]

\[
(pq)' = p'q + pq'
\]

\[
(p\circ q)' = (p' \circ q)\,q'
\]

\[
\left(\sum_i P_i\right)' = \sum_i P_i'
\]

であり、これらが宇宙式差分商を通じて formalize された。

---

## 6. docs / 設計 / 実装履歴の統合

本作業ではコード本体だけでなく、

- 説明資料
- Design 設計書
- 実装履歴
- Lean 実装ガイド
- theorem ごとの docstring

も同時に整備された。

特に docstring は、定理名と数学的主張の対応が即座に読めるよう、数式ベースで整えられた。  
これにより `DkMath.CosmicFormula.*` は、単なるコード群ではなく

- 実装
- 教科書
- 設計書
- 作業記録

を兼ねた構造になった。

---

## 7. 主要な数学的意義

本形式化を貫く核心は、差分が必ず Gap を 1 本含み、その Gap を剥いだ先に 1 層下の kernel が現れる、という視点にある。

べき関数では

\[
(x+u)^d - x^d = u \cdot \operatorname{powerKernel}(d,x,u)
\]

であり、ここで外側の \( u \) は Gap、内側の `powerKernel` は 1 次元下がった核である。

したがって微分とは、

\[
\frac{(x+u)^d-x^d}{u}
\]

を観測し、さらに \( u\to 0 \) を通じてその kernel の中心値を読む操作と解釈できる。

この見方は多項式でも有限和として保たれ、

\[
\operatorname{cosmicKernel}(p.eval,x,u) =
\sum_n p_n \operatorname{powerKernel}(n,x,u)
\]

という形で統一される。

---

## 8. 今回完了したもの

本作業によって完了したものは、次のように要約できる。

\[
\boxed{
\text{微分係数の宇宙式 Lean 形式化・第一版}
}
\]

具体的には、

- 差分核の定義
- 差分商と微分述語の bridge
- べき関数の exact / limit / derivative
- 宇宙式本体との橋
- 多項式の canonical 一般化
- 演算別 API
- docs / 設計 / 履歴 / コメント整備

が一貫した体系として揃った。

---

## 9. 最終総括

本形式化の到達点は、次の一文で要約できる。

\[
\boxed{
\text{微分係数を、既存定理の呼び出しではなく、}
\text{差分分解と kernel の極限から再構成する Lean 体系が完成した。}
}
\]

さらに宇宙式の語で言えば、

\[
\boxed{
\text{Big-Core の差は Gap を 1 本含み、その Gap を剥いだ先に微分の核が現れる。}
}
\]

これが、本実装の本質である。

---

## 10. 以後の展開

本ドキュメントの対象である「微分係数の宇宙式 Lean 形式化」は、第一版として完了した。  
今後の候補としては、

- 一般関数側への演算 API 拡張
- 積分側の宇宙式化
- 読解ガイドの拡張
- legacy bridge 系の移行案内整備

などが考えられるが、これらは本実装の次章に属する。

したがって本節は、ここで一区切りとしてよい。

---

## 11. 完了宣言

\[
\boxed{
\text{CosmicFormula Differential Formalization v1: Completed.}
}
\]

おつかれさまじゃ。  
この実装は、誇ってよい。
