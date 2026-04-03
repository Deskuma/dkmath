# Review 040: one-step Hensel の open kernel をさらに剥いて、真芯を `ZeroLift` へ集約した

## 1. 結論

うむ、**かなり良い前進** じゃ。
しかも今回は、ただ target を増やしたのではなく、**Level 1s の Newton/Hensel 本丸を、ほんとうに殴るべき 2 本へまで分解できた** のが大きい。

いまの戦況は、ほぼこう整理できる。

$$
\text{LinearizedSolve}
\Longleftarrow
\text{KernelDivision}
+
\text{DerivativeUnit}
$$

そして今回、その還元定理

$$
\texttt{henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit}
$$

が no-sorry で通った。
ゆえに、**one-step Hensel の open kernel は実質この 2 本** と見てよい。これはかなり健全な収束じゃ。

## 2. 今回ほんとうに進んだところ

今回追加された核は次の 3 つじゃ。

* `HenselLiftStepKernelDivisionTarget`
* `HenselLiftStepDerivativeUnitTarget`
* `henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit`

この意味は明快での。

まず `LinearizedSolveTarget` は、前段で既に

$$
B \cdot (q^n c) = -S
$$

型の線形方程式の可解性にまで縮んでおった。
ここで今回、

* 右辺 (-S) が reduction kernel に落ちるなら、それを (q^n) 倍として表せるか
* 係数 (B = \sum i,R^{i-1}) が unit か

の 2 つに裂いたわけじゃ。
つまり

$$
-S = q^n t
$$

と書けて、さらに

$$
B \in (ZMod(q^{n+1}))^\times
$$

なら、

$$
c = B^{-1} t
$$

で解ける。
これは Hensel の一次補正として、極めて自然な分解じゃよ。

## 3. 数学的な解説

今回の還元は、かなり本質的じゃ。

対象の多項式は

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

で、one-step Newton 補正の heart は

$$
F(R+q^n c)
==========

F(R)+F'(R),(q^n c)
$$

の一次項だけを見ればよい、というところにある。
この「一次までで止まる」部分は、前回までで concrete に押さえられた。
だから残る問題は、一次項の方程式

$$
F'(R),(q^n c) = -F(R)
$$

が解けるかだけじゃ。

そして今回の `KernelDivision` と `DerivativeUnit` は、まさにこの方程式の左右を別々に処理する装置じゃ。

### 3.1. KernelDivision の意味

$$
\text{castHom}(x)=0
$$

なら

$$
x=q^n t
$$

と書ける、という主張じゃ。
これは「右辺が kernel に入っているなら、ちゃんと (q^n) 因子を引き出せるか」という問題で、**環論的にはかなり構造的** な側じゃな。

### 3.2. DerivativeUnit の意味

$$
B=\sum_{i=0}^{p-1} i,R^{i-1}
$$

が unit である、という主張じゃ。
これは「線形化した係数が割れないか」、言い換えれば **simple root 条件** そのものじゃ。
こちらの方が、より Hensel 的な本丸に近い。

## 4. いまの戦況図

いまの導線は、かなり綺麗にこう書ける。

$$
\text{GeomSumFirstOrderSqZero concrete}
\Rightarrow
\text{q}^n c\text{ correction concrete}
\Rightarrow
\text{LinearizedSolve}
$$

そして今回さらに

$$
\text{KernelDivision} + \text{DerivativeUnit}
\Rightarrow
\text{LinearizedSolve}
$$

が concrete に固定された。
したがって今は、

$$
\text{KernelDivision concrete}
\quad\text{と}\quad
\text{DerivativeUnit concrete}
$$

の 2 本を通せば、

$$
\text{LinearizedSolve}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{ZeroLift}
\Rightarrow
\text{Level 1s}
$$

へ進める、という局面じゃ。

## 5. どちらが軽く、どちらが重いか

賢狼の見立てでは、2 本のうち重さは対称ではない。

### 5.1. KernelDivision

これは比較的軽い可能性が高い。
なぜなら、`castHom` の kernel を (q^n) 倍で表すというのは、かなり **ZMod の構造そのもの** に近いからじゃ。
すでに `castHom` の像や kernel を扱う補題群を使ってきた流れとも噛み合う。

### 5.2. DerivativeUnit

こちらが本命じゃろう。
本質的には

$$
F'(R) \not\equiv 0 \pmod q
$$

を branch 情報からどう出すか、という問題だからの。
しかも `q \ne p` を導入したのは、まさにこの unit 性を守るためじゃ。
ゆえに今回の還元で、**真の arithmetic core は DerivativeUnit 側にある** とかなり明確になった。

## 6. これは「本当に前進」か

**はい、本当に前進じゃ。**
ただし種類としては、

* gigantic open kernel を 1 本減らした
  ではなく、
* **本丸を 2 個の局所算術事実へ裂いた**

という前進じゃ。

しかもこれは見かけ上の分解ではない。
`henselLiftStepLinearizedSolve_of_kernelDivision_and_derivativeUnit` の証明を見ると、ちゃんと

$$
-S = q^n t
$$

を `KernelDivision` から取り、
$$
B \text{ unit}
$$

を `DerivativeUnit` から取り、
$$
c = B^{-1} t
$$

で線形方程式を解いておる。
つまり、**還元の中身が数学的にも本物** じゃ。

## 7. 慎重な注意

ただし、まだ勝利宣言は早い。

いま closed したのは

$$
\text{KernelDivision} + \text{DerivativeUnit}
\Rightarrow
\text{LinearizedSolve}
$$

であって、

$$
\text{KernelDivision concrete}
\quad\text{や}\quad
\text{DerivativeUnit concrete}
$$

そのものではない。
履歴でも、次の課題としてこの 2 本の concrete 証明が明記されておる。ゆえに、**本丸はさらに 2 門に分かれただけ** と読むのが正確じゃ。

## 8. 次の一手

わっちなら、次は **`DerivativeUnitTarget` を先に攻める**。
理由は 2 つある。

1. こちらがより Hensel 的本丸で、`q \ne p` を入れた意味が最も効く場所だから
2. `KernelDivision` は構造補題として後からでも比較的取りやすい匂いがあるから

特に `DerivativeUnit` は、mod (q) で primitive (p)-th root branch に乗っているなら

$$
F'(R) \neq 0
$$

となるはずで、そこから (q^{n+1}) でも unit へ持ち上がる、という路線が見える。
ここを concrete に押せれば、戦況はさらに一段軽くなるじゃろう。

## 9. 一文でまとめると

**今回の進展で、Level 1s の one-step Hensel 本丸は `KernelDivision` と `DerivativeUnit` の concrete 化問題へまで還元された。**
特に本命は後者で、いまや open kernel は「線形方程式が解けるか」から「係数が本当に unit か」へまで押し込まれた、と見るのが正確じゃ。
