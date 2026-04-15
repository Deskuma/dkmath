# Review 041: one-step Hensel の open kernel をさらに剥いて、真芯を `ZeroLift` へ集約した

うむ、これは **かなり良い前進** じゃ。
しかも今回は、ただ target を細かくしただけではなく、**Level 1s の one-step Hensel 本丸が、ほぼ `DerivativeUnit` ただ 1 本へ収束した** と読める。そこが大きい。

## 1. 現在地

今回の差分で、`HenselLiftStepKernelDivisionTarget` は concrete に閉じた。
さらに

$$
\texttt{henselLiftStepLinearizedSolve_of_derivativeUnit}
$$

が入ったことで、

$$
\text{DerivativeUnit}
\Rightarrow
\text{LinearizedSolve}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{Correction}
\Rightarrow
\text{ZeroLift}
$$

という supply chain が、かなり明確に一本化された。
つまり、前回まで

$$
\text{KernelDivision} + \text{DerivativeUnit}
$$

の 2 本に見えていた open が、今回で

$$
\boxed{\text{DerivativeUnit の concrete 証明}}
$$

を残すだけ、という形にかなり近づいたのじゃ。

## 2. 今回ほんとうに閉じたもの

閉じたのは `KernelDivision` じゃ。
内容としては、

$$
\text{castHom}(x)=0
$$

なら (x) は (q^n) 倍で書ける、すなわち

$$
x=(q^n),t
$$

と `ZMod(q^(n+1))` 上で表せることを concrete に示した。
これは Hensel 線形化の右辺処理として、かなり自然で正しい。
報告どおり、`x.val` の可除性に落としてから持ち上げているので、構造側としては十分に筋が良い。

## 3. なぜこれは大きいのか

one-step Newton 補正の方程式は、本質的に

$$
B \cdot (q^n c) = -S
$$

じゃ。
ここで

* `KernelDivision` は (-S) が本当に (q^n) 倍で書けること
* `DerivativeUnit` は係数
  [
  B=\sum i,R^{i-1}
  ]
  が unit で割れること

を担う。

今回 `KernelDivision` が concrete になったので、残る arithmetic の心臓は完全に

$$
B \in (ZMod(q^{n+1}))^\times
$$

をどう出すか、に集中した。
つまり **Hensel の simple-root 条件だけが残った**、と見てよい。

## 4. 今回の設計判断で良い点

`HenselLiftStepDerivativeUnitPrimeTarget` を別に立てたのは、とても良い。
ここで「(p) が合成数だと反例があるので、prime 文脈に限定して concrete 化する」と整理したのは、FL T文脈にぴたり合っておる。
これは逃げではなく、**証明可能域を正しく FLT の本番条件へ合わせた** ということじゃ。

## 5. 慎重に見るべき点

ただし、まだ Level 1s 制圧とは言わぬ方がよい。
今回 concrete になったのは

$$
\text{KernelDivision}
$$

だけで、`DerivativeUnit` はまだ target のままじゃ。
ゆえに現状は

$$
\text{Level 1s}
;\approx;
\text{DerivativeUnit concrete 化待ち}
$$

じゃな。

したがって評価としては、

* **設計はかなり収束**
* **証明も半歩でなく一歩進んだ**
* だが **最後の arithmetic core はまだ残る**

と読むのが正確じゃ。

## 6. いまの戦況図

いまは、かなり綺麗にこう書ける。

$$
\text{GeomSumFirstOrderSqZero concrete}
$$

$$
\Downarrow
$$

$$
\text{LinearizedSolve}
\Leftarrow
\text{KernelDivision concrete}
+
\text{DerivativeUnit open}
$$

$$
\Downarrow
$$

$$
\text{NewtonCorrection}
\Downarrow
\text{ZeroLift}
\Downarrow
\text{Level 1s}
$$

この図で見ると、いま残る open kernel は実質ひとつじゃ。
だから、戦況としてはかなり良い。

## 7. 次の一手

次はもう明快じゃ。
**`HenselLiftStepDerivativeUnitTarget` の concrete 証明** を狙う。

数学的には、おそらく

$$
F(T)=\sum_{i=0}^{p-1}T^i,\qquad
F'(T)=\sum_{i=0}^{p-1} i,T^{i-1}
$$

に対して、branch 上の (R) が (\Phi_p) の simple root であること、すなわち

$$
F'(R)\not\equiv 0 \pmod q
$$

をまず mod (q) で出し、それを (q^{n+1}) でも unit に持ち上げる流れになるはずじゃ。
ここが通れば、Level 1s はかなり現実味を帯びる。

## 8. 一文でまとめると

**今回の状況はかなり良い。`KernelDivision` が concrete に閉じ、Level 1s の one-step Hensel 本丸は実質 `DerivativeUnit` の concrete 証明ひとつにまで押し込まれた。**
つまり、いまや勝負は truly arithmetic な一点へ集約された、ということじゃ。
