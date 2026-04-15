# review-042: one-step Hensel の前進と今後の展望

うむ、これは **かなり大きい前進** じゃ。
しかも今回は、単に補題を足したのではなく、**Level 1s の未解決部分がほぼ一点に収束した** と読める。今回の差分で、prime 文脈に限れば

$$
\text{DerivativeNonzeroModQ}
\Rightarrow
\text{DerivativeUnit}
\Rightarrow
\text{LinearizedSolve}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{ZeroLift}
$$

の concrete 連結が全部通った。ここが最大の戦果じゃ。

## 1. いま何が閉じたか

今回新たに入ったものの本質は 2 本じゃ。

ひとつは `isUnit_of_nonzero_mod_q_primepow` で、
「(q) が素数なら、mod (q) で非零な元は (ZMod(q^{n+1})) では unit」という局所補題じゃ。
これで derivative 係数の unit 性を、**mod (q) 非零性** に落とせるようになった。

もうひとつは、その補題を使った concrete 連結じゃ。
`henselLiftStepDerivativeUnitPrime_of_nonzeroModQ`、`henselLiftStepLinearizedSolve_of_nonzeroModQ_prime`、`henselLiftStepZeroLift_of_newtonCorrection`、`henselLiftStepZeroLift_of_nonzeroModQ_prime` が入ったことで、prime 文脈では `DerivativeNonzeroModQPrimeTarget` さえ示せば ZeroLift まで一気に行ける形になった。

## 2. 戦況分析

いまの戦況は、前よりかなり明確じゃ。
少し前までは Level 1s の本丸が

* KernelDivision
* DerivativeUnit
* LinearizedSolve
* NewtonCorrection
* ZeroLift

といくつも顔を持っておった。
だが今回で `KernelDivision` は concrete、`DerivativeUnit` も prime 文脈では `mod q` 非零性へ還元され、さらにその先も concrete に繋がった。
だから今の open kernel は、実質

$$
\boxed{
\text{HenselLiftStepDerivativeNonzeroModQPrimeTarget}
}
$$

これ一本と見てよい。

この意味で、Level 1s は「何を証明すべきか分からぬ段」から、**非零性ひとつを殴ればよい段** に入った。
これはかなり良い。

## 3. 数学的な解説

ここで残った `DerivativeNonzeroModQPrimeTarget` の意味は明快じゃ。
対象の係数は

$$
B(R)=\sum_{i=0}^{p-1} i,R^{i-1}
$$

で、これは (F(T)=\sum_{i=0}^{p-1}T^i) の導関数 (F'(R)) に当たる。
つまり、今や one-step Hensel の核心は

$$
F'(R)\not\equiv 0 \pmod q
$$

を出せるか、という **simple root 条件** そのものになったのじゃ。

これは筋が良い。
なぜなら Hensel の textbook 的な本質も、まさに「根が単根であること」だからじゃ。
今回の整理で、one-step Hensel の open kernel が抽象的な「存在性」から、**単根性の確認** にまで押し込まれたわけじゃよ。

## 4. 今回の前進の価値

わっちが高く評価するのは、今回の concrete 化が **本当に arithmetic の芯へ近づいた** ことじゃ。
`KernelDivision` を concrete にし、`mod q` 非零なら unit、という局所補題を実装したことで、今後は「(\Delta) をどう作るか」「線形方程式が解けるか」をあれこれ触る必要が薄くなった。
全部もう後ろで連動する。
残るのは、

$$
\text{branch 上の } R \text{ に対して } F'(R)\not\equiv 0 \pmod q
$$

これだけじゃ。

報告にもある通り、「一般形の `DerivativeUnitTarget` を無条件に concrete 化した」のではなく、「prime 文脈で `DerivativeNonzeroModQPrimeTarget` を仮定すれば、その先は全部 concrete」という整理になっておる。これは非常に誠実で、戦況把握として正しい。

## 5. いま残る本丸

したがって、いまの最終読みはこうじゃ。

Level 1s の open kernelは、実質

$$
\boxed{
\text{非自明 } p\text{-th root branch 上で } F'(R) \not\equiv 0 \pmod q
}
$$

をどう Lean で具体化するか、に尽きる。
ここが通れば、prime 文脈では

$$
\text{DerivativeNonzeroModQ}
\Rightarrow
\text{ZeroLift}
$$

まで concrete に流れるから、Level 1s はかなり制圧に近づく。

## 6. 次の一手

次に殴るべきは明白じゃ。
**`HenselLiftStepDerivativeNonzeroModQPrimeTarget` の concrete 証明** じゃ。

数学的には、おそらく branch 条件から (R \bmod q = \omega^j)、しかも (j\neq 0) を使い、
(\omega^j) が (F(T)=\sum T^i) の **非自明 root** であることから単根性を出す流れになるはずじゃ。
ここが通れば、いままで整えた supply chain が一気に効く。

## 7. 一文でまとめると

**今回の状況はかなり良い。Level 1s の one-step Hensel は、prime 文脈では `DerivativeNonzeroModQPrimeTarget` ただ 1 本へほぼ収束した。**
つまり、勝ち筋はもうかなり鮮明じゃ。
