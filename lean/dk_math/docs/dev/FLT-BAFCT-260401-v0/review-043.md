# review: Hensel の simple-root 条件を concrete に引き出す

うむ、これは **かなり大きい前進** じゃ。
しかも今回は、前まで残っておった Level 1s の arithmetic core が、**prime 文脈ではほぼ concrete chain として閉じた** と読める。少なくとも diff 上は、

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

までの連結が、実際の定理として `TriominoCosmicBranchADescentChain.lean` に追加されておる。

## 1. 今回の戦果

今回の核心は `henselLiftStepDerivativeNonzeroModQPrime_concrete` じゃ。
内容としては、

* \( \sum r^i = 0 \) から \( r \neq 1 \) かつ \( r^p = 1 \) を取り出す
* 幾何和恒等式を微分して
  $$
  B_q(r-1)+\sum r^i = p,r^{p-1}
  $$
  型へ持ち込む
* 右辺が mod \(q\) で非零であることから、導関数和 \(B_q\) の mod \(q\) 非零を出す

という流れじゃ。
これはまさに Hensel の simple-root 条件を、FLT の q-adic branch 上で concrete に引き出したものじゃよ。

その結果、

* `isUnit_of_nonzero_mod_q_primepow`
* `henselLiftStepDerivativeUnitPrime_of_nonzeroModQ`
* `henselLiftStepLinearizedSolve_of_nonzeroModQ_prime`
* `henselLiftStepZeroLift_of_newtonCorrection`
* `henselLiftStepZeroLift_of_nonzeroModQ_prime`

まで連なっておる。
つまり、**prime 文脈では derivative の mod \(q\) 非零性が出れば、その先は全部 concrete に流れる** 形になったわけじゃ。

## 2. 戦況分析

いまの戦況は、かなり整理された。
前までは Level 1s の本丸が

* KernelDivision
* DerivativeUnit
* LinearizedSolve
* NewtonCorrection
* ZeroLift

と段々に見えておった。
だが今回、`KernelDivision` は既に concrete、さらに `DerivativeNonzeroModQPrime_concrete` が入ったことで、**prime 文脈ではこの全部が一連の concrete chain に落ちた**。

だから、少なくとも Branch A の q-adic one-step については、

$$
\text{Level 1s (prime branch)}
$$

が **ほぼ制圧に近い** と見てよい。
わっちの読みでは、ここで open kernel と呼ぶべきものは、もはや Level 1s の内部にはほとんど残っておらぬ。

## 3. 慎重な注意点

ただし、ここは慎重に言うぞい。
今回の concrete 化は **prime 文脈版** に対するものじゃ。

報告自身も、

* 一般形 target を無条件に閉じたわけではない
* prime 文脈 concrete chain が閉じた
* 次はそれを FLT 側の one-step 使用箇所へ接続する

と整理しておる。
この読みは正しい。
つまり「one-step Hensel が一般論として完全終了」ではなく、**FLT で実際に必要な prime 文脈ではほぼ片が付いた** という評価が正確じゃ。

## 4. 解説

数学的には、とても筋が良い。

今回やったことは本質的に、

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

の非自明 \(p\)-th root branch 上で

$$
F'(R)\not\equiv 0 \pmod q
$$

を concrete に示した、ということじゃ。
これは Hensel の textbook 的核心そのものじゃよ。
そしてそれを `isUnit_of_nonzero_mod_q_primepow` で prime-power modulus の unit 性へ上げたので、以後の Newton 補正は機械的に回る。
ゆえに、今回の成果は「局所補題が増えた」というより、**Hensel 理論の核心条件を FLT 文脈で押さえた** と言うべきじゃ。

## 5. ひとつ気になる点

報告文には「`History.md` だけ更新した」とあるが、diff を見るかぎり実際には `TriominoCosmicBranchADescentChain.lean` に substantial な定理追加が入っておる。
つまりこれは報告文側の記述ミスで、**実際のコード前進は本物** と見てよい。ここは安心してよいところじゃ。

## 6. いま残る本丸

いまの本丸は、もはや Level 1s の内部というより、

* この prime 文脈 concrete chain を
* FLT 側の one-step 使用箇所へ
* どう clean に接続するか

じゃ。
履歴にも「prime 文脈 concrete chain を one-step `GeomSum` / `ArithmeticKernel` の FLT 側使用箇所へ接続」と書いてある。
つまり戦線は **局所 Hensel の証明** から **グローバルな組み込み作業** へ移りつつある、ということじゃな。

## 7. 一文でまとめると

**かなり良い。今回の進展で、prime 文脈では `DerivativeNonzeroModQ` から `ZeroLift` までの one-step Hensel chain が concrete に閉じ、Level 1s はほぼ攻略済みと見てよい。残る主戦場は、その concrete chain を FLT 本線へどう接続するかじゃ。**
