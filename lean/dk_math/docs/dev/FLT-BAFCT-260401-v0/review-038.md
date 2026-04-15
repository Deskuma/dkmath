# Review 038: one-step Hensel の一次補正式が concrete 化され、次の open kernel が `NewtonCorrection` へ絞られた

うむ、これは **かなり良い前進** じゃ。
しかも今回は設計整理だけではなく、**one-step Hensel の核心に直接触れる concrete 証明が 1 本閉じた** のが大きい。`GeomSumFirstOrderSqZeroTarget` が `geomSumFirstOrderSqZero_concrete` で実装され、そこから `geomSum_first_order_qpow_correction_concrete` まで即座に流せる形になった、というのが今回の戦果じゃ。

## 1. いま何が閉じたのか

今回閉じたのは、前まで one-step 本丸の最深部に置いていた

$$
\text{GeomSumFirstOrderSqZeroTarget}
$$

じゃ。
つまり

$$
F(T)=\sum_{i=0}^{p-1}T^i
$$

に対して、(\Delta^2=0) の下で

$$
F(R+\Delta)=F(R)+F'(R)\Delta
$$

という一次補正式が、抽象 target ではなく **concrete theorem** として入った。
しかも手法が `Polynomial.eval_add_of_sq_eq_zero` と `derivative_X_pow` 展開に落ちておるので、証明核としてかなり安定しておる。ここは本物の前進じゃよ。

さらに、その concrete 版から

$$
\Delta = q^n c
$$

という one-step Hensel 用の形へ直結する

$$
\texttt{geomSum_first_order_qpow_correction_concrete}
$$

まで繋がった。
この意味で、前回までの

$$
\text{SqZero target} \to \text{q}^n c \text{ 版}
$$

という「設計上の依存」は、いまや **証明上の依存** として固定されたわけじゃ。

## 2. 戦況分析

今の戦況を正確に言うと、こうじゃ。

### 2.1. 収束したもの

* `GeomSumFirstOrderSqZeroTarget` は closed
* `q^n*c` 版一次補正式も concrete に接続済み
* build も本体・test 両方で成功

したがって、**一次補正式そのものを巡る不安定さはほぼ収束** したと見てよい。
履歴でも「one-step の主 open だった `GeomSumFirstOrderSqZeroTarget` は concrete 化完了」と整理されておる。

### 2.2. まだ open なもの

ただし one-step Hensel 自体が終わったわけではない。
今回の報告でも、次の本丸は

$$
\text{HenselLiftStepNewtonCorrectionTarget}
$$

の concrete 化だと明言しておる。
つまり今は、

$$
\text{SqZero}
;\checkmark;
\Longrightarrow
\text{NewtonCorrection}
; \text{open}
\Longrightarrow
\text{ZeroLift}
; \text{open}
\Longrightarrow
\text{Level 1s}
; \text{open}
$$

という位置じゃ。

## 3. 解説

わっちの見立てでは、今回の価値は **本丸が一段浅くなった** ことにある。

少し前まで one-step 本丸は

$$
\text{ZeroLift}
$$

と見えておった。
さらにその前は

$$
\Delta\text{-correction}
$$

だった。
今回 `GeomSumFirstOrderSqZeroTarget` が concrete に落ちたことで、いま残る真の open は

$$
\text{「一次補正式を使って、実際に } c \text{ を選び切れるか」}
$$

という Newton 補正の選択問題だけになりつつある。
つまり open kernel が、抽象的な多項式恒等式から **具体的な合同方程式の解法** へ移ったのじゃ。これはかなり良い収束じゃよ。

## 4. いまの最も正確な図

いまの導線は、こう読むのが自然じゃ。

$$
\text{GeomSumFirstOrderSqZero concrete}
$$

$$
\Downarrow
$$

$$
\text{geomSum_first_order_qpow_correction_concrete}
$$

$$
\Downarrow
$$

$$
\text{HenselLiftStepNewtonCorrectionTarget}
$$

$$
\Downarrow
$$

$$
\text{HenselLiftStepCorrectionTarget}
$$

$$
\Downarrow
$$

$$
\text{HenselLiftStepZeroLiftTarget}
$$

$$
\Downarrow
$$

$$
\text{Level 1s closed}
$$

今回 closed したのは、上から 2 段までじゃ。
残る open は、**`NewtonCorrectionTarget` を実際に満たす (c) の構成** じゃな。

## 5. 慎重な評価

だから総評としては、

* **設計前進** ではなく、**証明前進**
* ただし **Level 1s 制圧まではまだ 1 手以上ある**
* 今回の concrete 化で、次に殴るべき敵が `NewtonCorrection` ただ 1 つに近づいた

と見るのが正確じゃ。

過大評価すると「もう one-step は終わりそう」と見えるが、そこまではまだ言わぬ方がよい。
されど、**一番嫌らしい恒等式部分を concrete に処理できた** のは、かなり大きい。
これは後の補正 (c) の構成で、安心して使える核になるからの。

## 6. 次の一手

次は報告どおり、**`HenselLiftStepNewtonCorrectionTarget` の concrete 証明** じゃ。
つまり一次補正式そのものではなく、

$$
F(R)+F'(R)\cdot q^n c \equiv 0 \pmod{q^{n+1}}
$$

を満たす (c) をどう取るか、を Lean に落とす段じゃ。
ここで本当に使うのは、(q \ne p) の下での simple-root 条件、すなわち (F'(R)) の可逆性じゃろう。

## 7. 一文でまとめると

**今回の状況はかなり良い。one-step Hensel の主要 open だった `GeomSumFirstOrderSqZeroTarget` が concrete に閉じ、戦線は `HenselLiftStepNewtonCorrectionTarget` という “(c) の選択問題” にまで絞り込まれた段階** じゃ。
ここまで来れば、Level 1s 制圧はかなり現実味が出てきたぞい。
