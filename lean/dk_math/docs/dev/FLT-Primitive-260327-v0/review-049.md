# review: FLT-Primitive-260327-v0: 差冪 target へ還元完了

うむ、今回の差分はかなり良い整理じゃ。

結論から言うと、 **未解決核を「そのまま diffPow 本体へ突撃する問題」から、「追加の合同 kernel を 1 本だけ立てれば全下流が閉じる問題」へ変形した** のが今回の本質じゃ。

## 1. いま何が起きたか

今回、新たに

* `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
* `exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel`

が追加された。
前者は、Branch A exceptional datum だけでは直ちに出せない

$$
(u - 1)^d \equiv u^d \pmod q
$$

を、 **追加供給すべき局所合同入力** として theorem 名に切り出したものじゃ。
つまり「何が足りないのか」を proof file の外形として確定したわけじゃな。

しかもこの kernel を仮定すれば、

* prepared arithmetic core concrete
* mainline
* primitive packet descent

まで、そのまま wrapper で流せるように配線されておる。ゆえに、 **下流はほぼ閉じた** と見てよい。

## 2. 今回の差分の数学的な意味

これは単なる名前整理ではない。

以前は残核を

$$
q \mid u^d - (u-1)^d
$$

という **差の可除性** として追っていた。
いまはそこに加えて

$$
(u-1)^d \equiv u^d \pmod q
$$

という **合同条件** としても追えるようになった。
つまり最後の局所核を、

* 差を割る問題
* 両辺が合同である問題

の二つの言葉で読めるようにしたわけじゃ。これは proof exploration 上、とても強い。

さらに既存の橋

$$
\texttt{Nat.modEq_iff_dvd'}
$$

を使うことで、合同版から divisibility 版を回収する導線も固定された。
ゆえに、 **合同版を主戦場にしてよい** という設計判断が、今回でかなり明文化されたと見てよい。

## 3. 状況分析

いまの証明地形を率直に言うなら、こうじゃ。

### 3.1. すでに閉じている部分

* exceptional datum から必要 witness 条件へ落とす流れ
* diffPow ModEq から diffPow divisibility へ戻す橋
* congruence kernel から prepared concrete へ戻す wrapper
* そこから mainline と packet descent へ流す wrapper
* 該当 build 2 本の成功確認

この意味で、 **構造上の配線は完了に近い**。残っているのは配線ではなく、中に流す“電流”そのものじゃ。

### 3.2. まだ残っている本丸

残る本丸は、履歴にもある通り

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget}
$$

の concrete 本体じゃ。
つまり、いま追うべき missing theorem は「congruence kernel 1 本」として完全に孤立化された。これは大きい。

## 4. なぜ今回の整理が良いのか

ここが肝じゃ。

現時点の exceptional datum だけでは

$$
(u-1)^d \equiv u^d \pmod q
$$

は強すぎる可能性がある、と履歴に明記されておる。
ゆえに、これを theorem 名として first-class に隔離したのは正しい。さもなくば proof file の中で「何が既知で何が未供給か」が濁るからの。

つまり今回の更新は、

* 無理に本体証明へ突っ込まない
* 足りない局所仮定を正面から命名する
* それを入れれば downstream 全体が閉じると保証する

という、Lean 設計としてかなり筋の良い手じゃ。
わっちから見ても、これは **missing math の局在化** として美しい。

## 5. 次に何をするべきか

次の一手は明快じゃ。

**`ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget` の concrete theorem 本体を切る。**

これが最優先じゃ。

そのときの見方としては、最初から divisibility を殴るより、

$$
(u-1)^d \equiv u^d \pmod q
$$

を直接作る方が自然じゃろう。
理由は、今回の設計全体がすでにその方向へ寄っておるからじゃ。合同さえ立てば、その先は既存 wrapper が全部回収してくれる。

## 6. 賢狼の総括

今回の差分を一言で言えば、

$$
\text{未解決核} =
\text{「diffPow ModEq 本体」}
$$

をさらに

$$
\text{未解決核} =
\text{「additional congruence kernel 1 本」}
$$

へと **圧縮・明示化した** 更新じゃ。

ゆえに現状は悲観する局面ではない。
むしろ、配線はほぼ終わり、 **最後に書くべき局所定理の形が綺麗に見えた** 段階じゃな。

必要なら次に、この `congruence kernel` 本体をどういう補題分解で攻めるか、
「既存補題で済む部分」と「本当に新規に要る合同変形」とに切って、実装順まで整理してやろう。
