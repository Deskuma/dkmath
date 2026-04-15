# review: FLT-Primitive-260327-v0: selected route の未解決核をさらに圧縮して、current canonical route を selected-core-on-witness 版へ寄せる

うむ、これはかなり見通しが良くなった。
今回の連続差分で、selected route の未解決核は、ほぼ **一点** まで圧縮されたと見てよい。

結論を先に言うと、いまの proof file における **current canonical route** はもう明確に

$$
\text{selected-witness} \to \text{selected-core} \to \text{selected-core-on-witness}
$$

じゃ。
そして current missing math の本体は

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget}
$$

この 1 本、と判断してよい。

## 1. 何が起きたか

今回の更新は 3 段あった。

### 1.1. universal kernel から selected-witness への標準橋

まず

* `exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_congruenceKernel`

が入った。
これで stronger な universal kernel があれば、concrete arithmetic witness を通して

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget}
$$

を直接回収できるようになった。
つまりコード上でも、 **universal は保持しつつ main route は selected-witness** だと明示されたわけじゃ。

### 1.2. selected-witness の残核を CFBRC 側へ寄せた

次に

* `ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget`
* `exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedCoreWitness`

が入り、selected route の missing math を

$$
(u-1)^d \equiv u^d \pmod q
$$

そのものではなく、

$$
q \mid \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
$$

としても追えるようになった。
これは既存 `CFBRC/Bridge` の語彙にかなり近い。つまり、 **合同の世界から core divisibility の世界へ寄せた** のじゃ。

### 1.3. さらに existential packaging を外した

最後に

* `ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget`
* `exceptional_boundary_datum_prepared_selectedCoreWitness_of_onWitness`

が入り、`∃ q` を含む selected-core witness 全体ではなく、

**「arithmetic part がすでに選んだ witness (q) に対して core divisibility を返す」**

という witness-aware な局所 target 1 本へ押し込まれた。
ここが決定的じゃ。

## 2. いまの状況分析

いまの構図をきれいに書くとこうじゃ。

### 2.1. universal 側

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget}
$$

これは stronger theorem として保持されておる。
だが、もはや主戦場ではない。selected-witness 側へ落とす橋が置かれたからの。

### 2.2. selected-witness 側

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget}
$$

これは current canonical route 候補として明示された。
ただし、これ自身も今や主たる missing theorem ではない。さらに下へ押し込まれたからじゃ。

### 2.3. selected-core 側

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget}
$$

これは selected-witness を CFBRC 的な core divisibility へ寄せた中間層じゃ。
かなり自然だが、これも今は中間層になった。

### 2.4. witness-aware core divisibility 側

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget}
$$

これが current missing math の終着点じゃ。
履歴にも、「selected route の current missing math は、もはや `∃ q` 付き target 全体ではなく、この witness-aware core divisibility 1 本」と明記されておる。

## 3. 判断

ここでの判断をはっきり言うぞい。

## 3.1. canonical route について

**selected-core-on-witness 版を current canonical route の最下流核として採用してよい。**

つまり proof exploration の視点では、

$$
\text{universal kernel}
;\Rightarrow;
\text{selected congruence witness}
;\Rightarrow;
\text{selected core witness}
;\Rightarrow;
\text{selected core on witness}
$$

という下降列ができており、最後のものが実際に攻めるべき対象じゃ。

## 3.2. universal kernel の扱い

**消す必要はないが、補助的 stronger theorem として温存する位置で十分** じゃ。
current main route として前面に置く必要はもうない。selected 側へ落とす標準橋がコード化された以上、その役目は「上位一般化」に変わった。

## 4. 今回の整理の価値

これはかなり大きい。

なぜなら以前は「何が未解決なのか」が、

* universal congruence 全体なのか
* selected witness の存在なのか
* direct modEq なのか
* core divisibility なのか

少し揺れておった。
しかし今回で、未解決核ははっきり

$$
q \mid \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
$$

を、 **すでに選ばれた witness (q)** に対して返すことだ、と固定された。
これは proof responsibility が最も小さく、しかも CFBRC 既存橋に最も近い。よい圧縮じゃ。

## 5. 次に何をすべきか

次の一手も、もう明白じゃ。

**`ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget` の concrete theorem 本体を切る。**

これが次の仕事じゃ。

しかも履歴の通り、その下で必要ならさらに

* residual sum へ戻す
* diffPow へ戻す

といった局所補題へ分解してよい。
ここで初めて、ほんとうに数学の本体と向き合う段になったと言えるの。

## 6. 賢狼の見立て

わっちの見立てでは、ここまで来たなら、もう「選択」「存在」「下流配線」は十分に整理済みじゃ。
以後は existential packaging を忘れてよい。考えるべきはただ一つ、

**選ばれた witness (q) が、なぜ ( \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1) ) を割るのか**

これだけじゃ。
つまり議論の主語が finally 固定されたのだ。これは大きい。

## 7. 総括

今回の連続更新を総括すると、

**selected-witness route をさらに CFBRC 側へ寄せ、existential packaging を arithmetic witness で吸収した結果、current missing math は `ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget` ただ 1 本へ局所化された。したがって current canonical route は selected-core-on-witness 版であり、次はその concrete 本体を直接切るべき段である。**

よい。かなり筋が見えた。
必要なら次に、この `SelectedCoreOnWitness` 本体をどう分解して攻めるか、
「CFBRC residual sum route」と「diffPow route」の二股として設計してやろう。
