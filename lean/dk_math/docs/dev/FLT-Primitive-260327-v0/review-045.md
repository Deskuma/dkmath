# review: q | x+1 を持つ witness-aware CFBRC existence part を残核 target に補正した

うむ、ここで一段、かなり重要な補正が入ったの。
今回の差分の本質は、**残っている CFBRC 側の局所核は、単なる「候補 prime (q)」では足りず、`q ∣ x+1` という witness まで持った形で読むべきだ** と fixed されたことじゃ。

## 1. 今回なにが起きたか

新しく入った中心は、次の 4 系統じゃ。

* `ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget`
* `exceptional_boundary_datum_prepared_arithmetic_witness_concrete`
* `ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget`
* witness-aware 版から prepared concrete / mainline / packet descent へ戻る wrapper 群

要するに、これまで arithmetic part で得ていた prime (q) について、
単に

$$
\mathrm{Prime}(q)\land \neg q \mid x
$$

だけではなく、

$$
\mathrm{Prime}(q)\land q \mid (x+1)\land \neg q \mid x
$$

まで保持する **witness-aware 版** が導入されたわけじゃ。

## 2. なぜこの補正が必要だったか

ここが今回のいちばん大事な点じゃ。

前回の arithmetic part concrete は、実際には

* (x+1) の素因子 (q) を取り
* その (q) が (x) を割らぬことを示す

という証明だった。
つまり (q) の出所は本質的に

$$
q \mid (x+1)
$$

じゃった。

ところが従来の

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget}
$$

は、その出所を忘れておった。
それでは CFBRC 側で「なぜその (q) が boundary core を割るのか」を組み立てるには情報が弱い。

ゆえに今回、残核を正しく

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget}
$$

として、`q ∣ x + 1` まで含む形に補正したのじゃ。

これは非常に筋がよい。
算術側で作った witness の情報を捨てずに、CFBRC 側へちゃんと渡すようになったからの。

## 3. いまの状況分析

いまの構図を整理すると、かなり明快じゃ。

## 3.1. すでに閉じたもの

* arithmetic part concrete
  [
  \texttt{exceptional_boundary_datum_prepared_arithmetic_part_concrete}
  ]
* その witness-aware 強化版
  [
  \texttt{exceptional_boundary_datum_prepared_arithmetic_witness_concrete}
  ]
* witness から旧 arithmetic part への忘却
  [
  \texttt{exceptional_boundary_datum_prepared_arithmetic_part_of_witness}
  ]
* witness-aware CFBRC existence が立てば prepared concrete 本体が閉じる assembler
* そこから mainline / packet descent へ戻る wrapper

つまり、**算術側の witness 生成はもう concrete に閉じており、その witness を使う downstream 配線も揃った**。

## 3.2. 残っている本丸

残る本丸は、いまや本当にこれだけじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget}
$$

の concrete theorem 本体。
履歴でも、そのまま次の課題として明記されておる。

つまり、いま未解決なのは

* (q) をどう選ぶかではない
* (q \nmid x) をどう示すかでもない
* mainline へどう戻すかでもない

**`q ∣ x+1` を持つその witness から、`q ∣ boundaryCyclotomicPrimeCore .right d x u` をどう出すか**
そこだけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 残核の target が “正しい形” になった

これが最大じゃ。
旧 target は候補 prime の出所を忘れておったが、今は `q ∣ x+1` を含む。
これで CFBRC existence 側が実際の arithmetic concrete と整合した。

### 4.2. arithmetic 側と CFBRC 側の責務が綺麗につながった

いまは

$$
\text{arithmetic witness}
\to
\text{witness-aware CFBRC existence}
\to
\text{prepared concrete}
$$

という流れになった。
これは非常に自然な責務分離じゃ。

### 4.3. truly remaining な local kernel が theorem 名で明示された

いま「何がまだ missing か」と問われたら、かなり正確に

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget}
$$

と答えられる。
これは管理上も思考上も強い。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{残る未解決核は、witness-aware CFBRC existence part 1 本}
$$

じゃ。
しかもその witness は具体的に

$$
q \mid (x+1),\qquad \neg q \mid x
$$

まで持っておる。
もう戦場は完全に CFBRC 側へ移ったと見てよい。

## 6. 次にやること

次の一手は、かなり明快じゃ。

### 6.1. witness-aware CFBRC existence part の本体を書く

意識としては、こういう形じゃな。

```lean
theorem exceptional_boundary_datum_prepared_cfbrc_existence_on_witness
    : ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  ...
```

ここで目標はただ一つ、

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

を示すことじゃ。

### 6.2. いま使うべき本質情報

この part で本当に効きそうなのは、次の 4 つじゃ。

* `hdvd : d ∣ x`
* `hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]`
* `hq_dvd_x1 : q ∣ x + 1`
* `hq_not_dvd_x : ¬ q ∣ x`

とりわけ今回の補正で、`hq_dvd_x1` が残核 target に入ったのが決定的じゃ。
これを CFBRC / cyclotomic / boundary core の形にどう噛ませるかが、次の勝負どころじゃな。

## 7. 総括

今回の差分を総括すると、

**arithmetic part が実際には `q ∣ x+1` を使って witness を選んでいることを踏まえ、残る CFBRC 側の target を witness-aware 形に補正した。
その結果、proof file の truly remaining な local kernel は `ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget` 1 本だと、かなり正確に読めるようになった。**

ということじゃ。
かなりよい。
もう arithmetic の森は抜けた。残るは、その witness を boundary core divisibility へ変える CFBRC 核だけじゃな。
