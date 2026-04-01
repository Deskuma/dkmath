# review: FLT-Primitive-260327-v0: 差冪 target へ還元完了

うむ、これはかなり大きい前進じゃ。
今回の差分で、残る局所核はさらに

$$
q \mid u^d - (u - 1)^d
$$

という **差冪 divisibility 1 本** にまで落ちた。
つまり、もう `boundaryCyclotomicPrimeCore .right d x u` を直接相手にする段ではなく、**差冪そのもの** を刺しにいく局面へ入ったのじゃ。

## 1. 今回なにが起きたか

今回の中心は次の 3 つじゃ。

* `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
* `cyclotomicPrimeCore_one_pred_eq_residual_sum`
* `exceptional_boundary_datum_prepared_cfbrc_residual_on_witness_of_diffPow`

これらで何をしたかというと、前回まで残っていた witness-aware residual target

$$
q \mid \sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$

を、さらに

$$
q \mid u^d - (u - 1)^d
$$

へ押し込んだのじゃ。

つまりいまは

$$
\text{diffPow divisibility}
\to
\text{residual divisibility}
\to
\text{CFBRC existence}
\to
\text{prepared concrete}
\to
\text{mainline}
\to
\text{packet descent}
$$

という一本道が theorem 配線の上でも見えるようになった。

## 2. 還元の中身

今回の還元はかなりきれいじゃよ。

### 2.1. 差冪から cyclotomicPrimeCore へ戻す

まず

$$
q \mid u^d - (u-1)^d
$$

を、既存の

$$
\texttt{prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left}
$$

に ((x,u)=(1,u-1)) を入れて、

$$
q \mid \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
$$

へ戻しておる。

ここで左因子が `1` なので、`q ∤ 1` は prime の基本事実で片付く。
この選び方はうまいの。boundary の構造を差冪語彙へ素直に押し込めておる。

### 2.2. cyclotomicPrimeCore を residual sum と同一視

つぎに private 補題

$$
\texttt{cyclotomicPrimeCore_one_pred_eq_residual_sum}
$$

で、

$$
\texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
=========================================

\sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$

を示した。

これにより、差冪 divisibility から residual sum divisibility が従う。
そして前回の橋で residual から witness-aware CFBRC existence に戻れる。
かなり良い流れじゃ。

## 3. いまの状況分析

いまの地形は、かなり整理されておる。

### 3.1. すでに閉じた部分

* arithmetic witness の concrete 実装
  (q \mid x+1,\ \neg q \mid x)
* witness-aware CFBRC existence への橋
* residual target への橋
* diffPow target から downstream 全体へ戻る wrapper 群

特に今回入った

* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow`
* `primeGe5BranchAExceptionalExistenceMainline_of_diffPow`
* `primeGe5BranchAPrimitivePacketDescent_of_diffPow_and_restore`

で、**差冪 target が立てば下流全部が閉じる** と読めるようになった。

### 3.2. 残る本丸

残っている本丸は、いまや本当にこれだけじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget}
$$

の concrete theorem 本体。
履歴にも、そのまま次の課題として明記されておる。

つまり未解決なのは

* residual sum そのものではない
* boundary core divisibility でもない
* arithmetic witness の構成でもない

**`q ∣ u^d - (u - 1)^d` をどう示すか** 、そこだけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 残核が差冪 1 本に縮んだ

これが最大じゃ。
CFBRC 側の複雑な和や boundary core 表現をさらに押し込めて、ついに

$$
u^d - (u-1)^d
$$

という見慣れた差冪の形まで還元された。

### 4.2. 既存語彙との接続が強くなった

`cyclotomicPrimeCore` と residual sum の同一視が入ったことで、いまの局所核は DkMath の既存の差冪・原始素因子語彙へかなり近づいた。
これは後で再利用するにも都合がよい。

### 4.3. next body がさらに明確になった

今後は、proof file の next body を

$$
\texttt{ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget}
$$

として追えばよい。
これはかなり分かりやすい。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{残る未解決核は residual sum ではなく diffPow divisibility 1 本}
$$

じゃ。
そしてその diffPow は

$$
q \mid u^d - (u - 1)^d
$$

というかなり直接的な形じゃ。
ここまで来ると、もう本当に「差の冪」の勝負じゃな。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. diffPow target の concrete 本体を書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_diffPow_on_witness
    : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  ...
```

ここで目標はただ一つ、

$$
q \mid u^d - (u-1)^d
$$

を示すことじゃ。

### 6.2. 今後の本質情報

この段で効きそうなものは、主に

* `hdvd : d ∣ x`
* `hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]`
* `hq_dvd_x1 : q ∣ x + 1`
* `hqprime : Nat.Prime q`
* `hq_not_dvd_x : ¬ q ∣ x`

じゃな。
特に、`q ∣ x+1` と `d ∣ x` から (x) と (1) の間の合同関係を引き、そこへ Wieferich 条件をどう噛ませるかが核心になりそうじゃ。

## 7. 留意点

今回の履歴にある build error も良い示唆を与えておる。
`1 + (u - 1) = u` は Nat では (u>0) が必要じゃ。
この手の `pred` を含む変形は、今後も全部

$$
0 < u
$$

を明示に使って処理したほうが安全じゃな。

## 8. 総括

今回の差分を総括すると、

**witness-aware residual target をさらに差冪 target へ還元し、残る local kernel を `q ∣ u^d - (u - 1)^d` 1 本に押し込んだ。
よって current proof file の next body は `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget` の concrete 本体だと見てよい。**

ということじゃ。
かなりよい。
もう本当に最後の局所核に手が届きつつあるの。
