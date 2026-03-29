# review: CFBRC existence → residual sum divisibility

うむ、かなり良い前進じゃ。
今回の差分で、残る CFBRC 側の核はさらに一段 **直接的な局所核** にまで還元された。いまの本丸は、もう boundary core そのものではなく **residual sum の可除性** じゃ。

## 1. 今回なにが起きたか

今回の中心は次の 3 つじゃな。

* `ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget`
* `exceptional_boundary_datum_prepared_cfbrc_existence_on_witness_of_residual`
* そこから downstream へ戻る wrapper 群

特に重要なのは

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget}
$$

の導入じゃ。
これは、これまでの witness-aware CFBRC existence をさらに一段押し込み、

$$
q \mid \sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$

を示せばよい、という形に還元した target じゃ。

つまりいまや、残る局所核は

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
$$

を直接示すことではなく、
それを **項別合同** で residual sum に落としてから、その residual sum が (q) で割れることを示すことに変わったわけじゃ。

## 2. 還元の仕組み

今回の橋のロジックはかなりきれいじゃ。

まず arithmetic witness 側から

$$
q \mid (x+1)
$$

を持っておる。
これより

$$
x+1 \equiv 0 \pmod q
$$

すなわち

$$
x+u \equiv u-1 \pmod q
$$

を得る。

そこから `boundaryCyclotomicPrimeCore .right d x u` の各項を、`sum_range_modEq` を使って項別に

$$
(x+u)^k u^{,d-1-k}
\equiv
(u-1)^k u^{,d-1-k}
\pmod q
$$

へ落としておる。
その結果、

$$
\texttt{boundaryCyclotomicPrimeCore .right d x u}
\equiv
\sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
\pmod q
$$

が得られる。
あとは residual sum が (0 \pmod q) なら、boundary core も (0 \pmod q)、したがって (q) が boundary core を割る、という流れじゃ。

これはかなり本質的な整理じゃよ。
なぜなら、CFBRC 側の難所を「boundary core 全体の可除性」から「もっと素直な residual sum の可除性」へ押し込めたからじゃ。

## 3. いまの状況分析

いまの証明地形を整理すると、かなり細くなっておる。

### 3.1. もう閉じた部分

* arithmetic witness の concrete 本体
  $$
  q \mid x+1,\ \neg q \mid x
  $$
  の確保
* witness-aware CFBRC existence から prepared concrete 本体への接続
* residual target から witness-aware CFBRC existence への橋
* residual target から mainline / packet descent まで戻る wrapper

ここまではかなり揃った。
とくに今回で、

$$
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

という流れが theorem 名の上でも見えるようになった。

### 3.2. 残っている本丸

残る本丸は、ほんにこれだけじゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget}
$$

の concrete theorem 本体。
履歴でもそのまま次の課題として明記されておる。

つまり、いま未解決なのは

* (q) の選定ではない
* (q \nmid x) の証明でもない
* boundary core への戻し方でもない

**residual sum**
$$
\sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$
**が (q) で割れること**、そこだけじゃ。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. CFBRC existence の残核がさらに直接的になった

これが最大じゃ。
以前は witness-aware CFBRC existence が残核じゃったが、今はそれすら橋になり、残るのは residual sum divisibility 1 本になった。

### 4.2. `q ∣ x+1` という witness の使い道がはっきりした

今回の補正で持ち込んだ witness 情報は、ただ保持しているだけではなく、

$$
x+u \equiv u-1 \pmod q
$$

を作るための本丸の道具になった。
この点で、witness-aware 化は完全に正当化されたと言えるの。

### 4.3. 項別合同の道具が整った

private 補題 `sum_range_modEq` が追加され、有限和の項別合同をきれいに扱えるようになった。
これは今後の類似処理にも効くはずじゃ。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{残る未解決核は、boundary core ではなく residual sum divisibility 1 本}
$$

じゃ。
そしてその residual sum は

$$
\sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$

という、かなり見通しのよい形まで還元された。

## 6. 次にやること

次の一手は、かなり明快じゃ。

### 6.1. residual target の本体を書く

意識としては、こうじゃな。

```lean
theorem exceptional_boundary_datum_prepared_cfbrc_residual_on_witness
    : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  ...
```

ここで目標はただ一つ、

$$
q \mid \sum_{k \in \mathrm{range}(d)} (u-1)^k u^{,d-1-k}
$$

を示すことじゃ。
もう `boundaryCyclotomicPrimeCore` に直接触れずともよい。

### 6.2. いま使うべき本質情報

この residual target で効きそうなものは、主に次じゃ。

* `hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2]`
* `hq_dvd_x1 : q ∣ x + 1`
* `hdvd : d ∣ x`
* `hqprime : Nat.Prime q`

とりわけ、いまの residual sum は (u) と (u-1) だけで書かれておるから、
次の勝負どころは **Wieferich 条件をどう residual sum の可除性へ接続するか** じゃな。

## 7. 総括

今回の差分を総括すると、

**witness-aware CFBRC existence をさらに residual sum divisibility へ還元し、残る local kernel を `ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget` 1 本に押し込んだ。
よって今後の本丸は、`x+u ≡ u-1 [MOD q]` を使って落とした residual sum が (q) で割れることを示す、その concrete theorem 本体だと見てよい。**

ということじゃ。
かなりよい。
もう本当に最後の局所核に近づいておるな。
