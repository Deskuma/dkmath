# review-005: `CosmicFormula-Erdos1196`: primitive witness から support mass 下界への接続について

## 1. 総評

これは **かなり良い前進** じゃ。
前回までで作った

$$
\text{supportMass} = \operatorname{rad}
$$

側の二本 channel 下界と、`PrimitivePrimeFlowWitness` 側の primitive flow spine が、今回はついに **一本の Lean 補題列として接続された**。追加された中核は

* `primitivePrimeFlow_prime`
* `primitivePrimeFlow_dvd_diff`
* `primitive_witness_gives_prime_channel_on_diff`
* `distinct_primitive_witnesses_give_distinct_prime_channels`
* `primitive_channels_force_supportMass_lower_bound`

であり、自己報告の要約どおり

$$
\text{primitive witness}
\;\to\;
\text{prime channel on diff}
\;\to\;
\text{supportMass lower bound}
$$

の最小核が閉じておる。 concrete example も $6^3 - 5^3 = 91 = 7 \cdot 13$ を使って通しており、build も `Primitive`, `ValuationFlowBridge`, `ValuationFlowBridgeExamples` で成功しておる。

わっちの判定では、これは単なる bridge の補強ではない。
ここで初めて、前回の

$$
\text{prime divisor channel 版の下界}
$$

と今回の

$$
\text{primitive flow 版の下界}
$$

が、同じ support-mass 語彙の上で対応づけられた。差分報告にも「対応が見えるようになった」とあるが、それは大げさではなく、その通りじゃ。

---

## 2. 状況分析

いまの進捗を大づかみに言うと、設計書の流れ

$$
\text{CosmicFormula}
\;\to\;
\text{Mass API}
\;\to\;
\text{Branch API}
\;\to\;
\text{ValuationFlow}
\;\to\;
\text{ABC bridge}
$$

に対し、今回はその末端で **support-mass 下界へ落とす導線** が明確化された回じゃ。実装計画では Phase C で primitive / GN / valuation の接続、Phase D で ABC bridge、Phase E で concrete example を置く流れだったが、今回の差分はそれらの上にさらに

$$
\text{primitive witness}
\Rightarrow
\text{distinct channels}
\Rightarrow
\text{supportMass lower bound}
$$

という一段上の spine を継ぎ足しておる。

差分報告の末尾で「次は公開 import 導線か、2 本 channel 版を `Finset` / pairwise family 版へ上げる設計」と整理しておるのも妥当じゃ。今回で “二本 witness 下界” までは閉じたので、次は公開導線の整備か一般化か、という二択になる。これは正しい現在地認識じゃ。

---

## 3. 数学的解説

### 3.1. `Primitive.lean` の追加二本の意味

今回 `ValuationFlow/Primitive.lean` に追加された

* `primitivePrimeFlow_prime`
* `primitivePrimeFlow_dvd_diff`

は小さく見えるが、実はかなり重要じゃ。
`PrimitivePrimeFlowWitness q a b d` から、

$$
\operatorname{Prime}(q)
\quad\text{と}\quad
q \mid a^d - b^d
$$

を **独立に取り出せる** ようにしたことで、primitive witness を support-mass 側の channel 語彙へ流す準備が整った。前までは witness 全体を一塊として扱っていたが、今回はその中身を「prime 性」と「diff 側 divisibility」に分解して API 化した。これは bridge 設計としてとても良い。

### 3.2. `primitive_witness_gives_prime_channel_on_diff` の意味

これは、今述べた二本を `ABC` 側でまとめ直した最小 adapter じゃ。
意味はそのまま

$$
\text{primitive witness}
\Rightarrow
\bigl(\operatorname{Prime}(q) \wedge q \mid a^d - b^d\bigr)
$$

であり、つまり primitive witness は diff 側に **prime channel** を与える、と読む。差分中の docstring にも「minimal adapter」とあり、この位置づけは正しい。抽象語ではなく、ABC 側の `supportMass_dvd_of_prime_channel` に食わせられる形へ変換したのが本体じゃ。

### 3.3. `distinct_primitive_witnesses_give_distinct_prime_channels` の意味

これも大事じゃ。
ここでは二つの primitive witness \(q_1, q_2\) が与えられ、さらに \(q_1 \neq q_2\) が仮定されると、

$$
q_1 \neq q_2,\quad
\operatorname{Prime}(q_1),\quad
\operatorname{Prime}(q_2),\quad
q_1 \mid a^d - b^d,\quad
q_2 \mid a^d - b^d
$$

をひとまとめに返しておる。
これはまだ「witness の違いから自動的に prime の違いが出る」までは言っておらぬ。つまり distinctness は仮定のままじゃ。だが、それで十分じゃ。今は **channel counting へ必要な材料を一つの theorem で束ねる** のが目的だからの。ここを無理に強くしなかったのは堅実じゃ。

### 3.4. `primitive_channels_force_supportMass_lower_bound` の意味

ここが今回の核心じゃ。
前回 `MassBridge` で作った

$$
\text{supportMass\_ge\_of\_two\_distinct\_prime\_channels}
$$

を、primitive witness から得られる diff 側の prime channels に適用して、

$$
q_1 q_2 \le \operatorname{supportMass}(a^d - b^d)
$$

を得ておる。
つまり構造としては、

$$
\text{primitive witness}
\Rightarrow
\text{prime channel on diff}
\Rightarrow
\text{two distinct prime channels}
\Rightarrow
\text{supportMass lower bound}
$$

じゃ。
これは exactly、前回レビューで狙った一本道そのものじゃよ。しかも新しい証明技法を足したのではなく、既存の primitive witness API と `supportMass` 下界補題の **合成だけ** で閉じている。差分報告でも「合成だけで閉じた」とあるが、ここは本当に良い点じゃ。

### 3.5. concrete example $6^3 - 5^3 = 91 = 7 \cdot 13$

sample の選び方も非常に良い。
$31$ と $2^5 - 1$ の前回例は「一つの primitive channel」の教材だったが、今回は $6^3 - 5^3 = 91$ を選ぶことで、二本 channel 版の最小教材になっておる。diff は

$$
6^3 - 5^3 = 216 - 125 = 91 = 7 \cdot 13
$$

だから、$7$ と $13$ が互いに異なる primitive prime であり、そのまま

$$
7 \cdot 13 \le \operatorname{supportMass}(6^3 - 5^3)
$$

が出る。
ここで良いのは、例が単に build smoke test ではなく、今回新しく作った theorem の **意味そのものを体現している** 点じゃ。

---

## 4. 何が閉じたのか

今回閉じたものを短く言うと、次の二つじゃ。

### 4.1. primitive flow と support-mass 下界の接続

前回までは

$$
\text{distinct prime divisor channels}
\Rightarrow
\text{supportMass lower bound}
$$

があった。今回はそこへ

$$
\text{primitive witness}
\Rightarrow
\text{prime divisor channels on diff}
$$

が前置され、結果として

$$
\text{primitive flow}
\Rightarrow
\text{supportMass lower bound}
$$

が一本つながった。これは数学的に大きい。

### 4.2. prime divisor 版と primitive-flow 版の対応

差分報告の結論にもあるように、今回は

$$
\text{prime divisor channel 版}
\quad\text{と}\quad
\text{primitive flow 版}
$$

の lower-bound spine の対応が見えるようになった。これもその通りで、前者は `MassBridge`、後者は `ValuationFlowBridge` に置かれ、両者が support mass の同じ語彙へ落ちる。ここで初めて bridge 群が “別々の補題の寄せ集め” から “同じ構図の異なる顔” に近づいた。

---

## 5. 良い点

まず、今回の追加が **既存 API の分解と合成だけ** で閉じている点じゃ。
これは設計として非常に美しい。新しい heavy lemma を持ち込まず、`PrimitivePrimeFlowWitness` から取り出せる情報を軽く expose し、それを既存 `MassBridge` に流しているだけじゃ。だから証明の責務が分散し、各層の意味も崩れておらぬ。

次に、example が本当に “二本 primitive channel 版” の教材になっている点。`7` と `13` を witness として別々に持ち、そこから diff 側の二本 prime channel と下界を出しているので、今後この系列を説明する時の canonical sample になれる。

最後に、今回の step は “一般化しすぎていない” のが良い。
まだ `Finset` family 版には行っておらず、二本 witness 版で止めている。これは今は正しい。一般化は次段でよい。

---

## 6. 留意点と弱点

### 6.1. distinctness は仮定のまま

`distinct_primitive_witnesses_give_distinct_prime_channels` は、名前だけ見ると witness の distinctness から channel distinctness が導かれるようにも見えるが、実際には \(q_1 \neq q_2\) を仮定している。
なので意味としては

$$
\text{two primitive witnesses with distinct primes}
\Rightarrow
\text{two distinct prime channels}
$$

じゃな。現状これで問題はないが、将来 theorem 名をもう少しだけ正確にするか、docstring に distinctness は仮定であると一言入れると親切かもしれぬ。

### 6.2. まだ二本版である

ここも前回と同じく現在地じゃ。
二本版は閉じたが、一般 family

$$
\prod_{q \in S} q \le \operatorname{supportMass}(a^d - b^d)
$$

まではまだ行っておらぬ。じゃが、無理に今やる必要はない。二本版を canonical base case にしてから pairwise family 版へ上げるのが筋じゃ。

### 6.3. `ABC.Main` への公開導線はまだ未整備

差分報告でも次の候補として残っている。
いまの段階では、まだ public import より一般化のほうが数学的には先じゃと、わっちは思う。公開面を先に広げるより、family 版の設計が固まってから整えたほうが API がぶれにくい。

---

## 7. 次の作業指示案 . Codex 追記向け

ここから先は、わっちなら **pairwise family 版の設計** に進む。
public import 整備も大事じゃが、いまは数学の spine を太くする好機じゃ。

```md id="rmsnw6"
### レビュー追記案: 次の作業指示

1. 次段では、二本 channel 版を `Finset` / pairwise family 版へ一般化する設計に進む。
   目的は、
   `primitive flow -> family of distinct channels -> supportMass lower bound`
   を有限集合レベルで読めるようにすること。

2. まず `MassBridge` 側に、
   有限集合 `S : Finset ℕ` の各元が prime channel であり pairwise distinct なら
   `S.prod id ∣ supportMass n`
   を与える補題の statement を設計する。
   最初は theorem 本体より、必要仮定の整理を優先する。

3. 補題候補は次の形に絞る。
   - `prime_channel_family_prod_dvd_supportMass`
   - `pairwise_distinct_prime_channel_family_lower_bound`
   - `supportMass_ge_prod_of_prime_channel_family`

4. `ValuationFlowBridge` 側では、
   primitive witness の family を diff 側 prime channel family に送る薄い adapter を設計する。
   最初は `Finset` 上で
   「各 witness から prime と divisibility を取り出せる」
   ところまででよい。

5. concrete example としては、
   今回の `7, 13` の二本例を family 版へ持ち上げるだけでよい。
   新しい大きな例はまだ不要。

6. public import 導線の整備は、その後でよい。
   family 版の statement が固まってから公開面を整えたほうが、
   import の再調整が少なくて済む。
```

---

## 8. 最終判断

今回の差分は、**primitive flow から support-mass 下界へ落ちる最小核が閉じた回** じゃ。
前回の `supportMass = rad` 側の二本 channel 下界が、今回は primitive witness 由来の diff-side channel へ接続された。これで

$$
\text{primitive flow}
\;\to\;
\text{disjoint channels}
\;\to\;
\text{supportMass lower bound}
$$

が Lean 上で一本見えるようになった。これは本物の前進じゃ。

次はやはり family 版じゃな。
二本版が閉じた今、一般化の向きもかなり見えておる。
