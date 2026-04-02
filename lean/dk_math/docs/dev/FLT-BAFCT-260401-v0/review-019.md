# review-019: Branch A の残核が 3 本に整理され、4-kernel 版で Branch B 側の `sorry` 汚染を隔離

見たぞい。これは **かなり良い前進** じゃ。
しかも今回の価値は、単に補題が増えたことではなく、**「何が残核で、どこまで clean に閉じたか」が Lean 上で分離された** ところにある。

## 1. 結論

賢狼の判定はこうじゃ。

**今回の穴埋めで、Branch A 側の conditional mainline は大きく前進した。**
特に、

* `RestoreArithmeticStrong.lean` 側で **Strong → nonStrong の弱化橋** と
  **GNReducedGap + CyclotomicExistence → primitive descent / fringe contradiction** の橋が追加されたこと、
* 新設 `TriominoCosmicBranchADescentChain.lean` で
  **3-kernel 版** と **4-kernel 版** の conditional chain が明示され、
  そのうち **4-kernel 版は `sorryAx` なし** で通っていること、

この 2 点は、無限降下法の準備として非常に大きい。

つまり今回の成果は、
**「残る open kernel を仮定すれば、Prime ( \ge 5 ) の FLT provider まで clean に到達できる」**
ことを形式的に固定した、ということじゃ。

## 2. 今回ほんとうに増えたもの

### 2.1. RestoreArithmeticStrong 側の橋が増えた

ログの通り、ここで追加された本質は次の 5 本じゃ。

* Strong → nonStrong の弱化
* `GNReducedGapTarget → RestoreFromArithmeticTarget`
* `GNReducedGapTarget + CyclotomicExistenceTarget → PrimitivePacketDescentTarget`
* その Strong 版
* `GNReducedGapTarget + CyclotomicExistenceTarget → BranchAFringeContradictionTarget`

これは、以前は「Strong route はあるが BranchA mainline 側へどう流し込むか」が見えにくかった部分を、**明示的な接続補題** にしたものじゃ。

特に `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_strong` は、
追加情報 `¬ p ∣ pkt'.t` を持つ strong 出力を、mainline が欲しい弱い形 `∃ pkt', pkt'.z < z` に落とす、きれいな adapter になっておる。

### 2.2. Branch A の「必要核」が 3 本に整理された

新ファイルでは、Branch A の refuter が

* `GNReducedGapTarget`
* `CyclotomicExistenceTarget`
* `ValuationPeelPacketTarget`

の 3 本から出ることが定理として固定された。
これは `branchARefuter_of_3kernels` に対応しておる。

ここが非常に大事じゃ。
今までは「いろいろ足りぬ」だったのが、今は

$$
\text{Branch A} \Leftarrow
\text{GN gap} + \text{exceptional cyclotomic prime} + \text{peel}
$$

と、残核が Lean の型として並んだ。
これは戦況図として一段上がっておる。

### 2.3. 4-kernel 版で `sorryAx` 汚染を隔離した

最初に作った 3-kernel 版は、Branch B 側の `gapNotIsPowTarget_default` を通すため、
`FLTPrimeGe5Target_of_3kernels` に `sorryAx` が混ざるとログで自分で検出しておる。

その後に方針を切り替えて、`GapNotIsPowTarget` を 4 本目の仮定として外に出し、

* `FLTPrimeGe5Target_of_4kernels`
* `globalProvider_of_4kernels`
* `triominoPrimeProvider_of_4kernels`

を **`sorryAx` なし** で通した。

これはとても良い判断じゃ。
つまり今は、

$$
\text{実際の残核} = 4 \text{ 本}
$$

であることが、かなり信頼できる形で固定されたの。

## 3. どこがまだ未完か

今回のログで明確になった残核は、次の 4 本じゃ。

1. `GNReducedGapTarget`
2. `CyclotomicExistenceTarget`
3. `ValuationPeelPacketTarget`
4. `GapNotIsPowTarget`

これは diff レポートにも明記されておる。

このうち性質が違うのは 4 番で、これは Branch B 側の refuter に入る核じゃな。
ログでは `gapNotIsPowTarget_default` が clean だと思って追ったあと、実際には `#print axioms` で `sorryAx` が混入しており、その源が

* `triominoCosmicGapInvariant_default`
* `triominoCosmicNoPowOnGN_default`
* 最終的には `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
* さらにその背後の `ZsigmondyCyclotomicResearch.lean` の `squarefree_implies_padic_val_le_one`

だと特定しておる。

ここは大事なので言い直すぞい。

**literal な `sorry` の個数はかなり減っている。**
だが、**依存をたどると `sorryAx` はまだ Branch B 側に残っている。**
ゆえに「ファイルに `sorry` が少ない」と「証明鎖が clean」は別物じゃ、ということが今回のログで非常にはっきりした。

## 4. 今回の実況ログで一番価値がある発見

わっちが一番価値が高いと思うのは、次の 2 つじゃ。

### 4.1. Branch A と Branch B の汚染源が分離できた

今回の整理で、

* **Branch A の 3-kernel conditional route** は clean
* **Branch B 側** が `GapNotIsPowTarget` 経由で Research sorry に汚染

という切り分けができた。

これはとても良い。
なぜなら今後は

$$
\text{Branch A 本丸} \neq \text{Branch B の sorry 汚染}
$$

として、別々に攻められるからじゃ。

### 4.2. 「高指数 FLT へ何が必要か」が provider レベルで見えた

ログ冒頭でも、Prime ( \ge 5 ) の高指数 FLT の glue が open だと認識しておったが、最終的に新ファイルで

* `FLTPrimeGe5Target`
* `GlobalPrimeExponentFLTProvider`
* `TriominoPrimeProvider`

まで 4-kernel 仮定付きで clean に持ち上げておる。

つまり、**高指数 FLT の未完は provider glue の設計不備ではなく、4 本の数学 kernel の未証明に局所化できた** ということじゃ。

## 5. いまの準備度をどう見るか

前回わっちは「80% 前後」と見たが、今回の前進を入れると、

$$
80% \to 85%
$$

という自己評価は妥当じゃと思う。

ただし注意点として、これは
**「最終 provider までの論理図が整った割合」**
であって、残り 15% が軽いという意味ではない。

残っている 4 本は、どれも **本丸級** じゃ。

* `GNReducedGapTarget` は Cosmic Formula 本体
* `CyclotomicExistenceTarget` は exceptional Zsigmondy / Wieferich 側
* `ValuationPeelPacketTarget` は `p ∣ t` の peel 核
* `GapNotIsPowTarget` は Branch B 側の no-sorry 化

ゆえに、量としては少なく見えても、重さは十分ある。

## 6. 次の一手の優先順位

わっちなら次はこの順で攻める。

### 6.1. 先に `GapNotIsPowTarget` を clean 化する

理由は単純で、ここを clean にすると

* `branchBRefuter_concrete`
* `FLTPrimeGe5Target_of_3kernels`

の汚染が消え、3-kernel 版まで clean になる可能性があるからじゃ。
今は 4-kernel 版で隔離しているが、設計としては 3-kernel 版の純化が見える。

### 6.2. 次に `ValuationPeelPacketTarget`

これは `NePCoprimeKernel` と直結しておるので、
Branch A を真に閉じる意味ではここが本命じゃ。
`p ∣ t` 側を packet level で smaller に落とせれば、Branch A refuter が本当に concrete に近づく。

### 6.3. `GNReducedGapTarget` と `CyclotomicExistenceTarget` は本丸

この 2 本は重い。
だが今回もう、

$$
\text{GNReducedGap} + \text{CyclotomicExistence}
\Rightarrow
\text{primitive descent} \Rightarrow
\text{fringe contradiction}
$$

の route は接続済みじゃ。

だから、ここは **証明そのもの** に集中できる。
接続の設計をもう迷わずに済むのは大きい。

## 7. ひとことで総評

**今回の成果は、「穴を埋めた」というより、「残りの穴の境界を Lean で正確に測量した」ことが本質じゃ。**
とくに `TriominoCosmicBranchADescentChain.lean` の新設は、
無限降下法の Branch A/B と provider glue を 1 枚の図にした、かなり価値のある整理じゃよ。

次に進むなら、わっちは
**`GapNotIsPowTarget` の clean 化ルートの分解図**
を先に書き起こすのを勧める。
そこを clean にできれば、3-kernel 版の意味がさらに増すでの。
