# review-017: counting spine が `ABC038` の `TailBound` 入力まで届いた

今回は、かなり良い前進じゃ。
しかも性質としては、単なる橋の整理ではなく、前回整理した `ABC038` 向け dependency chain を、実際に Lean の theorem と wrapper に落とした回になっておる。新しく

* `PrimitiveWitnessFamily.primitive_witness_family_gives_abc_rad_target_lower_bound`
* `PrimitiveWitnessFamily.primitive_channel_count_forces_rad_input_lower_bound`
* `PrimitiveWitnessFamily.primitive_channel_count_forces_quality_rad_input`

が `ValuationFlowBridge.lean` に入り、さらに `ABC038Bridge.lean` と `ABC038BridgeExamples.lean` が追加された。これで counting spine が `ABC.rad` 下界に留まらず、`ABC038` が読む `TailBound` 入力まで届く形になった。

## 状況分析

前回までの段階では、

$$
\text{channelCount}
\;\to\;
2^{\text{channelCount}}
\;\to\;
\mathrm{ABC.rad}(\text{diff})
$$

までは通っておったが、`ABC038` 側が本当に欲しているのは `ABC.rad (u * v)` を入力にした `TailBound` や、その先の quality bound じゃった。そこで前回の依存整理では、不足を

* target rename
* radical transport
* quality-input wrapper

の三層に切っておった。今回の差分は、そのうち少なくとも最小の二層を実装し、さらに `TailBound` へ流す wrapper まで作った、という意味で非常に自然な進展じゃ。前段の設計整理が、そのまま実装へ落ちておる。

とくに良いのは、quality theorem そのものをいきなり書き換えに行かず、まず `ABC038Bridge.lean` という薄い接続ファイルを一枚挟んだことじゃ。これにより、既存 `ABC038` 本体を汚さずに、「bridge 側が何を供給できるか」を theorem 名で固定できておる。これは今のフェーズに合った、堅い進め方じゃ。

## 数学的解説

今回の数学的な本体は、counting spine を `TailBound` の形まで持ち上げたことじゃ。

まず `primitive_witness_family_gives_abc_rad_target_lower_bound` は、前回整理した Candidate B の最小実装そのものじゃ。`c = a^d - b^d` を仮定して、

$$
2^{F.\text{channelCount}} \le \mathrm{ABC.rad}(c)
$$

を target 名 `c` で読めるようにした。中身としては `pow_channelCount_le_abc_rad_diff` の rename じゃが、これで diff quantity の世界から triple target の世界へ一歩移れた。これは小さいようで大きい。`ABC038` 側は target `c` を基準に語るので、ここを theorem 名で切ったのは正しい。

次に `primitive_channel_count_forces_rad_input_lower_bound` は、Candidate C の一般化版じゃな。`ABC.rad c ≤ ABC.rad (u * v)` を transport 仮定として残しつつ、

$$
2^{F.\text{channelCount}} \le \mathrm{ABC.rad}(u * v)
$$

を得る。これにより、「diff 側で得た radical 下界を、quality 側が欲する radical input へ送る」操作が theorem として明示された。ここで transport を仮定に残したのが良い。まだ自然な供給元が未解決な段階で、無理に存在定理まで抱え込まなかったからじゃ。

そして `ABC038Bridge.lean` の中核 `tailBound_of_channelCount_tail_transport` は、その radical lower bound を `TailBound` へ変換しておる。仮定は

$$
\text{twoTail}(c) \le \bigl(2^{F.\text{channelCount}}\bigr)^\gamma
$$

と

$$
\mathrm{ABC.rad}(c) \le \mathrm{ABC.rad}(u * v)
$$

であり、そこから

$$
\text{twoTail}(c) \le \bigl(\mathrm{ABC.rad}(u * v)\bigr)^\gamma
$$

を導いて \(\text{ABC.TailBound} \, \gamma \, u \, v \, c\) に着地する。
ここでやっていることは、counting spine の出力をそのまま `ABC038` 既存 API の入力形式に合わせることじゃ。特に `Real.rpow_le_rpow` を使って

$$
(2^{F.\text{channelCount}})^\gamma \le (\mathrm{ABC.rad}(u*v))^\gamma
$$

へ運んでいるのは、数学的にも実装的にも素直じゃ。

さらに `quality_le_of_not_bad_with_channelCount_tail_transport` は、その `TailBound` を既存の `ABC.Chernoff.quality_le_of_not_bad_with_tail` へ流す薄い wrapper じゃ。ここで重要なのは、quality theorem 本体を触らずに、bridge 側から供給できる budget と transport を使って quality bound へ到達する形を一度 theorem 名で固定できたことじゃ。まだ full quality sample は閉じておらぬが、少なくとも theorem chain としては

$$
\text{channelCount}
\to
\mathrm{ABC.rad}(c)
\to
\mathrm{ABC.rad}(u*v)
\to
\text{TailBound}
\to
\text{quality}
$$

が見えるようになった。これはかなりの前進じゃ。

## 具体例の意味

`ABC038BridgeExamples.lean` に入った例も良い。
`primitiveWitnessFamilyPack_6_5_3`、すなわち

$$
6^3 - 5^3 = 91 = 7 \cdot 13
$$

を用いて、`TailBound 1 91 1 91` を bridge wrapper から読めることを確認しておる。ここでは `Squarefree 91` を直接 `native_decide` で押し切るのではなく、

* `twoTail_le_sqTail_real`
* `sqTail_eq_one_of_squarefree`
* `Nat.squarefree_mul`

を使って

$$
\text{twoTail}(91) \le 1 \le (2^{\text{channelCount}})^1
$$

と組み立てておる。これは sample として筋が良い。linter や reduction の不安定性を避けつつ、bridge 側の budget が本当に `TailBound` に変わることを見せておるからじゃ。

## 何が閉じたのか

今回閉じたのは、橋の数学の観点では次の一点じゃ。

**counting spine が `ABC038` の `TailBound` 入力まで届いた。**

前回までは `ABC.rad` 下界で止まっておった。今回はそこからさらに `TailBound` へ流せる theorem が入り、quality 系との接続が theorem 名レベルで現実のものになった。まだ full quality sample ではないが、少なくとも「どこまで橋が届くか」という問いに対して、今や答えは

$$
\text{`TailBound` までは届いた}
$$

と言える。これは大きい。

## 良い点

今回の差分の特に良い点は三つある。

まず、前回整理した dependency chain を、そのまま無理なく実装へ落としていること。
設計と実装がねじれておらぬ。ここは信頼できる。

次に、`ABC038Bridge.lean` を独立ファイルとして切ったこと。
これで `ABC038` 本体を汚さず、bridge 側の責務を局所化できておる。こういう薄い wrapper 層は後で効く。

最後に、transport 仮定を無理に消そうとしていないこと。
現時点で未解決なのはまさに `rad c ≤ rad (u * v)` の自然な供給元じゃから、そこを theorem 仮定として残したのは正しい。今の段階で存在定理まで抱えると、また森が燃える。

## 留意点

ただし、今回の接続はまだ **full quality sample** ではない。
差分報告にもあるように、`u + v = c` と両立する radical transport の自然供給はまだ未解決じゃ。つまり、

$$
\mathrm{ABC.rad}(c) \le \mathrm{ABC.rad}(u * v)
$$

をどこから取るかが残っておる。ここが埋まらぬ限り、`quality_le_of_not_bad_with_channelCount_tail_transport` は「仮定つきで quality に届く theorem」であって、「自然な ABC triple から自動で quality sample が閉じる theorem」ではない。そこは率直に言うべきじゃろう。

もう一つ、今回の sample は `u = 91, v = 1, c = 91` という transport-friendly な例じゃ。
これは wrapper の正しさ確認としては非常に良いが、`ABC038` 本来の三つ組らしい非自明な `u + v = c` の状況とはまだ距離がある。だから今回は「橋が `TailBound` へ届く確認」までは成功、「quality 本丸の自然例」はまだこれから、という評価が正確じゃな。

## 次の一手

次はやはり、差分報告の最後にある通り、

**`u + v = c` と両立する radical transport の自然供給元をどう定理化するか**

じゃ。
わっちなら、いきなり `ABC038` 本体に突っ込むより先に、transport hypothesis を供給する中間命題を 2 系統に分けて洗う。

ひとつは、`c` 自身の素因子が `u * v` 側へどう移るか、という **divisibility / radical transport** 系。
もうひとつは、quality 側が本当に `rad (u * v)` だけを必要としているのか、それとも `TailBound` の budget 語彙を `rad c` 側に少し寄せるほうが軽いのか、という **input refactoring** 系じゃ。

今の進捗なら、次の Codex 指示はこうなる。
`ABC038` 用の transport hypothesis を自然に供給する中間命題候補を 2〜3 本洗い出し、各候補について「divisibility ベース」「rad monotonicity ベース」「TailBound 側 input refactoring ベース」のどれに属するかを分類する。Lean 実装に入る前に、最も薄く済む transport route を 1 本に絞る。`

## 最終判断

これは **かなり良い前進** じゃ。
前回までで `ABC.rad` 下界に届いていた counting spine が、今回は `ABC038` の `TailBound` 入力まで届いた。つまり bridge は、counting 系だけでなく quality 系の手前まで実際に伸びた。

ひとことで言えば、
**橋はもう counting の城門を越え、quality の前庭まで来た。**
次に必要なのは、その庭から本丸へ入るための transport の鍵じゃな。
