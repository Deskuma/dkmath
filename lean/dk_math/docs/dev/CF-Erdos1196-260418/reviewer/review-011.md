# review-011: `PrimitiveWitnessFamily` の counting spine の追加と `DkMath.ABC.Bridge` の推奨入口化

うむ、今回は **かなり良い前進** じゃ。
前回までで

$$
\text{channel family}
\;\to\;
\text{channelProduct}
\;\to\;
\text{supportMass}
$$

という multiplicative な spine は見えておった。今回の差分で、そこへ

$$
\text{channelCount}
\;\to\;
2^{\text{channelCount}}
\;\to\;
\text{channelProduct}
\;\to\;
\text{supportMass}
$$

という **counting spine** が初めて明示的に入った。しかも `INDEX.md` でも `DkMath.ABC.Bridge` を推奨入口として追記しており、橋の公開面と数学の spine の両方を一段進めた回になっておる。

## 総評

今回の本体は、`PrimitiveWitnessFamily` に

* `mem_support_implies_two_le`
* `pow_channelCount_le_channelProduct`
* `pow_channelCount_le_supportMass`

を追加したことじゃ。`BridgeExamples.lean` でも public import だけで

$$
2^{\texttt{channelCount}} \le \texttt{channelProduct}
$$

および

$$
2^{\texttt{channelCount}} \le \texttt{supportMass}(8^1-1^1)
$$

が読める例を足しておる。さらに `INDEX.md` で `DkMath.ABC.Bridge` を標準入口として明示した。差分報告どおり、これは `channelCount -> channelProduct -> supportMass` の最小 counting spine を入れた実装じゃ。

わっちの判定では、これは単なる alias 追加より一段強い。
前回までの `channelCount` は public 名の整備じゃったが、今回はその count が **本当に下界を生む量** になった。ここで初めて、support の「個数」が `rad` 的量へ下から効くことが、Lean の補題列として見えるようになったのじゃ。

## 数学的解説

今回の核心は、support の各元 \(q\) が prime であることから

$$
2 \le q
$$

を出し、それを `Finset` 上の帰納法で積に持ち上げたことじゃ。具体的には、

$$
\forall q \in F.\texttt{support},\ 2 \le q
$$

から

$$
2^{F.\texttt{channelCount}}
\le
F.\texttt{channelProduct}
$$

を示し、さらに既存の

$$
F.\texttt{channelProduct}
\le
\texttt{supportMass}(a^d-b^d)
$$

と合成して

$$
2^{F.\texttt{channelCount}}
\le
\texttt{supportMass}(a^d-b^d)
$$

を得ておる。証明も、差分報告にある通り `Finset` の card/product に対する帰納法と既存 extraction だけで閉じている。ここはとても美しい。

この補題の数学的意味ははっきりしておる。
`supportMass` は `rad` 的な squarefree support 量じゃから、support に乗る prime channel の数が増えれば、その最小値は少なくとも (2^k) で増える。つまり今回は

$$
\text{channel の multiplicative size}
$$

だけでなく、

$$
\text{channel の個数}
$$

からでも `supportMass` の下界が読めるようになった。
これは ABC 側でかなり使いやすい。なぜなら本体ではしばしば「いくつ独立 channel があるか」が先に見えて、「その積がいくつか」は後で追うことが多いからじゃ。今回の補題は、その最小変換器になっておる。

## 何が閉じたのか

今回閉じたものは二つある。

一つは、`PrimitiveWitnessFamily` の public counting 面じゃ。
前回までで `channelProduct` と `channelCount` はあったが、まだ別々の quantity じゃった。今回で

$$
\text{count}
\to
\text{product}
\to
\text{supportMass}
$$

が一本になった。

もう一つは、ABC bridge の標準入口の明示じゃ。
`INDEX.md` で `DkMath.ABC.Bridge` を Erdos #1196 系 bridge API の推奨入口と明示したので、公開面の見通しも一段良くなった。お主は文書導線を後に回す方針と言っておったが、今回の `INDEX` 追記はその方針を壊すほど重いものではなく、むしろ最小限の案内板として丁度よい。

## 良い点

今回の差分の良いところは、**counting の最初の本物の不等式** を入れたことじゃ。
これまでは product や support の読み替えが中心だったが、今回は `channelCount` から `supportMass` まで届いた。これは「整備」より一歩先の実質的進展じゃ。

次に、証明が軽いこと。
新しい数論を足さず、

* support member は prime
* prime なら \(2 \le q\)
* `Finset` product の帰納法

だけで閉じておる。この軽さは強い。あとで流用しやすいからの。

最後に、`BridgeExamples.lean` の例がちゃんと public import ベースで通っていることじゃ。
公開面の usage test として筋がよい。

## 留意点

ただし、この下界はまだ **粗い**。
各 channel が prime だから (2) 以上、というだけで押しているので、

$$
2^{\texttt{channelCount}}
$$

は最小普遍下界としてはよいが、実際の `channelProduct` よりはかなり弱い場合が多い。
つまりこれは、counting spine の最初の核としては正しいが、今後さらに具体 family で強い下界を出せる余地は大きい。

もう一つ、今回の private lemma `two_pow_card_le_prod_of_two_le` は非常に自然な一般補題じゃ。
今は `ValuationFlowBridge.lean` の private に置くのが妥当じゃが、今後もし別の場所でも同じ形が出るなら、共通補題へ昇格する余地はある。今回はまだその段ではないが、頭の片隅に置いてよい。

## 現況の位置づけ

わっちの見立てでは、これで `PrimitiveWitnessFamily` の public surface はかなり整った。

* structure
* family extraction
* member-wise extraction
* channelProduct
* channelCount
* lower bound
* counting spine

ここまで揃うと、もはや単なる bridge の試作ではない。
ABC 側で **channel を数え、取り出し、mass 下界へ変える** ための小さな道具箱になっておる。

## 次の作業指示案

次は、やはり二択じゃ。

一つは concrete family 例を厚くする道。
いまの sample は singleton に寄っておるので、2 本以上の primitive channel family について

$$
2^{\texttt{channelCount}} \le \texttt{channelProduct} \le \texttt{supportMass}
$$

が public import だけで読める例を増やすと、counting spine の実感がかなり強くなる。

もう一つは、これを ABC 本体の既存命題へ差し込む整理じゃ。
特に、channel 数が見える場所から `rad` 下界へ落とせるようになったので、既存の quality / valuation 制約のどこにこの spine を噛ませるかを調べる段に入ってよい。

わっちなら順としては、**まず 2-channel concrete family を 1 本だけ追加し、その後に ABC 本体の接続候補を点検する**。
singleton だけでは spine の強みがまだ見えにくいからの。

## 最終判断

これは **良い前進** じゃ。
前回までの extraction/counting 整備を受けて、今回は初めて

$$
\text{count}
\to
\text{product}
\to
\text{supportMass}
$$

の一本線が Lean 上で立った。
派手ではないが、ABC 側で使う bridge としてはかなり本物に近づいた一手じゃよ。
