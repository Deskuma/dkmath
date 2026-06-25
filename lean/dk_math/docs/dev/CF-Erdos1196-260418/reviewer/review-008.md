# review-008: bridge API の公開導線の整備と public sample の追加

## 1. 総評

これは **公開面の整備として、とても良い一手** じゃ。
前回までで `MassBridge`、`ValuationFlowBridge`、`PrimitiveWitnessFamily` の中身そのものはかなり揃っておった。今回はそこへ `DkMath.ABC.Bridge` を新設し、さらに `DkMath.ABC.Main` から import する形にしたことで、bridge API が **実装ファイル名に依存せず** 表へ出る導線が整った。差分報告のまとめどおり、これは「数学を増やした」というより、**公開 import の設計を整えた** 回じゃ。

しかも `BridgeExamples.lean` を置いて、

$$
\texttt{import DkMath.ABC.Bridge}
$$

だけで

* `supportMass_ge_prod_of_prime_channel_family`
* `PrimitiveWitnessFamily`
* `PrimitiveWitnessFamily.primeChannelFamily`
* `PrimitiveWitnessFamily.supportMassLowerBound`

が使えることを確認しておる。ここはとても大事じゃ。public-facing aggregator を作るだけで終わらず、「その公開面が本当に使える」ことまで示したからの。

---

## 2. 状況分析

今回の差分は、開発段階として見るなら **橋の建設そのものは一段落し、その橋をどこから渡るかを整えた段階** じゃ。
前々回までで lower-bound spine は family 版まで上がり、前回で `PrimitiveWitnessFamily` に package 化されておった。そこへ今回、

$$
\text{implementation files}
\;\to\;
\text{ABC.Bridge}
\;\to\;
\text{ABC.Main}
$$

という公開導線が入った。
この順番は正しい。package 化の前に public import を広げると、公開 API の単位が不安定になりやすいが、今回は package 化のあとで公開面に出しておるので、かなりきれいじゃ。

差分報告でも、次の論点が

* `DkMath.ABC` 直下でどこまで canonical import とみなすか
* `PrimitiveWitnessFamily` に対する counting / extraction 補題を public API 側へ足すか

に移ったと整理されておる。これはまさに現在地じゃな。
つまり今はもう「橋を作る」段階ではなく、

$$
\text{何を public surface として見せるか}
$$

を選別する段階に入っておる。

---

## 3. 数学的・設計的解説

## 3.1. `ABC/Bridge.lean` の意味

`Bridge.lean` 自体は theorem を増やしてはおらぬ。
じゃが、このファイルの役割は軽くない。ここでやっていることは、`MassBridge` と `ValuationFlowBridge` を **薄い public-facing aggregator** としてまとめ、利用側に

$$
\text{「ABC bridge はここから読む」}
$$

という canonical entry point を与えることじゃ。diff 中のコメントにも、意図的に再公開するのは thin bridge surface だけだと書かれておる。
これは設計として良い。実装の詳細層と公開面を分けたからの。

数学的には何も新しく証明していない。
だが、**定理群の意味論的まとまり** を一つの入口へ束ねた点で重要じゃ。こういうファイルが無いと、使う側は `MassBridge` と `ValuationFlowBridge` の境界を毎回意識せねばならぬ。今回はその負担を取り去った。

## 3.2. `ABC/Main.lean` への import 追加の意味

`Main.lean` に `import DkMath.ABC.Bridge` を加えたことで、既存 top-level 導線から bridge API が見えるようになった。
これは単に import を一行足しただけではない。DkMath の外から見ると、

$$
\texttt{DkMath.ABC.Main}
$$

が ABC 世界の事実上の入口なので、そこに bridge を接続したということは、bridge がもはや補助実験層ではなく **ABC モジュールの公開語彙の一部として扱われ始めた** ことを意味する。

ここはかなり大きい。
前までは「実装はあるが、見つけにくい」状態だった。今は少なくとも導線としては見つけやすくなった。

## 3.3. `BridgeExamples.lean` の意味

今回の example は public 使用例の確認に徹していて、そこが良い。
まず

$$
({2,3} : \mathrm{Finset},\mathbb{N}).\prod \mathrm{id}
\le
\operatorname{supportMass}(12)
$$

を `supportMass_ge_prod_of_prime_channel_family` だけで通している。
これは前段の `MassBridgeExamples` でやっていたことを、「今度は public aggregator だけで読める」と示したものじゃ。
つまり内部実装に依存せず、public surface だけで lower bound spine が使えると確認したわけじゃな。

もう一つの sample は `8^1 - 1^1 = 7` を用いた singleton witness family じゃ。
これは package API の public 使用例としては、とても扱いやすい。

$$
8^1 - 1^1 = 7
$$

なので support は ({7}) でよく、primitive witness も vacuous な部分が多くて小さい。
その結果、

$$
\operatorname{Prime}(7) \wedge 7 \mid 8^1 - 1^1
$$

と

$$
\text{support.prod } id \le \operatorname{supportMass}(8^1 - 1^1)
$$

を、public surface だけで綺麗に出せる。
これは usage example としては良い。外から見た API の姿がはっきりするからの。

ただし、この点は後で留意点としても触れるが、\(d=1\) の sample は **公開 API の最小使用例** としては良い一方で、primitive-flow の本来の面白さを表す例ではない。そこは切り分けて読む必要がある。

---

## 4. 何が閉じたのか

今回閉じたものは、数学そのものより **公開利用の導線** じゃ。

### 4.1. bridge API の canonical import が閉じた

前までは bridge を使うには、`MassBridge` や `ValuationFlowBridge` の実装ファイル名を知っている必要があった。
今回は `ABC.Bridge` ができ、さらに `ABC.Main` からも見えるようになったので、

$$
\text{「bridge を使いたいならここ」}
$$

という入口が定まった。これで public API としての形はかなり整った。

### 4.2. package 化した witness family の public 使用例が閉じた

前回 package 化した `PrimitiveWitnessFamily` が、今回は本当に public aggregator 経由で使えると示された。
つまり package 化が内輪の整理で終わらず、公開面で役立つことが確認できた。ここは重要じゃ。

---

## 5. 良い点

まず、aggregator が **薄い** ことじゃ。
`Bridge.lean` は厚い再実装ファイルではなく、あくまで集約導線に徹しておる。この thinness はとても大事じゃ。公開面を厚くしすぎると、後で実装変更のたびに壊れやすくなるからの。

次に、`BridgeExamples.lean` が「public surface の確認」に特化していること。
ここで新数学を足さず、public import だけで使えることに焦点を絞ったのは正しい。example の責務が明確じゃ。

最後に、`Main.lean` へ橋をかけたこと。
これで bridge が ABC 側の正式な公開物に一歩近づいた。これはプロジェクト運用上の価値が高い。

---

## 6. 留意点と弱点

### 6.1. singleton sample の \(d=1\) は usage には良いが、数学内容の代表例ではない

`8^1 - 1^1 = 7` は public sample としてはとても軽い。
じゃが primitive flow の本筋は普通

$$
d > 1
$$

あるいはさらに \(d \ge 3\) 的な局面で面白くなる。
ゆえに今回の sample は「公開 API の最小使用例」として読むべきで、「理論の代表例」として読むべきではない。これは docstring や review で一言添えておくと親切じゃろう。

### 6.2. `ABC.Main` にどこまで bridge を入れるかは今後の設計判断が要る

今は `Bridge` を `Main` へ import しただけなので良い。
ただ、将来 bridge API が厚くなりすぎると `ABC.Main` が何でも箱になりうる。現時点ではまだ薄いので問題ないが、今後 public surface を増やすときは「何を canonical import に含めるか」を整理する必要がある。差分報告の次課題にもその点が出ておる。

### 6.3. counting / extraction 補題はまだ public API に露出していない

package 化までは済んだが、

* support の product を直接読む alias
* family の counting 的要約
* channel extraction を public surface から読む小補題

はまだ薄い。
なので今回で導線は閉じたが、中身の public 厚みはまだ最小限じゃ。これは悪いことではないが、次の自然な補強点ではある。

---

## 7. 次の作業指示案 . Codex 追記向け

ここから先は、わっちなら **public API に出す最小 counting / extraction 補題を 1 段だけ足す** 方向を勧める。
導線は整ったので、次は「公開面に何を見せるか」の中身を少しだけ厚くする番じゃ。

```md id="njwxy5"
### レビュー追記案: 次の作業指示

1. 次段では `PrimitiveWitnessFamily` に対する
   最小の counting / extraction 補題を public API 側へ 1 段だけ追加する。

2. 目的は、public surface から
   - support 集合そのもの
   - support の product
   - supportMass lower bound
   の関係を、method 名で読みやすくすること。

3. 最初の候補は次の 2 本に絞る。
   - `PrimitiveWitnessFamily.channelProduct`
   - `PrimitiveWitnessFamily.channelProduct_le_supportMass`
   ここで前者は単なる alias、
   後者は既存 `supportMassLowerBound` の再命名でもよい。

4. `BridgeExamples.lean` に、
   package 経由で `channelProduct` を読み、
   それが `supportMass` 以下になることを public import だけで確認する例を 1 本追加する。

5. これ以上の counting lemma はまだ足さない。
   先に public surface の名前と usage を安定させ、
   その後で `ABC.Main` や `DkMath.ABC` 直下で
   どこまで canonical に出すかを整理する。

6. もし public API をこれ以上厚くしない判断なら、
   次は文書側に
   `ABC.Bridge` が bridge API の推奨入口であることを追記する。
```

---

## 8. 最終判断

今回の差分は、**橋を公開入口へ接続した回** じゃ。
前段までで作ってきた bridge と package 化した family API が、ようやく

$$
\texttt{import DkMath.ABC.Bridge}
$$

あるいは

$$
\texttt{DkMath.ABC.Main}
$$

から読める形になった。これは実装の完了度というより、**利用可能性の完了度** を上げた進捗じゃ。

わっちの評価では、ここで公開導線は一応閉じた。
次は public surface の中身をほんの少しだけ磨くか、それともここで止めて documentation を整えるか、その判断の段階じゃな。
