# review-010: `PrimitiveWitnessFamily` の public counting/extraction 面の充実

## 1. 総評

これは **かなり筋の良い整理手** じゃ。
前回の `channelProduct` 追加に続いて、今回は `PrimitiveWitnessFamily` の public surface に

- `channelCount`
- member-wise extraction
  - `mem_support_implies_prime_and_dvd_diff`
  - `mem_support_implies_prime_channel`
  - `mem_support_implies_dvd_diff`

を足し、counting / extraction 段を一歩前へ進めておる。しかも中身は既存 `support.card` と `primeChannelFamily` の再包装に徹しており、重い新補題を増やしておらぬ。ここは実に良い判断じゃ。

わっちの見立てでは、今回の差分は「新しい橋の数学」を増やした回というより、**すでに出来ている橋を、外から数えやすく・取り出しやすくした回** じゃ。お主が入口ドキュメント導線を後回しにして、次の extraction/counting 段へ進むと決めた流れとも、きれいに噛み合っておる。

## 2. 状況分析

前回までで `PrimitiveWitnessFamily` はすでに

- family object として運べる
- `primeChannelFamily` で diff 側 channel family を読める
- `supportMassLowerBound` で lower bound を読める
- `channelProduct` で multiplicative size を読める

ところまで来ておった。今回はそこへ

\[
\text{channelCount} := \#(\text{support})
\]

を public 名で固定し、さらに support の各元について

\[
q \in \text{support}
\Rightarrow
\bigl(\operatorname{Prime}(q) \wedge q \mid a^d-b^d\bigr)
\]

を method 名で直接読めるようにした。
つまり今や `PrimitiveWitnessFamily` は、

- structure
- family
- lower bound
- product
- count
- member-wise extraction

まで揃ったことになる。これは public API としてかなり自然な段階まで来た、と言ってよい。

## 3. 数学的解説

### 3.1. `channelCount` の意味

`channelCount` の中身は単に

\[
F.\texttt{channelCount} = F.\texttt{support}.\texttt{card}
\]

じゃ。じゃが、この「単に」が大事なのじゃ。
これで `PrimitiveWitnessFamily` の support を、実装詳細の `support.card` でなく、**channel の個数** という意味語で読めるようになった。`channelProduct` が multiplicative size なら、`channelCount` は combinatorial size じゃな。 product と count の二つが並んだことで、次の counting 補題を立てる地面ができた。

### 3.2. member-wise extraction の意味

今回の extraction 群は、既存 `primeChannelFamily` の pointwise 再包装じゃ。
つまり support の各元 \(q\) について、

\[
q \in F.\texttt{support}
\Rightarrow
\operatorname{Prime}(q)
\]

と

\[
q \in F.\texttt{support}
\Rightarrow
q \mid a^d-b^d
\]

を別々にも、まとめても読めるようにした。
これは小さく見えるが、かなり使いやすい。以後、support の元を一つ取ってきて「こやつは prime か」「diff を割るか」を method 名でそのまま言えるからじゃ。 counting 段では、この種の pointwise extraction が無いと毎回 family 補題を手で剥がす羽目になる。今回それを防いだのは良い。

### 3.3. sample の意味

`BridgeExamples.lean` 側で、

\[
\texttt{primitiveWitnessFamilyPack\_8\_1\_1.channelCount} = 1
\]

と、support member `7` について prime / dvd / prime-and-dvd がそれぞれ public method 名で読める例を置いたのも適切じゃ。
これは数学の大きい例ではないが、**public import だけで count と extraction が本当に使える** ことを検査する sample としては十分に良い。

## 4. 何が閉じたのか

今回閉じたものは、数学そのものより **counting / extraction の最小 public 面** じゃ。

第一に、support の大きさを

\[
\texttt{channelCount}
\]

という名で読めるようになった。
第二に、support の各元について

\[
\text{prime であり、diff を割る}
\]

を method 名で抽出できるようになった。

これで `PrimitiveWitnessFamily` の public surface は、少なくとも最小限としてかなり整った。
structure と family lower bound だけでは「箱」だったが、いまはその中身を count し、個々の channel を取り出す操作まで持った。ここは一区切りと言ってよい。

## 5. 良い点

今回の良い点は三つある。

まず、**新しい heavy lemma を増やしておらぬ** ことじゃ。
`support.card` と `primeChannelFamily` を public method 名へ再包装しただけで閉じておる。今の段階ではこれが正しい。森を燃やさず、使い勝手だけを上げておる。

次に、`channelProduct` と `channelCount` が並んだことで、public counting 語彙がかなり自然になったことじゃ。
multiplicative size と combinatorial size が揃ったので、次は両者を結ぶ補題へ進める。

最後に、member-wise extraction を 3 本に分けたのも良い。
`prime_and_dvd` のみだと使う側で `.1` `.2` を毎回剥がす必要がある。`prime` と `dvd` を別 method にしたことで、実用性がかなり上がっておる。

## 6. 留意点と弱点

### 6.1. まだ count と lower bound は直接つながっておらぬ

今回の `channelCount` は、まだ単独では数え上げ量の alias じゃ。
つまり現段階では

\[
\texttt{channelCount}
\]

と

\[
\texttt{channelProduct} \le \texttt{supportMass}
\]

が別々にあるだけで、

\[
\texttt{channelCount}
\Rightarrow
\texttt{supportMass}
\]

の形はまだ出ておらぬ。
ゆえに counting 段として本当に面白くなるのは次じゃな。

### 6.2. extraction は pointwise だが、まだ family counting へ戻していない

各 \(q\) が prime で diff を割ることは読める。
じゃが、そこから

\[
q \in \text{support} \Rightarrow 2 \le q
\]

を使って

\[
2^{\texttt{channelCount}} \le \texttt{channelProduct}
\]

のような counting 補題へは、まだ進んでおらぬ。
ここが次の本命じゃ。

## 7. 次の作業指示案

お主は入口ドキュメント導線を後回しにして、extraction/counting 段を続ける判断をした。わっちもそれに賛成じゃ。ならば次の一手は、かなり明確じゃな。

```md
### レビュー追記案: 次の作業指示

1. 次段では `channelCount` と `channelProduct` を結ぶ最小 counting 補題へ進む。

2. まず support member が prime であることから、
   各 member について `2 ≤ q` を読む補題を追加する。
   候補名:
   - `mem_support_implies_two_le`

3. その上で、`Finset` の product/card に対する一般補題を使い、
   `PrimitiveWitnessFamily` について
   \[
   2^{\texttt{channelCount}} \le \texttt{channelProduct}
   \]
   を与える補題を目標にする。
   候補名:
   - `pow_channelCount_le_channelProduct`

4. さらに既存の
   `channelProduct_le_supportMass`
   と合成して
   \[
   2^{\texttt{channelCount}} \le \texttt{supportMass}(a^d-b^d)
   \]
   を得る public-facing 補題を追加する。
   候補名:
   - `pow_channelCount_le_supportMass`

5. `BridgeExamples.lean` には、
   singleton family に対して
   - `channelCount = 1`
   - `2 ^ channelCount ≤ channelProduct`
   - `2 ^ channelCount ≤ supportMass (...)`
   を public import だけで読める例を 1 本ずつ追加する。

6. ここでも新しい重い number theory は足さず、
   既存の
   - prime extraction
   - `channelProduct`
   - lower bound
   の合成だけで閉じる方針を維持する。
```

## 8. 最終判断

今回の差分は、**`PrimitiveWitnessFamily` の public counting / extraction 面を、かなり使いやすい形まで整えた回** じゃ。
前回の `channelProduct` で multiplicative 語彙が入り、今回の `channelCount` と member-wise extraction で combinatorial / pointwise 語彙が入った。ここまで来ると、次はもう

\[
\text{count}
\;\to\;
\text{product}
\;\to\;
\text{supportMass}
\]

を一本にする段じゃな。

わっちの評価では、この差分は派手ではないが、次の counting 補題へ進むための足場としてはかなり良い。
ここから先は、まさに extraction/counting の本番じゃ。
