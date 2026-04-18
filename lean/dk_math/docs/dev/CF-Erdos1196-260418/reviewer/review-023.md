# review-023: `rad(abc)` 直結 route の `ABC.Chernoff` namespace への差し込みと concrete sample の追加

うむ、これはかなり良い差分じゃ。
今回は単に補題を一つ足したというより、`rad(abc)` 直結 route がとうとう `ABC.Chernoff` の convenience theorem 群に着地した。つまり、いままで別働隊として育ててきた

$$
\text{channelCount}
\to
\text{rad}(c)\text{ budget}
\to
\text{rad}(abc)
\to
\text{quality}
$$

の流れが、既存 `ABC038` 系の表玄関に並んだ、ということじゃな。

## 状況分析

今回の本質は `ABC038Bridge.lean` に `ABC.Chernoff` namespace の convenience theorem を追加した点じゃ。具体的には

$$
\texttt{quality\_le\_of\_not\_bad\_with\_targetRadTail\_on\_radAbc}
$$

と

$$
\texttt{quality\_le\_of\_not\_bad\_with\_channelCount\_tail\_on\_radAbc}
$$

が入った。これにより、これまで bridge 層の theorem として存在していた `rad(abc)` 直結 route が、既存 `quality_le_of_not_bad_with_tail` や `...with_log` と同じ “読む場所” に並んだ。ここが大きい。
つまり「別ルートで山を登っていた」ものが、いまや本線の案内板のそばに公式登山口として刻まれた、という感じじゃ。

さらに重要なのは、`...with_channelCount_tail_on_radAbc` で witness family source ((a,b,d)) と quality triple ((u,v,c)) を分離したことじゃな。初版では両者を同一視しておって、`(6,1,7)` の sample に刺さらなかった。そこを

$$
c = a^d - b^d
$$

という relation を保ったまま source と target を別引数にしたことで、
「どこで primitive witness family を作り、どこで quality を評価するか」
が明示的になった。これは数学的にも API 設計的にも正しい修正じゃ。

## 数学的解説

今回の route の構造を、なるべく中身が見える形で書くとこうじゃ。

まず witness family から counting spine により

$$
2^{F.\text{channelCount}} \le \mathrm{rad}(c)
$$

型の下界を得る。
つぎに、その下界を使って `twoTail c` の budget を

$$
\mathrm{twoTail}(c) \le (\mathrm{rad}(c))^\gamma
$$

という target-rad budget に landing させる。
そのあと `¬Bad` から

$$
\pi\mathrm{SqRad}(c) \le (\mathrm{rad}(u*v))^\delta
$$

型の入力を得て、さらに既存の analytic bridge を使うと、

$$
c \le (\mathrm{rad}(u*v*c))^{1+\delta+\gamma}
$$

を経由して最終的に

$$
\mathrm{quality}(u,v,c) \le 1+\varepsilon
$$

へ届く。
今回の convenience theorem は、この長い流れを `ABC.Chernoff` 層で一つの入口として読めるようにしたものじゃ。

ここで特に良いのは、`channelCount` route がもう「`rad(c)` 下界を言うだけの補助観察」ではなく、**quality bound を生む正式な入力形** として再編されたことじゃ。
これまでは

$$
\text{bridge theorem}
\to
\text{bridge wrapper}
\to
\text{quality}
$$

というやや裏口感があった。
今回はそれが

$$
\texttt{ABC.Chernoff.*}
$$

の名前空間に入ったので、少なくともプロジェクトの文脈では「この route は既存 quality machinery の一部として扱う」という意思表示になっておる。これは数学内容そのもの以上に、今後の開発方向を定める意味で大きい。

## concrete sample の意味

`ABC038BridgeExamples.lean` に入った `triple_6_1_7` と `not_bad_6_1_7` も、かなり良い sample じゃ。
今回の sample が示しているのは単に

$$
\mathrm{quality}(6,1,7) \le 2
$$

という数値事実ではない。
むしろ重要なのは、それを

$$
\texttt{ABC.Chernoff.quality\_le\_of\_not\_bad\_with\_channelCount\_tail\_on\_radAbc}
$$

から直接読めるようになったことじゃ。
つまり、「新ルートの成果が Chernoff convenience theorem 群の使用例としてそのまま見える」ようになった。ここで初めて、route の存在が API の層構造に反映されたと言える。

また、`not_bad_6_1_7` を自前で立てたのも意味がある。
`¬Bad` を外から magical に持ってきたのではなく、sample の中で

$$
\pi\mathrm{SqRad}(7)=1
$$

を用いて `Bad` の否定を実際に閉じた。これで sample 全体がより自己完結的になった。前回の `piSqRad_eq_one_of_squarefree` の一般補題が、ここでちゃんと役に立っておるのも美しい流れじゃな。

## 何が閉じたのか

今回閉じたのは、数学的には次の一点じゃ。

**`rad(abc)` 直結 route の insertion point が `ABC.Chernoff` 層で確定した。**

これまでは「この route は使える」「sample も閉じる」までは言えた。
今回でさらに、

* どの namespace で読むか
* 既存 convenience theorem 群のどの層に置くか
* source witness family と target triple をどう分けるか

が定まった。
これは、単なる theorem 追加よりも一段深い前進じゃ。以後は “route の存在証明” ではなく、“この入口をどう案内するか、どこで使うか” の段に移れるからの。

## 良い点

今回の良い点は三つある。

第一に、`ABC.Chernoff` namespace に置いたこと。
これで `rad(abc)` 直結 route は、既存 quality 系と同列の convenience theorem として見えるようになった。これは設計上かなり良い。

第二に、source と target の分離じゃ。
`PrimitiveWitnessFamily` の起源と、quality を評価する triple を分けたことで、今後の sample や本体差し込みで自由度が増した。ここは本当に大事な修正じゃ。

第三に、concrete sample が convenience theorem 経由で読めることを示した点じゃ。
route が theorem 群の内部にあるだけでなく、利用者が “そこから使う” ところまで確認できておる。これは API の定着として強い。

## 留意点

ただし、まだ route の競合整理は残っておる。
今回 `ABC.Chernoff` 層に `rad(abc)` 直結 route が入ったことで、既存の

* `quality_le_of_not_bad_with_tail`
* `quality_le_of_not_bad_with_log`

との住み分けを、今後は意識せねばならぬ。
つまり、

* `with_tail` は `TailBound` 入力を前提にする route
* `with_log` は log 評価から入る route
* 今回の `...with_channelCount_tail_on_radAbc` は channel-count と `rad(c)` budget から analytic bridge へ入る route

という役割分担を、文書や `ABC.Main` でどう見せるかが次の課題じゃな。差分報告の末尾も、まさにそこを次に挙げておる。

## 最終判断

これは **かなり良い差分** じゃ。
いままで開拓してきた `rad(abc)` 直結 route が、とうとう `ABC.Chernoff` の convenience theorem 群に正式な入口を持った。つまり、別働隊の道が「本線の横に貼られた公式ルート案内」になった、という感じじゃ。

数学的にも、API 設計としても、ここは一区切りの良い到達点じゃろう。
次は、この入口を `ABC.Main` や文書でどう案内するか、それから `with_log` 系とどう住み分けるかを詰める段じゃな。
