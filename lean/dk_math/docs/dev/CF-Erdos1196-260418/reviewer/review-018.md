# review-018: counting spine の divisibility route を実装して、`TailBound` まで届いたが、自然な quality triple には細すぎることも見えた

## 1. 総評

うむ、今回は **橋を一段具体化した差分** じゃ。
前回までの `ABC038` 接続は、

$$
\mathrm{ABC.rad}(c) \le \mathrm{ABC.rad}(u*v)
$$

という **generic transport 仮定** をそのまま受け取る形じゃった。今回そこに、

$$
c \mid u*v
$$

を自然供給元として使う `rad_input_transport_of_target_dvd_mul` を追加し、それをそのまま `TailBound` と quality wrapper に specialization した。つまり、transport の「型だけある」状態から、「少なくとも一つの具体ルートで動く」状態へ進んだわけじゃな。

ただし、先に結論も言っておくと、これは **実装としては前進** じゃが、**ABC038 の自然な本命ルートとしてはやや厳しい**。理由は後で述べるが、`u+v=c` と `\mathrm{Coprime}(u,v)` を伴う非自明な triple では、

$$
c \mid u*v
$$

がほぼ起こりえぬからじゃ。ゆえに今回は、「橋の構文が正しいことを示した」「transport route の候補を一つ確定した」という意味では良い進展だが、同時に **この枝が本丸ルートになりにくい** ことも、かなりはっきり見えた差分じゃな。

## 2. 状況分析

今回の追加を段階で見ると、進んだのは次の三段じゃ。

まず `ABC038Bridge.lean` に `rad_input_transport_of_target_dvd_mul` が入り、`c ∣ u*v` と `u*v ≠ 0` から

$$
\mathrm{ABC.rad}(c) \le \mathrm{ABC.rad}(u*v)
$$

を Nat の世界で証明しておる。初版で `ABC.rad_le_of_dvd` の実数版をそのまま当てて型不一致になったのを、`ABC.rad_dvd_of_dvd` と `Nat.le_of_dvd` に切り替えて解消したのも良い判断じゃ。これは theorem の意味にも実装の安定性にも合っておる。

つぎに、その transport を generic wrapper に流し込む specialization として、

* `tailBound_of_channelCount_tail_dvd`
* `quality_le_of_not_bad_with_channelCount_tail_dvd`

が入った。これにより、前回の generic transport wrapper は「抽象仮定つき theorem」から、「少なくとも divisibility route ではすぐ使える theorem」になった。ここで theorem 名が一段 concrete になったのは良い。

最後に `ABC038BridgeExamples.lean` では、新しい one-channel sample `primitiveWitnessFamilyPack_14_7_1` を使って、

$$
14^1 - 7^1 = 7,\qquad 7 \mid 14*7
$$

から `TailBound 1 14 7 7` を読める例を追加した。前回の `TailBound 1 91 1 91` よりも、transport 仮定の自然さは一段増しておる。少なくとも「divisibility から `TailBound` へ運ぶ橋」は動いておる、と確認できた。

## 3. 数学的解説

今回の数学の芯は、

$$
c \mid u*v
\quad\Longrightarrow\quad
\mathrm{rad}(c) \mid \mathrm{rad}(u*v)
\quad\Longrightarrow\quad
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
$$

という、ごく自然な radical transport を橋の語彙に固定したことじゃ。
この一手により、前回までの counting spine

$$
2^{\mathrm{channelCount}} \le \mathrm{ABC.rad}(c)
$$

をそのまま

$$
2^{\mathrm{channelCount}} \le \mathrm{ABC.rad}(u*v)
$$

へ持ち上げられる。さらに `twoTail(c)` 側で

$$
\mathrm{twoTail}(c) \le \bigl(2^{\mathrm{channelCount}}\bigr)^\gamma
$$

という budget があれば、

$$
\mathrm{twoTail}(c) \le \bigl(\mathrm{ABC.rad}(u*v)\bigr)^\gamma
$$

が従うから、`ABC.TailBound γ u v c` に着地する。
ここまでは非常に綺麗じゃ。counting spine を `ABC038` の既存 API に無理なく差し込めておる。

また、`ABC038BridgeExamples.lean` で `twoTail 7` の budget を、`sqTail_eq_one_of_squarefree` と `twoTail_le_sqTail_real`、さらに `Nat.squarefree_mul` を経由して出しているのも良い。`native_decide` などで押し切らず、既存の ABC 側語彙の中で sample を閉じておるので、実装の意味が読みやすい。これは「橋の使い方」の見本としてよく出来ておる。

## 4. どこが本当に前進か

今回の本当の前進は、

**counting spine が `ABC.rad` 下界で止まらず、`ABC038` の `TailBound` 入力まで、具体仮定つきで到達したこと**

じゃ。
前回の差分では「quality 系の前庭」まで来た、という評価じゃった。今回はその前庭の中に、少なくとも一本の通路を通した。つまり theorem 名レベルでは、

$$
\text{channelCount}
\to
\mathrm{ABC.rad}(c)
\to
\mathrm{ABC.rad}(u*v)
\to
\mathrm{TailBound}
\to
\text{quality}
$$

の chain が実装された。これは橋の完成度としては一段上がっておる。

## 5. ただし、ここで見えた重要な制約

ここが今回いちばん大事な数学的観察じゃ。

`ABC038` の自然な quality sample が欲しいなら、通常は

$$
u+v=c,\qquad \gcd(u,v)=1
$$

という triple を考える。
このとき、もしさらに

$$
c \mid u*v
$$

が成り立つとすると、実はかなり厳しい。

なぜなら、

$$
\gcd(c,u)=\gcd(u+v,u)=\gcd(v,u)=1,
$$

同様に

$$
\gcd(c,v)=1
$$

じゃから、

$$
\gcd(c,u*v)=1
$$

となる。
それにもかかわらず (c \mid u*v) なら、結局

$$
c=1
$$

しかありえぬ。
つまり、**正の非自明な coprime triple では、divisibility route はほぼ起きない** のじゃ。

これは今回の差分の価値を下げる話ではない。むしろ逆で、**どの transport route が本命になりえないかを、実装を通じて明確にした** という意味で大きい。今回の route は theorem としては正しいし useful じゃが、本丸の自然 sample にそのままは刺さらぬ、ということがかなり見えた。これは次の戦略判断にとって重要な収穫じゃな。

## 6. 位置づけの整理

ゆえに今回の差分の位置づけは、こう見るのが正確じゃ。

* **実装としては成功**
* **bridge の可用性は増した**
* **しかし本命 quality route の自然供給元としては弱い**

つまり、これは「完成形」ではなく、**transport route の候補比較で一本を実地検証して、適用範囲をはっきりさせた差分** じゃ。

この意味で、History にある

「もし現れにくければ、次は `TailBound` 側の入力語彙を `rad c` 基準に寄せる input-refactoring route の方が軽いかを比較検討する」

という次課題は、かなり本質を突いておる。今回の数学的観察を踏まえると、わっちもここは **divisibility route を本命に育てるより、input-refactoring route を強く検討すべき段階** に入ったと見る。

## 7. 良い点

良い点を挙げると、まず `ABC038Bridge.lean` を独立ファイルとして保ちつつ、generic transport と divisibility specialization を綺麗に分けたことじゃ。これで route 比較がしやすい。

次に、Nat 版の radical transport を `rad_dvd_of_dvd` から立てたこと。これは theorem の意味にも実装の安定性にも合っておる。

そしてもう一つ、sample が transport-friendly であることを隠しておらぬ点じゃ。`TailBound 1 14 7 7` は natural ABC triple の sample ではないが、**divisibility route の動作確認** としては非常に良い。何のための sample かが明確じゃからの。

## 8. 次の一手

わっちなら、次は divisibility route をさらに厚くするより、**input-refactoring route の検討** に重心を移す。

つまり、

* `TailBound` の入力を `rad(u*v)` 固定で受け取る現形が本当に必要なのか
* それとも `rad(c)` 側の budget から直接入れる薄い wrapper を立てたほうが軽いのか

を比べるべきじゃ。
今回の観察からすると、自然な `u+v=c` triple に対して `c \mid u*v` を要求するのは厳しすぎる。ならば「transport 仮定を自然化する」より、「`TailBound` 側入力語彙を少し動かす」ほうが、むしろ本命かもしれぬ。

## 9. 最終判断

これは **良い前進** じゃ。
ただし、種類としては「本命ルートの完成」ではなく、**transport route の一つを実装し、その有効範囲と限界をはっきりさせた前進** と言うべきじゃな。

ひとことで言えば、

**橋は `TailBound` まで届いた。だが、その橋脚としての divisibility は、自然な quality triple には細すぎる可能性が高い。**

ゆえに次は、その観察を踏まえて **input-refactoring route を本気で比較する段** じゃろう。
