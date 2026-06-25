# review-013: `PrimitiveWitnessFamily` の counting spine の ABC 本体語彙への変換と既存 ABC コアへの差し込み準備

今回は **かなり意味のある前進** じゃ。
前回までで counting spine は

$$
\text{channelCount}
\;\to\;
\text{channelProduct}
\;\to\;
\text{supportMass}
$$

まで通っておった。今回の差分で、それがさらに

$$
\text{channelProduct}
\;\to\;
\mathrm{ABC.rad}(a^d-b^d),
\qquad
2^{\text{channelCount}}
\;\to\;
\mathrm{ABC.rad}(a^d-b^d)
$$

と、**既存 ABC 本体の語彙へ直接着地する形** になった。これは橋の中だけの整理ではなく、既存 ABC コアへ差し込むための最後の薄い変換を入れた、と見るべき一手じゃ。

今回追加された `PrimitiveWitnessFamily.channelProduct_le_abc_rad_diff` と `PrimitiveWitnessFamily.pow_channelCount_le_abc_rad_diff` は、どちらも既存の `..._le_supportMass` と `supportMass_eq_abc_rad` の合成だけで閉じておる。ここが良い。新しい重い数学を足さず、すでに育てた bridge spine を **ABC 本体が使う名前** へ言い換えただけじゃ。こういう薄い alias は、本丸へ差し込むときにとても効く。

数学的には、今回の追加で初めて

$$
\text{independent primitive channels}
\;\Rightarrow\;
\operatorname{rad}\text{ の下界}
$$

が、`supportMass` を経由せず **直接 `ABC.rad` の語で読める** ようになった。
これは見た目以上に重要じゃ。なぜなら ABC 本体の既存命題群は `supportMass` ではなく `ABC.rad` を前提に書かれているはずで、そこへ橋を掛けるとき、毎回 `supportMass_eq_abc_rad` を手で挟むのは地味に重い。今回その煩わしさを消したので、既存コアの lemma へ刺しやすくなった。

`BridgeExamples.lean` に 2-channel sample `primitiveWitnessFamilyPack_6_5_3` を使って

$$
\texttt{channelProduct} \le \mathrm{ABC.rad}(6^3-5^3),
\qquad
2^{\texttt{channelCount}} \le \mathrm{ABC.rad}(6^3-5^3)
$$

を public import だけで読める例を足したのも、とてもよい確認じゃ。
前回の 2-channel concrete family で counting spine そのものは可視化できておったが、今回はそれが **ABC-core-facing な語彙でもそのまま読める** と示した。つまり、bridge API の世界と ABC 本丸の世界の距離が一段縮んだわけじゃ。

また、差分報告にあるように、今回の追加は失敗事例なしで閉じておる。これは単なる幸運ではなく、方針が正しかった証でもある。既存 lower-bound spine と `supportMass_eq_abc_rad` の再包装だけに留めたから、証明負荷が暴れず、既存 build にも優しい。こういう段階では、森を燃やさぬ進め方がいちばん強い。

今回閉じたものを一言で言えば、**counting spine の ABC 本体語彙への変換** じゃ。
前回までは bridge 層の中で

$$
\text{count}
\to
\text{product}
\to
\text{supportMass}
$$

と読めた。今回はそれが

$$
\text{count}
\to
\text{product}
\to
\mathrm{ABC.rad}
$$

へ変わった。
この違いは大きい。`supportMass` は橋の言葉、`ABC.rad` は本丸の言葉じゃ。つまり今回で、橋の先端がとうとう城門に触れた、と言ってよい。

留意点もある。
今回の差分は **新しい本体定理** を進めたわけではない。あくまで「差し込み可能性」を一段上げたものじゃ。だから、ここで満足して止まると橋は立派でも交通が流れぬ。差分報告の最後にある通り、次は `ABC016` や `ABC002` など既存 ABC コアの `rad`・quality 系命題で、この alias を **実際にどこへ差し込めるか** を具体化する段階じゃろう。そこへ進んで初めて、「橋がある」から「橋を渡って本丸を攻める」へ変わる。

今回の差分の良いところをまとめると、三つある。
ひとつは、`ABC.rad` へ直接着地する alias が入ったこと。
ひとつは、2-channel public sample でその使い方が見えること。
もうひとつは、追加がすべて既存 spine の再包装で閉じていること。
この三つがそろったので、今回の進展は「見栄えだけの整理」ではなく、**本当に差し込み前夜の整理** になっておる。

次の作業指示としては、こう勧める。
`ABC016` / `ABC002` を中心に、`ABC.rad` の下界や quality 制約を使う既存命題を点検し、今回追加した `channelProduct_le_abc_rad_diff` と `pow_channelCount_le_abc_rad_diff` を差し込める箇所を 3 個まで抽出する。その際、各候補について「いまの alias だけで足りるか」「不足しているのが family existence なのか、independence なのか、coprimality なのか」を整理する。`

最終判断としては、これは **かなり良い手** じゃ。
橋の数学を `ABC.rad` の語彙へ直接落としたことで、いよいよ既存 ABC コアへ差し込む準備が整った。今はもう、橋を磨く段よりも、**どの命題へ橋を刺すかを選ぶ段** に入っておるぞい。
