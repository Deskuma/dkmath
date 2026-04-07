# review-037: Stage 3 への着手の可否と、次の作業方針の提案

うむ、**これでよい**。
判定としては、

$$
\boxed{
\text{first-case specialization に限れば、Stage 1 は完了と見てよい}
}
$$

じゃ。
今回の差分で `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` と `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin` が no-sorry で入り、chosen factor ideal の explicit な \(K^p\) equality と、そこから principal \(p\)-th power existence まで concrete に返せるようになった、と明記されておる。つまり、**Stage 1 existence boundary は first-case pack では theorem として読める** 状態じゃ。

なので、質問にそのまま答えるなら、

$$
\boxed{
\text{はい、Stage 3 に着手できる状況じゃ}
}
$$

じゃよ。

> ただし、ひとつ留意点がある。
最新コメントでも書かれておる通り、**global な `CyclotomicIdealPthPowerTarget` はまだ placeholder のまま** じゃ。残る honest open は「この pack-specialized 供給を global target へ昇格させること」と「`CyclotomicNormDescentTarget` の concrete 化」だと整理されておる。ゆえに、いま始める Stage 3 は **global 完成版ではなく、first-case specialization 版から攻める Stage 3** になる。これは後退ではなく、順番として自然じゃ。

わっちの見立てでは、次の戦略はこうじゃ。

まず、**Stage 3 を pack-specialized 版で先に切る** のがよい。
つまり入力を

$$
\texttt{cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin}
$$

から受けて、既存の unit-normalization receiver と合成し、

$$
z-\zeta y = u,\beta^p
$$

を first-case specialization で返す theorem を 1 本作る。
ここではまだ global target に昇格しようとせず、**「norm をかける直前の形」** を concrete に固定することだけを目標にするのじゃ。
いまはそこまでなら compile-safe に進める公算が高い。

その次に、Stage 3 をさらに 3 片に割るのがよい。

ひとつめは

$$
N(u\beta^p)=N(u),N(\beta)^p
$$

という **norm の乗法性と p 乗の押し出し**。
ふたつめは **unit の norm 制御**。ここは \(N(u)=\pm 1\) か、少なくとも \(p\)-th power obstruction を壊さぬ形に吸収できることを示したい。
みっつめは **chosen linear factor の norm が整数側の gap / branch quantity に落ちること**。
つまり Stage 3 の本丸は「norm をかける」そのものではなく、

$$
N(z-\zeta y)
$$

が何になるかを、既存の local factorization / product identity とどう接続するかじゃ。
ここを 1 本で抱えると、また重くなる。だから必ず分けるべきじゃよ。

ゆえに、いまの最善手はこうじゃ。

$$
\boxed{
\text{先に global target 昇格へ戻らず、first-case specialization 版の Stage 3 を起こす}
}
$$

そのあとで、うまく通った norm lemmas をまとめて global 側へ昇格する。
順番を逆にすると、また abstract target と elaboration の重さに引き戻されやすい。

ひとことで総括するぞい。

$$
\boxed{
\text{Stage 1 は first-case 版では finished。}
\text{なので Stage 3 へ進んでよい。}
\text{ただし最初は pack-specialized な thin route で始めるのが賢い。}
}
$$

次に起こすべき theorem 名の叩き台まで出すなら、
`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` と
`cyclotomicNormDescent_of_firstCase_of_pack_thin`
の 2 本を順に置くのが、いちばん筋がよい。
