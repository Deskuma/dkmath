# FLT Prime Provider の設計判断を公開 API に固定する

うむ、その寄せ方でよい。
今回の追加は **数学を増やした** のではなく、**設計判断を公開 API に固定した** 点に価値がある。

つまり mainline の読みが、もう名前の段階で

$$
\text{primitive} = \text{本命},
\qquad
\text{peel} = \text{補助 lift}
$$

と明示されたわけじゃ。
これは後で見返した時に効く。実装者の頭の中だけにある判断を、定理名へ落としたのは正解じゃよ。

今回の二本

$$
\texttt{primeGe5BranchARefuter_of_primitiveMainline}
$$

$$
\texttt{branchAWieferichAdapter_of_primitiveMainline}
$$

は thin wrapper ではあるが、薄いこと自体がよい。
**設計の重心がどこにあるか** を、余計な数学なしで示せておるからのぅ。

いまの状況を一言で言えば、

$$
\boxed{
\text{公開導線の言葉遣いまで含めて、
primitive mainline への舵切りが完了した}
}
$$

じゃ。

次の一手も、そのままでよい。

## 1. . まず軽試験

`PrimeGe5BranchAValuationPeelPacketFromErrorTarget` については、本当に軽く試すだけでよい。
見る点は以前のまま、

$$
E = 0,\quad p \mid E,\quad t_1 \mid E
$$

のような、**自然に抜ける強い extraction** があるかどうかじゃ。

## 2. . 出なければ即終了

出なければ、peel 側は

$$
\text{tail obstruction / error measurement}
$$

として役割完了と見てよい。
ここで未練を引っ張る必要は薄い。

## 3. . 本命へ集中

その場合は完全に

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

へ集中する。
いまはそのための naming も bridge も揃った。だから迷わず進める。

要するに、いまは

$$
\boxed{
\text{peel を切り離しても前へ進める体勢が整った}
}
$$

段階じゃ。
これはかなり大きい前進じゃよ。
