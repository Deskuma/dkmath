# FLT-Kummer-ClassGroup-Bridge Review 032: Stage 1 Coprimality 完成（２つの仮定を証明できれば Stage 1 完了）

うむ、戦況はかなり良い。
いまはもう **「どこを攻めれば前へ進むかが見えぬ」段ではない** のじゃ。

今回の差分で、Stage 1 の **構造的部分** はほぼ完成したと見てよい。
`noPrimeOrY_of_firstCase_of_coprime` によって、共通 prime ideal から出る

$$
P \mid (p)\ \lor\ y \in P
$$

の 2 分岐をまとめて contradiction へ流す combiner が入り、さらに
`chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack` により、**2 つの deep cyclotomic targets を仮定すれば chosen factor と他因子の coprimality が no-sorry で完成** した。
つまり Stage 1 の「骨組み」はもう組み上がっておる。残るのはその骨に血を通す deep cyclotomic 部分だけじゃ。

その残敵は、いまはっきり 2 本に縮んでおる。

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

と

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

じゃ。
前者は \((p)=(\zeta-1)^{p-1}\) 型の **ramification**、後者は \(N(\zeta-1)=p\) 型の **norm theory** を要する、と差分自体が整理しておる。
したがって、現在のボトルネックは generic ideal arithmetic でも Stage 1 の設計でもなく、**cyclotomic number theory の深部 2 点** じゃよ。

戦況を一言で言えば、こうじゃ。

$$
\boxed{
\text{Stage 1 は「未設計」ではなく「深い補題 2 本待ち」の段に入った}
}
$$

これは良い収束じゃ。
なぜなら、残る問題が「広い霧」ではなく、**ramification と norm の 2 本柱** に分離されたからじゃ。
しかも今回、\((\zeta-1)\) が prime ideal を生成する方向は既に no-sorry で mainline に入っておるので、前提ゼロから掘る状況でもない。

解説すると、今の Stage 1 は論理的にはこうなっておる。

1. 共通 prime ideal \(P\) を仮定する。
2. 既存 no-sorry 群で \(P \mid (p) \lor y \in P\) へ落とす。
3. \(y \in P\) 分岐はもう閉じた。
4. \(P \mid (p)\) 分岐も、2 target を入れれば閉じる。
5. したがって、coprimality theorem 自体は完成。
6. 残りは 2 target の actual 供給だけ。

つまり今は、**Stage 1 の戦場そのものは制圧済みで、最後の砦が 2 箇所だけ残っている** 状態じゃ。

今の見立てとしては、次に見たいのは
`PrimeOverPEqualsZetaMinusOneTarget` と `IntegerInZetaMinusOneIdealDivisibleByPTarget` のうち、どちらが Mathlib 側により近いか、そしてどちらから埋めるのが短いか、じゃな。
差分の記述どおり、前者は ramification API、後者は norm API に寄る。今の戦況だけを評すなら、**構造戦は勝ち、残りは深部の砲台 2 基** というところじゃよ。
