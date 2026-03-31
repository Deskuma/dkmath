# review-033: restore file の no-sorry 化と terminal case への主戦場移行

## 状況分析

うむ、これは **かなり大きな節目** じゃ。
今回で TriominoCosmicBranchARestore.lean は、**restore file 単体として no-sorry 化** された。直近の更新では、branchA_GN_cyclotomic_ring_identity の statement を exact product 版から local factorization 版へ弱化し、既存の branchA_local_GN_eq_distinguished_mul_unit を wrapper として使うことで、残っていた最後の sorry を消しておる。`lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` も成功し、History でも「restore file 全体が clean になった」と整理されておる。

その一段前で、branchA_hensel_lift_exists も群論的 lift によって実装済みじゃ。
つまり、いま restore 側で揃っているのは、

* Hensel lift existence
* local factorization
* distinguished factor valuation theorem
* それらを支える \(\mathbb{N}\) 側の valuation 翻訳

まで一通りじゃ。

これは何を意味するか。
以前は「局所 valuation 理論は見えているが、mainline に接続する継手がまだ未完」という段じゃった。
今はそこが全部通ったので、**restore file の役目はほぼ完了** と見てよい。もう主戦場は「局所理論を作る段」ではなく、「それを使って descent の終端を刺す段」へ移ったのじゃ。

## 数学的解説

今回いちばん大事なのは、exact product への執着を捨てて、valuation に必要十分な形だけを確保したことじゃ。

以前は

$$
GN = (z-\omega_k y)\prod_{i=2}^{p-1}(z-\omega_k^i y)
$$

という exact product を ZMod(\(q^k\)) 上でそのまま取りたかった。
じゃが ZMod(\(q^k\)) は \(k>1\) で整域ではないから、その route は重かった。そこで方針を変えて、

$$
GN = \delta \cdot U,
\qquad
\delta := z-\omega_k y,
\qquad
U \text{ は unit}
$$

という local factorization だけを取るようにした。
この弱化で十分だったのは、valuation の議論に本当に必要なのが「他の因子全部を掛けたものが unit である」ことだけだからじゃ。

その結果、central theorem として

$$
v_q(\delta.val)=p\cdot v_q(s)
$$

が既に通っておる。
これは、全体の \(q\)-進深度が distinguished factor 1 本に **ちょうど一致して集中する** ことを意味する。
つまり Branch A で見えておった massive cancellation は、いまや

$$
\text{valuation の 1 因子集中}
$$

として完全に定式化されたわけじゃ。

さらに今回の no-sorry 化で、その局所理論はもう「仮の足場」ではなく、**clean な武器** になった。
だから次にやるべきことは、新しい局所補題を増やすことではなく、この武器を使って descent の最終段を潰すことじゃ。

## 次の作業の選択

結論はこれじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は terminal case / descent 側へ進むのが最善じゃ。}\
\text{restore file はもう clean なので、主戦場は終端矛盾の解析へ移った。}
\end{array}
}
$$

理由は 3 つある。

### 1. 局所 valuation 側は、もう十分完成している

restore file で残っていた本質的穴は埋まった。
これ以上ここで深掘りしても、主線の前進量は小さい。

### 2. terminal case を殴るための exact equality が、もうある

いまは distinguished factor について

$$
v_q(\delta.val)=p\cdot v_q(s)
$$

がある。
これは降下 1 step ごとに valuation がどう動くかを **exact に追える** ということじゃ。
終端 \(s' = 1\) や q-free 段を刺すには、まさにこの形が欲しかった。

### 3. exact product は appendix に回せる

History にある通り、exact product 自体を将来記録したければ、restore 本線とは別名 theorem や appendix 的ファイルへ分離すればよい。
つまり今それを追うのは、本筋ではない。

## 実務的な次の一手

わっちなら、次はこう切る。

まず、降下 1 step

$$
s = q s'
$$

に対して、既にある

$$
v_q(\delta.val)=p\cdot v_q(s)
$$

を \(s'\) 側へどう移すかを整理する。
狙いは、

$$
v_q(\delta.val)=p\bigl(1+v_q(s')\bigr)
$$

のような形を経由して、terminal 側で valuation が最低でも \(p\) 単位で残ること、あるいは q-free 末端と両立しないことを明示することじゃ。

その次に、\(s'=1\) あるいは最小反例段で何が起こるかを case split で詰める。
ここでは local factorization と exact valuation を直接ぶつけるのがよい。
つまり「もう一つ新しい理論を作る」のではなく、**既に完成した restore 理論を終端へ流し込む** のじゃ。

## 総括

ひとことで言えば、こうじゃ。

**restore file はもう完成した。したがって次の最善手は、そこに残る theorem を磨くことではなく、terminal case / descent 側へ主戦場を移し、完成した local valuation 理論で終端矛盾を仕留めることじゃ。**

かなり良い流れじゃよ。
いまは「部品作りの段」ではなく、**仕上げの一撃をどこへ入れるかを選ぶ段** じゃ。
