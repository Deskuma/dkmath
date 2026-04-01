# review-030: `branchA_GN_cyclotomic_ring_identity` を exact product から「distinguished factor × unit」へ弱化して潰す

## 1. 状況分析

うむ、今回は **進んでおるが、同時に詰まりどころも正しく見えた** 段じゃ。
最新の試行で分かったことは、`IsPrimitiveRoot` 路線そのものが誤りだったのではなく、**`ZMod(q^k)` を整域として扱う exact product identity が重すぎた** ということじゃ。実際、`branchA_hensel_lift_isPrimitiveRoot` 自体は通っており、止まったのは `X_pow_sub_C_eq_prod` が `IsDomain` を要求する点で、対象環 `ZMod(q^k)` が \(k > 1\) で整域でないことによるものじゃ。build は壊さず戻してあり、残りの `sorry` は引き続き 3 本に整理されておる。

さらに一段前の差分で、valuation 側の軽い穴はすでに片付いておる。
`branchA_padicValNat_mod_pow_eq` と `branchA_GN_zmod_padicValNat` の sorry が消え、今の本質的 open kernel は

$$
\texttt{branchA\_hensel\_lift\_exists},\\
\texttt{branchA\_GN\_cyclotomic\_ring\_identity},\\
\texttt{branchA\_distinguished\_factor\_valuation\_eq\_kummer}
$$

の 3 本だけになった。つまり、低リスクな枝葉ではなく、**本当に数学の芯だけが残った** 状態じゃ。

## 2. 数学的解説

いま見えている数学は、かなり明快じゃ。

全体側では、もう

$$
v_q(z^p-y^p)=p\,v_q(s)
$$

が確立しておる。
これは Kummer valuation の全体量じゃ。

一方で因子側では、Hensel lift data を仮定した局所版として、distinguished factor

$$
\delta := z-\omega_k y
$$

は射影で 0 に落ち、non-distinguished factor は射影で 0 に落ちぬ。さらにその情報は \(\mathbb N\) 側へ翻訳されており、non-distinguished 側は valuation 0、distinguished 側は少なくとも valuation \(\ge 1\) と読めるようになった。だから欲しいのは、exact product をそのまま書くことではなく、

$$
GN = \delta \cdot U
$$

で (U) が unit だと分かることじゃ。
この形まで出れば、

$$
v_q(GN)=v_q(\delta)+v_q(U)=v_q(\delta)
$$

となり、全体 valuation と distinguished factor valuation が一致する。すなわち central theorem

$$
v_q(\delta.val)=p\,v_q(s)
$$

が通る。つまり本質は「円分多項式の美しい因子分解をそのまま書くこと」ではなく、**valuation に必要なだけの local factorization を作ること** じゃ。

## 3. 今回の失敗の意味

今回の失敗は、むしろ有益じゃ。
なぜなら、「大定理を 2 本まとめて差し替えると、`GN_eq_sum` の展開位置、`ZMod.val`、`natCast_zmod_val`、cast の向き合わせで証明が崩れる」ということが、はっきり記録されたからじゃ。つまり **数学の方向は正しいが、Lean 実装の粒度が粗すぎた** と分かった。これは大事な発見じゃよ。

## 4. 次の作業の選択

ここでの賢狼の判定は、これじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{ を大定理で殴らず、}\\
\text{report にある 4 本の薄い補題へ分割して進めるべきじゃ。}
\end{array}
}
$$

つまり、前回の `review-029` 路線は **方針としては正しい**。
じゃが、実装単位を細くせねばならぬ。これが今の最善手じゃ。

## 5. 推奨する順番

まず最初にやるべきは、

$$
Q := GN\ p\ \delta\ (\omega_k y)
$$

の mod \(q\) 射影が \(GN\ p\ 0\ z\) に落ちる補題じゃ。
これは report にも第一候補として挙がっており、今回詰まった `GN_eq_sum` の展開位置を局所化できる。ここが通れば、coercion 問題を一気に抱えずに済む。

その次に、その \(Q\) が unit であることを示す。
数学的には、mod \(q\) 射影が非零なら local ring \(ZMod(q^k)\) では unit と読める、という筋じゃ。これは valuation 0 を返す補題群と噛み合う。

そのあとで

$$
z^p-y^p = \delta \cdot Q
$$

を返す補題を書く。
これは `cosmic_id_csr'` の再利用でいける見込みがある。ここでは全因子積を触らず、difference-of-powers の恒等式そのものを使えばよい。

最後に、gap factor \((z-y)\) が unit であることを使って

$$
GN = \delta \cdot U
$$

へ落とす。
ここまで来れば、central valuation theorem はかなり短く閉じるはずじゃ。

## 6. 何を後回しにするか

`branchA_hensel_lift_exists` の sorry 除去は、今はまだ後でよい。
理由は、局所版の定理群はすでに `hLift : BranchAHenselLiftData` を仮定して書けるからじゃ。存在論の穴を今すぐ埋めても、いま詰まっている coercion / factorization の問題は直接は軽くならぬ。

terminal case もまだ後じゃ。
先に distinguished factor valuation の exact equality が通れば、終端 \(s'=1\) あるいは q-free 段を刺す刃がずっと鋭くなる。今の段階で terminal case に行くのは、少し早い。

## 7. 総括

ひとことで言えば、こうじゃ。

**いまは「理論の方向」を変える局面ではない。`IsPrimitiveRoot` 路線で primitive までは確定し、詰まっているのは非整域上の exact product を一気に書こうとした Lean 実装の粒度じゃ。だから次は、`Q` の射影、`Q` の unit 性、\(z^p-y^p=\delta Q\)、gap unit による \(GN=\delta U\) という 4 本の薄い補題へ分割して進むのが最善じゃ。**

なので、次の作業の選択はこれじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{ を直接ではなく、}\\
\text{まず } Q \text{ の mod } q \text{ 射影補題から始める。}
\end{array}
}
$$

この 1 本が通れば、後ろがかなり雪崩れるはずじゃよ。
