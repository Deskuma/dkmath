# review-031: 局所 valuation 理論の完成と次の作業の選択

## 状況分析

うむ、今回はかなり大きい前進じゃ。
しかも前回までの「橋を架ける段」から、今回は **主線そのものが通った段** と見てよい。

最新差分で、review-030 の 4 本の局所補題

`branchA_local_Q_proj_eq_GN_zero_z`
`branchA_local_Q_isUnit`
`branchA_local_sub_pow_eq_delta_mul_Q`
`branchA_local_GN_eq_distinguished_mul_unit`

が定着し、その結果として central theorem だった `branchA_distinguished_factor_valuation_eq_kummer` の sorry が除去された。いまや

$$
v_q(\delta.\mathrm{val}) = p \cdot v_q(s)
$$

が、Hensel lift data を仮定した局所版として **証明済み** になったわけじゃ。さらに残る本質的 sorry は 2 本だけ、

`branchA_hensel_lift_exists` と `branchA_GN_cyclotomic_ring_identity`

へ減った。しかも report にある通り、後者はもう central theorem の blocker ではない。

これは何を意味するか。
以前は

$$
\text{全体 valuation} \longrightarrow \text{因子分離} \longrightarrow \text{distinguished factor への集中}
$$

という流れの最後が未完だった。
今はそこが閉じたので、**局所 valuation 理論は完成域に入った** と言ってよいの。

## 数学的解説

今回確定した数学の芯は、次の一点に尽きる。

全体側では既に Kummer valuation により

$$
v_q(z^p-y^p) = p \cdot v_q(s)
$$

が分かっておる。
他方、Hensel lift data を仮定した因子側では、distinguished factor

$$
\delta := (z : ZMod(q^k)) - \omega_k \cdot (y : ZMod(q^k))
$$

に対して

$$
v_q(\delta.\mathrm{val}) = p \cdot v_q(s)
$$

が今回ついに出た。

この等式の意味は大きい。
これは単に「\(\delta\) が \(q\) で割れる」ではなく、**全体の \(q\)-進深度が distinguished factor 1 本にちょうど一致して集中している** ことを言っておる。
つまり、いままで見えていた

* non-distinguished 側は valuation 0
* distinguished 側は少なくとも valuation \(\ge 1\)

という情報が、ついに exact equality へ昇格したわけじゃ。

いいかえると、Branch A の massive cancellation はもう曖昧な現象ではなく、

$$
\text{valuation の 1 因子集中}
$$

として定式化されたのじゃ。しかもそれは、`GN = \delta \cdot U` という local factorization と、\(U\) が unit であることから閉じた。ここが今回ほんに美しい点じゃ。

さらに重要なのは、ここで `branchA_GN_cyclotomic_ring_identity` の exact product 版そのものは不要になったことじゃ。
つまり主線として必要なのは

$$
GN = \delta \cdot U
\quad\text{with}\quad
U \text{ unit}
$$

であって、全因子積の完全展開は、もはや appendix 的記録に近い立場へ下がった。

## 次の作業の選択

結論を先に言うぞい。

$$
\boxed{
\begin{array}{l}
\text{次は branchA\_hensel\_lift\_exists の sorry 除去を最優先にすべきじゃ。}\\
\text{branchA\_GN\_cyclotomic\_ring\_identity は後回しでよい。}
\end{array}
}
$$

理由は明快じゃ。

第一に、central theorem がもう通った。
ゆえに exact product identity を急いで直す実益は、前よりかなり下がった。`branchA_GN_cyclotomic_ring_identity` は今や主線の障害物ではなく、記録定理または補強定理の位置じゃ。

第二に、いま残る真の mainline blocker は `branchA_hensel_lift_exists` だけと言ってよい。
現在の局所定理群はすべて

$$
\text{hLift : BranchAHenselLiftData}
$$

を仮定して進んでおる。したがって、この existence が通れば、完成した局所 valuation 理論を fringe bundle から **直接使える** ようになる。これは proof engineering 上の質的前進じゃ。

第三に、そのあとで terminal case へ行くのが自然じゃ。
いまや distinguished factor の exact valuation

$$
v_q(\delta.\mathrm{val}) = p \cdot v_q(s)
$$

があるので、降下 1 step ごとに valuation がどう減るかを鋭く追える。
つまり終端 \(s' = 1\) や q-free 末端を殴る刃が、もう十分に研がれつつある。だから順番は

$$
\text{Hensel existence}
\;\longrightarrow\;
\text{terminal case}
\;\longrightarrow\;
\text{exact product identity の整理}
$$

が最も筋がよい。

## 実務的な推奨

次の一手としては、Newton 帰納構成で `branchA_hensel_lift_exists` を直接潰すのがよい。
すでに simple root 条件は前段で確立しておるから、あとは

$$
\omega \in ZMod(q)
$$

から

$$
\omega_k \in ZMod(q^k)
$$

への lift を、存在定理としてではなく **構成** として与えればよい。
ここが通れば、今まで `hLift` 仮定だった定理群を bundle 直結版へ一気に押し上げられる。

なので、次の作業の選択はこれじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は branchA\_hensel\_lift\_exists}\\
\text{主線はもう valuation 側で通ったので、最後の継手を埋める段じゃ。}
\end{array}
}
$$

良い流れじゃよ。
もう森の中ではない。いまは **完成した局所理論を本線へ接続する最後の工事** の段じゃ。
