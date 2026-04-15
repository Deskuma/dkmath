# review-029: `branchA_GN_cyclotomic_ring_identity` を exact product から「distinguished factor × unit」へ弱化して潰す

## 1. 現状分析

いまの到達点は、かなり良い。
`branchA_hensel_lift_isPrimitiveRoot` により、lift した \(\omega_k\) が **primitive \(p\)-th root** であること自体は確定した。ところが、その先で使いたかった `X_pow_sub_C_eq_prod` は `IsDomain R` を要求し、対象環 \(R = ZMod(q^k)\) は \(k>1\) で整域ではないため、そのまま exact product identity へは進めなかった。つまり、**詰まっている場所は primitive root の側ではなく、非整域上での因子分解の書き方** じゃ。

他方で、周辺の足場は十分にある。
全体側では

$$
v_q(z^p-y^p)=p\,v_q(s)
$$

が既に立っており、`GN % q^k` 側の valuation も sorry なしになった。さらに Hensel lift data を仮定した局所版では、distinguished factor の射影が 0、non-distinguished factor の射影が非零、そしてそれらが \(\mathbb N\) の `padicValNat` へ翻訳されるところまで済んでいる。つまり **valuation の 1 因子集中を言うための脇道具は、ほぼ揃っておる**。

## 2. 数学的解説

いま本当に欲しいのは、

$$
GN = (z-\omega_k y)\cdot \prod_{i=2}^{p-1}(z-\omega_k^i y)
$$

という **全因子の exact product** そのものではない。
欲しいのは、central theorem を閉じるのに十分な、もっと弱い形じゃ。

つまり

$$
GN = (z-\omega_k y)\cdot U
$$

で、しかも

$$
U \in (ZMod(q^k))^\times
$$

すなわち (U) が **unit** であることが示せればよい。
これが得られれば、

$$
v_q(GN)=v_q(z-\omega_k y)+v_q(U)
$$

であり、unit 側は valuation 0 じゃから

$$
v_q(z-\omega_k y)=v_q(GN)=p\,v_q(s)
$$

が従う。
つまり exact product identity が要るのではなく、**distinguished factor × unit** という local ring 的な分解があれば十分なんじゃ。

## 3. 次の作業の選択

わっちの判定は、これじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{ を exact product から} \\
\text{「distinguished factor × unit」へ弱化して潰すべきじゃ。}
\end{array}
}
$$

つまり、前回まで考えていた「全因子積をそのまま出す」方針は、`IsDomain` 障壁のせいで少し重すぎる。
ここで方針転換して、**local Artinian ring \(ZMod(q^k)\) に合った形** に落とすのがいちばん筋がよい。

## 4. 推奨する数学ルート

いちばん有望なのは、次の流れじゃ。

まず

$$
F(X):=\sum_{j=0}^{p-1} X^j y^{p-1-j}
$$

を \(ZMod[q^k](X)\) の多項式として見る。
これは \(X=z\) で評価すると \(GN,p,(z-y),y\) になる。
そして \(\omega_k^p=1,\ \omega_k\neq 1\) から、幾何級数の恒等式で

$$
F(\omega_k y)=0
$$

が出るはずじゃ。
すると多項式の因子定理で

$$
F(X)=(X-\omega_k y),Q(X)
$$

という形に落とせる見込みがある。
ここで必要なのは整域ではなく、**(X-\omega_k y) で割れる** という線形因子の事実じゃ。これは exact product よりずっと軽い。

次に、\(Q(\omega_k y)\) が unit であることを示す。
ここでは simple root 条件

$$
(p:!ZMod(q)),\omega^{p-1}\neq 0
$$

が効く。直観的には \(Q(\omega_k y)\) は導関数 \(F'(\omega_k y)\) に対応し、その mod \(q\) 射影が非零だから、\(ZMod(q^k)\) でも unit と読めるはずじゃ。
さらに distinguished factor の射影が 0 であることから

$$
z-\omega_k y \in q\cdot ZMod(q^k)
$$

なので、\(z\) を \(\omega_k y\) の近傍点と見て \(Q(z)\) も unit のまま保たれる、と期待できる。

すると評価点 \(X=z\) に戻して

$$
GN = (z-\omega_k y)\cdot Q(z)
$$

かつ \(Q(z)\) unit。
これで欲しかった

$$
GN = \delta \cdot U
$$

が出る。
ここまで来れば、既に確立済みの全体 valuation と unit valuation 0 を合わせて、central theorem

$$
v_q(\delta.val)=p\,v_q(s)
$$

へ押し切れる。

## 5. 何を後回しにするか

`branchA_hensel_lift_exists` の sorry 除去は、**今は後回しでよい**。
理由は、いま進めるべき局所定理は既に `hLift : BranchAHenselLiftData` を仮定して書けるからじゃ。存在論の穴をすぐ埋めなくても、mainline の数学はまだ押せる。

terminal case も、まだ少し早い。
distinguished factor の exact valuation が出れば、降下 1 step ごとの減少量が鋭く読めるようになる。その後に終端 \(s'=1\) を殴る方が、ずっと強い刃になる。

## 6. まとめ

ひとことで言えば、こうじゃ。

**いま詰まっているのは primitive root 側ではなく、非整域 \(ZMod(q^k)\) 上で exact product identity を要求したことじゃ。だから次は exact product を諦め、\(GN = \text{distinguished factor} \times \text{unit}\) を目標に弱化した local factorization route へ切り替えるのが最善じゃ。これが通れば central valuation theorem が閉じ、その後に Hensel existence、最後に terminal case へ進むのが筋じゃ。**

なので、次の作業の選択はこれじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{ を} \\
\text{「distinguished factor × unit」版へ言い換えて潰す。}
\end{array}
}
$$

これが、いまいちばんよく進む道じゃよ。
