# NOTE-032 教科書: Frobenius 固定点を数えて最終矛盾を得る

日付: 2026-11-02。
前章: [円分指標核上の有限加法指標](TEXTBOOK-N032-CYCLOTOMIC-EXTENSION-CHARACTER-261102.md)。
実装: `FiniteFixedQuotient`、`FiniteFieldFrobeniusFixed`、
`EllipticFrobeniusFixedReduction`、`FreyGoodReductionTowerObstruction`。

今回、実際の良還元を使う最終矛盾の別経路を完成した。
同じ曲線で `N=#E(F_ell)` とし、位数 `p^N` の巡回段と共鳴住所の吸収が与えられれば、
実際の Frobenius 固定点の数から `p^N≤N` を導いて矛盾する。
新しい終点に `hCH` はない。

これは Frobenius の特性方程式そのものの完成ではない。
その独立した定理は未実装だが、新しい最終経路では必要な入力から外れた。
大域分裂、指定された長さの巡回塔、共鳴する悪い住所の吸収は依然残り、一般 `hno` は未完成である。

## 1. レビューの制約と実装方針

最新の `__REVIEW.md` は、旧終点の `hCH` に含まれる `N` が
塔の指数でも有限体点数でもあることを指摘している。この制約は保持する。

上流の `frobenius_cayleyHamilton_on_torsion` は、実際の良還元写像と
有限体上の特性方程式を合成して、標数0の捩れ点上の関係式を導く。
ただし有限体側の `frobCharEqOnPoints_of_frobenius` は、その先に
`kerDeg_frobEnd_line_one`、等方的な捩れ上の関係式などの基礎定理を必要とする。
標数0への輸送を記した275行だけで証明全体が閉じるわけではない。

一方、最終用途では、局所吸収を大域化した後に既に

\[
\sigma P-P\in K\qquad(P\in E[p^N])
\]

が全 Galois 元について得られる。そこで今回は、実際の Frobenius について
この作用差の核を直接数える。特性方程式の係数や isogeny の次数を構成する必要がない。

## 2. 有限群の核・像の個数だけで固定点の下界を得る

有限可換群 `T` と加法自己準同型 `φ`、部分群 `K` があり、全ての `x∈T` に対して
`φx-x∈K` とする。`δ=φ-id` とおくと

\[
\operatorname{im}\delta\subseteq K,\qquad
|T|=|\ker\delta|\,|\operatorname{im}\delta|
\le |\operatorname{Fix}(\varphi)|\,|K|.
\]

`FiniteFixedQuotient.card_le_card_fixed_mul` はこの評価を証明する。
巡回性・素数性・特性方程式は要求しない。
特に `|T|=n²`、`|K|=n>0` なら

\[
\boxed{n\le|\operatorname{Fix}(\varphi)|}.
\]

曲線への適用では、実際の `T=E[n]` と実際の Galois 作用を使う。
点群内の吸収先 `K` を `E[n]` に引き戻した群の濃度は `|K|` 以下。
`K⊆E[n]` の同一視や別の群への置換は不要である。
`|E[n]|=n²` は既存の倍写像・全捩れ濃度の定理から供給する。

## 3. 大きな剰余体の Frobenius 固定元を有限体へ降ろす

`F` を有限体、`κ` をその任意の拡大体とする。
`FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq` は

\[
x^{|F|}=x\quad\Longrightarrow\quad
\exists a\in F,\ \iota(a)=x
\]

を証明する。`κ` の有限性も代数閉性も仮定しない。

もし `x` が `F` の像の外にあれば、`F` の全元に `x` を追加した `Option F` から
`κ` への単射ができる。その `|F|+1` 個の元は全て `X^|F|-X` の根になる。
これは非零多項式の次数 `|F|` を越え、矛盾する。

任意の延長付値環 `A` の剰余体 `κ(A)` 全体を `F_q` とみなしてはいけない。
今回降ろすのは、実際に `q` 乗で固定された座標だけである。

## 4. 同じ整数モデルの実際の還元を構成する

有理曲線 `E`、整数モデル `W`、等式 `W.map ℚ = E` を固定する。
指定された `q` 上の付値環 `A` で、同じ `W` の係数を `A` に入れる。

`integerReduction` は、一般ファイバーのモデル等式による点同型、既存の
`modelReduce`、剰余モデルの等式による点同型を合成する。
標的は同じ `W` を `κ(A)` に写した曲線であり、点の二座標は元の剰余のままである。

`q∤n` なら `A.valuation n=1`。
良還元では全点が滑らかに還元するので、既存の
`EllipticSmoothTorsionReduction.reduce_injOn_torsion` が使える。
モデル同型が加法と可換することも含めて

\[
\operatorname{red}:E[n]\hookrightarrow W(\kappa(A))
\]

という実際の単射を得る。これが `integerReduction_injOn_torsion` である。
還元単射性や座標整性を新しい仮定にしていない。

## 5. 実際の Frobenius 固定捩れ点は `W(F_q)` へ単射に入る

`σ` を同じ `A` の実際の算術 Frobenius とする。
`P∈E[n]`、`σP=P` とする。`P=O` の場合は有限体の `O` を選ぶ。
有限点なら `q∤n` によって両座標 `x,y` は `A` に入る。
点の固定性は `σx=x`、`σy=y` を与え、実際の剰余上の Frobenius 公式から

\[
\bar x^q=\bar x,\qquad\bar y^q=\bar y
\]

となる。前節の有限体降下により、両座標は `ZMod q` の像に入る。
非特異性は体の埋込みに沿って反映されるため、元の曲線の実際の有限体点が得られる。

`finitePointEmbedding` はこの有限体点の座標埋込みを明示する。
`exists_finite_point_of_fixed_torsion` は、その像が `integerReduction P` と一致する点を取り出す。
取り出した有限体点が同じなら還元像も同じで、前節の単射性から元の捩れ点も同じ。
従って

\[
\boxed{\#E[n]^{\sigma=1}\le\#W(\mathbb F_q)}.
\]

これは `card_fixed_torsion_le_finite_points`。
固定捩れ点からの単射であり、有限体点全体への全射は主張しない。

## 6. 一般の曲線で、作用差の吸収から有限体点数の下界へ

二つの計数評価を組み合わせた一般終点が

```lean
torsion_index_le_finite_point_count_of_absorbing
```

である。楕円曲線 `E`、その整数モデル `W`、良還元素数 `q`、`q∤n`、
実際の Frobenius `σ`、有限部分群 `|K|=n` を入力する。
同じ点上で `σP-P∈K` が全ての `P∈E[n]` について成立すれば

\[
\boxed{n\le\#W(\mathbb F_q)}
\]

となる。この一般定理には Cofixed 直線、巡回性、塔、`hCH` は不要である。

## 7. Frey の最終終点では点数と塔の指数を固定する

`exists_good_prime_ne` は、`p+|Δ|+1` 以上の素数を選び、
`ell≠p` かつ `ell∤Δ` を供給する。存在しない良還元素数を仮定しない。

良還元素数 `ell` を選んだ後に

\[
N=\texttt{S.goodReductionPointCount ell}
=\#(S.\mathrm{curve})(\mathbb F_{\ell})
\]

と固定する。良還元と有限体の有限性、無限遠点の存在により `N>0`。
同じ Cofixed 直線の底を含む大域安定な巡回 `K` が `|K|=p^N` を満たすとする。

`p` 上の吸収、非共鳴・2・3の吸収、良還元の慣性固定性は既存の実際の定理から供給する。
共鳴する悪い住所の `hbad` を加えれば、絶対慣性の大域生成によって
全 Galois 元の変化量が同じ `K` に入る。

新しい終点は、選んだ `ell` 上の付値環と Frobenius を内部で構成する。
`ell≠p` から `ell∤p^N` を得て、前節を `n=p^N` に適用する。

\[
p^N\le N<p^N
\]

となり矛盾する。

```lean
residual_cofixed_point_count_tower_resonant_inertia_impossible
```

の公開型には独立な `N`、`σ`、`A`、`hCH` はない。
`hcard` と `hbad` の指数は、ともに実際の `goodReductionPointCount ell` を使っている。
任意の長さの段を、この必要な長さの段と見なすことはできない。

## 8. 一般 `hno` に残るもの

新しい最終経路で残る局所入力は、これまでと同じく

\[
q\ge5,\quad q\ne p,\quad q\mid abc,\quad q\equiv\pm1\pmod p
\]

の住所での高次捩れの吸収である。また `N=#E(F_ell)` の長さの大域巡回段の存在は入力。
前章の有限加法指標を円分体の類群・単数へ接続し消滅させることと、
巡回段を必要な長さまで反復構成する工程は残る。
Mazur/Eisenstein specialization の幾何は、共鳴住所などの入力を実際に供給する際の残件である。

一般の Frobenius Cayley–Hamilton 定理は引き続き未実装だが、
今回の最終計数経路の前提として移植する必要はなくなった。
未証明の `hCH` を別名の特性方程式 provider に移していない。
一般 `hno` や大域巡回段の存在を未証明の定数で追加していない。

## 9. 回帰例と依存監査

- `F_25` の5乗固定元が `F_5` に降りることと、`F_25` 全体は5乗固定ではないこと。
- `ZMod 25 × ZMod 25` の剪断作用で、625個の元から少なくとも25個の固定点を得ること。
- 作用差の吸収を外すと、同じ下界は導けないこと。
- `F_5` 上の実際の曲線 `y²=x³+x+1` が良還元で、無限遠を含めて9点を持つこと。

主要14宣言の公理依存を確認する。7終点の再帰依存、7終点の公開入力、
最終公開型に実際の点数が現れることを監査する。
再帰監査は旧 `TorsionTowerFrobenius` と旧 `*_inertia_frobenius_impossible` 終点を拒否し、
実際の Frobenius・還元単射・素体への降下・全捩れ濃度への到達を要求する。

検証記録: `evidence/validation-note032-frobenius-fixed-count.txt`。
