# NOTE-032 教科書: `q mod p ≠ ±1` の悪い素点での慣性吸収

日付: 2026-11-01。
前章: [p上の局所分裂](TEXTBOOK-N032-AT-P-LOCAL-SPLITTING-261101.md)。
実装: `DkMath/FLT/FreyNonresonantInertia.lean`。

今回証明したのは、元の Cofixed 直線を含む大域安定な巡回段が与えられたとき、
`q≠p`、`q=2` または `q∣abc`、かつ `q mod p ≠ ±1` を満たす住所での
高次捩れ・逆像上の慣性吸収である。`p≥5` なら `2` と `3` はこの条件を満たす。
一般 `hno` の完成ではない。

## 1. 同じ点群・同じ段・同じ住所を固定する

`S : Frey.Source p`、`p≥5` とする。元の残余表現に Cofixed 直線 `L` があり、
その実際の点群での像を `B` と書く。大域安定な巡回部分群

\[
B\subseteq K\subseteq E(\overline{\mathbb Q}),\qquad |K|=p^m,\quad m\ge1
\]

を固定する。今回 `K` の存在は入力である。別の曲線や同種写像先に置き換えない。

素数 `q≠p` と、その上の指定された付値環 `A` を固定する。
`H_A` は `S.valuationModel A` で滑らかに還元する、同じ点群の実際の部分群である。
新しい `valuationSmoothSubgroup` の所属条件は

```lean
P ∈ S.valuationSmoothSubgroup A ↔ HasSmoothReduction (S.valuationModel A) P
```

そのものである。`p` 上の前章の還元核と、今回の `H_A` を同一視しない。

## 2. 実際の Frobenius の円分指標

`CyclotomicFrobenius` は、同じ `A` の実際の算術 Frobenius `σ` に対して

\[
\chi_p(\sigma)=q\pmod p
\]

を証明する。まず、付値で単元となる次数 `n` の二つの冪根について、
剰余合同なら元の体でも等しいことを示す。比 `z/w` が非自明な冪根なら、
既存の `valuation_sub_one_eq_one` によって `v(z/w-1)=1`。
一方、剰余合同と `v(w)=1` は `v(z/w-1)<1` を与えるので矛盾する。

剰余上での Frobenius の `q` 乗公式を、この剛性で元の冪根へ持ち上げる。
原始 `p` 乗根の位数が `p` であることから、指数を `ZMod p` で比較できる。
Frobenius と名付けた任意の作用に公式を仮定する構成ではない。

Cofixed 直線の底では既存の行列式公式から作用が `χ_p` に等しい。
従って `q mod p ≠ ±1` なら、同じ底の非零点 `x` について

\[
\sigma x\ne x,\qquad \sigma x\ne-x
\]

が得られる。これが巡回群の議論の二つの必須入力である。

## 3. 臨界中心が分解群に固定されることを全素点で証明する

`EllipticNodalDecomposition.centre_decomposition_fixed` は、同じ有理曲線の臨界中心
`C` を分解群が固定することを示す。ここで `q=2,3` も除外しない。

`n=b₂+12C.x`、中心での方程式のずれを `F` とすると

\[
n^2=c_4,\quad v(n)=1,\quad v(F)<1,\qquad
864F=c_6+c_4n.
\]

分解群は有理係数を固定するので `σn=±n`。反対の符号なら、上の恒等式を引いて

\[
432(F-\sigma F)=c_4n
\]

を得る。左辺の付値は `v(432)≤1` と分解群の付値保存から `1` 未満、
右辺の付値は `1` であり矛盾する。`432` を付値の単元として約分していないため、
2・3上でも有効である。体内の恒等式から `C.x`、さらに微分条件から `C.y` の固定を得る。

## 4. 高次捩れの二枝比較と巡回群の符号分離

`p^m` は奇数で、`q≠p` より `A` で単元である。滑らかでない `p^m` 捩れ点 `y` に、
既存の `odd_torsion_depth_of_model` を適用できる。中心の固定と付値保存により
`y` と `σy` は同じ深さにある。同じ枝・反対の枝の既存の比較定理から

\[
\sigma y-y\in H_A\quad\text{または}\quad\sigma y+y\in H_A
\]

を実際に導く。二択を外部 provider として残していない。

`CyclicSignSeparation.le_of_sub_or_add_mem` はこの二択を一般の巡回 `p` 冪群で処理する。
生成元 `g` が `H_A` に入れば全群が入る。入らなければ、二択で差か和のどちらかが入る。
差の場合は作用 `σ`、和の場合は作用 `-σ` を用いる。
生成元での差の所属は加法性により全群へ延びる。
底の作用がそれぞれ恒等でないため、前章の `le_of_nontrivial_socle` が使え、

\[
K\subseteq H_A
\]

が得られる。巡回性と二つの符号からの分離を保持することが重要である。

## 5. 包含から、同じ次数の滑らかな捩れ全体との一致へ

全ての `K` の点は `p^m` 倍で消えるため

\[
K\subseteq E[p^m]\cap H_A.
\]

実際の節点還元上の滑らかな捩れの個数評価
`EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion` は右辺の濃度を `p^m` 以下に抑える。
左辺は仮定によりちょうど `p^m` 個で、両辺は有限である。従って

\[
\boxed{K=E[p^m]\cap H_A}.
\]

これが `cyclic_tower_eq_smooth_torsion_of_nonresonant`。
局所濃度の等式や包含を追加仮定に移していない。

## 6. 高次捩れと逆像上の二種類の吸収

同じ中心の固定と既存の節点慣性定理により、任意の点 `y` と慣性元 `τ` について
`δ=τy-y` は滑らかに還元する。

`y∈E[p^m]` なら `δ` も `p^m` 倍で消えるので、上の一致から直ちに `δ∈K`。
これは `prime_power_pointAction_sub_mem_of_nonresonant_bad` である。

塔を一段持ち上げる逆像の場合は `py∈K` だけを仮定する。このとき `y∈E[p^(m+1)]`。
そのままでは差の指数が一段大きい。しかし `z=p^m y` は `K` の滑らかな `p` 捩れ点で、
`q≠p` の慣性に固定される。従って

\[
p^m\delta=\tau(p^m y)-p^m y=0.
\]

差は同じ `E[p^m]∩H_A=K` に戻る。
`preimage_pointAction_sub_mem_of_nonresonant_bad` は、この指数を一段下げる箇所まで実装する。

## 7. 公開終点で残る局所入力

`small_prime_sign_separated` は `p≥5` のもとで `2,3 mod p ≠ ±1` を証明する。
良還元の住所は既存の慣性固定性が供給する。従って、新しい

```lean
residual_preimage_unramified_away_of_resonant_inertia
residual_cofixed_tower_resonant_inertia_frobenius_impossible
```

で `hbad` に残る住所は、次の全条件を満たすものだけである。

\[
q\text{ は素数},\quad q\ne p,\quad q\ge5,\quad q\mid abc,\quad q\equiv\pm1\pmod p.
\]

第一の終点は、同じ実際の商 `(p⁻¹K)/K` の全 `p` 外の不分岐性を得る。
第二の終点は、前章で閉じた `p` 上の吸収と合わせて最終矛盾に接続する。
第二の終点に残る `hCH` は、指定された `σ, ell` と同じ指数 `N` に関する
実際の点上の関係式

\[
\sigma^2 y+\ell y=(\ell+1-N)\sigma y\qquad(y\in E[p^N])
\]

である。この関係を満たす Frobenius と `ell,N` の選択・構成は今回供給していない。

## 8. 条件を外せないことと、一般 `hno` の残件

回帰例では、`ZMod 25` 上の2倍作用と `5` 捩れの底を使い、二択から全群への包含を確認する。
一方、`ZMod 5` 上の符号反転では和は常に零でも、全群は零部分群に入らない。
`p=5` では素数 `11,19` がそれぞれ `+1,-1` の剰余類に入り、残る条件は空ではない。
これは一般的な符号分離論法の境界であり、これらの指数に Frey.Source が存在するという主張ではない。

一般 `hno` に向けて、次を引き続き構成する必要がある。

1. 共鳴する悪い住所での必要な吸収、またはそれを得る Mazur/Eisenstein specialization の実際の幾何。
2. 円分体の類群・単数の omega 二乗固有成分からの大域 extension 消滅。
3. 大域安定な補直線を反復して、必要な長さの同じ巡回塔を構成すること。
4. 最終矛盾に使う実際の Frobenius 関係と指数の選択。

局所分裂から大域分裂を推論せず、`hEXT` や一般 `hno` を未証明の定数で補わない。

## 9. 検証の範囲

主要15宣言の公理依存、6終点の型・構成子・opaque 本体を含む再帰的依存、
6終点の明示入力を監査する。実際の Frobenius、中心の恒等式、二枝比較、
滑らかな捩れの上界、良還元と `p` 上の吸収への到達を要求する。

検証記録: `evidence/validation-note032-nonresonant-inertia.txt`。
公開入口は `DkMath.Lib`、`DkMath.FLT`、`DkMathTest` へ接続する。
