# NOTE-032 教科書: 有限加法指標から円分体上の巡回 `p` 拡大へ

日付: 2026-11-02。
前章: [Frobenius 固定点の計数](TEXTBOOK-N032-FROBENIUS-FIXED-COUNT-261102.md)。
実装: `CyclotomicKernelField`、`CyclotomicCharacterField`、`FreyCyclotomicCharacterField`。

今回は、大域非分裂から得た指標を、同じ代数閉包内の実際の数体の拡大へ接続した。
原始 `p` 乗根 `ζ` に対して `F=ℚ(ζ)` とおき、指標の核の固定体 `M` を構成する。
非分裂なら一つの指標が全射になり、

\[
[M:\mathbb Q]=p(p-1),\qquad [M:F]=p,\qquad
M/F\text{ は Galois、}\operatorname{Gal}(M/F)\text{ は巡回}
\]

を証明する。分解群・慣性群の局所作用も同じ `M` 上で固定となることを示す。
類群・単数によるこの拡大の排除は未実装であり、一般 `hno` は未完成である。

## 1. 同じ逆像商と同じ指標を保つ

`p≥5`、同じ Frey Source `S` と Cofixed 直線 `L` を固定する。
その実際の底を含む大域安定な巡回段 `K` が `|K|=p^m`、`m≥1` を満たすとする。
同じ商と固定直線を

\[
V=(p^{-1}K)/K,\qquad C=\operatorname{image}(E[p]\to V),\qquad |C|=p
\]

と書く。前章までに、各 `v∈V` について

\[
\psi_v:\Gamma\longrightarrow(C,+),\qquad
\Gamma=\ker\chi_p,\qquad\psi_v(u)=\rho(u)v-v
\]

を実際に構成した。これらは開核を持ち、同じ `v` で

\[
\psi_v(gug^{-1})=\chi_p(g)^{-1}\psi_v(u)
\]

を満たす。大域補直線が存在しないなら、一つの `ψ_v` は `C` 全体へ全射する。
今回の構成体は、この同じ指標の核から定義する。

## 2. 円分指標の核を実際の円分体の fixing subgroup と同定する

同じ `ℚ̄` 内の原始 `p` 乗根 `ζ` を固定し、

```lean
CyclotomicKernelField.rootField ζ
```

を `IntermediateField.adjoin ℚ {ζ}` と定義する。
円分指標の実際の根への作用公式と原始根の位数から

\[
\chi_p(\sigma)=1\iff\sigma\zeta=\zeta
\]

を得る。さらに生成元の固定性を adjoin 全体へ延ばすことで

\[
\boxed{F.\operatorname{fixingSubgroup}=\Gamma}
\]

となる。これが `fixingSubgroup_eq_kernel`。
既存の `IntermediateField.fixingSubgroupEquiv` と合成し、

\[
\Gamma\simeq\operatorname{Gal}(\overline{\mathbb Q}/F)
\]

を実際の群同型として構成する。`kernelEquiv_apply` は、同型の前後で同じ代数的数への
作用が変わらないことを述べる。単に同じ濃度の別の群を選ぶ構成ではない。

`F` は同じ原始根から生成した実際の円分拡大であり、数体構造も供給する。
有限次元の中間体の fixing subgroup は Krull 位相で開くため、`Γ` は開部分群になる。
その固定体が `F` に戻ることも無限 Galois 対応で証明する。

実際の `p` 上の円分慣性の全射性から `χ_p` は `(ZMod p)ˣ` へ全射する。
従って

\[
[\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q):\Gamma]=p-1,
\qquad [F:\mathbb Q]=p-1.
\]

## 3. 同じ付値環の分解群・慣性群も輸送する

`A` を `ℚ̄` の同じ付値環とする。`u∈Γ` に対応する `F` 上の自己同型を `θ(u)` と書く。
どちらも `ℚ̄` の同じ元に同じように作用するので

\[
\theta(u)\in D(A/F)\iff u\in D(A/\mathbb Q),
\qquad
\theta(u)\in I(A/F)\iff u\in I(A/\mathbb Q)
\]

を証明できる。慣性については、付値環の保存と全整元の剰余合同という既存の判定を
両方向に使う。別の付値環や素イデアルを選び直さない。

```lean
kernelEquiv_mem_decomposition_iff
kernelEquiv_mem_inertia_iff
```

はこの実際の所属条件を保存する。

## 4. 同じ指標の核の固定体を構成する

一般の固定直線値の指標 `ψ:Γ→C` について

\[
H=\operatorname{image}(\ker\psi\hookrightarrow\Gamma\hookrightarrow G_{\mathbb Q}),
\qquad
M=\overline{\mathbb Q}^{\,H}
\]

と定義する。`kernelInGalois` と `characterField` がこれらの実際の部分群・中間体である。
`u∈Γ` に対して `u∈H↔ψ(u)=0` と証明し、元の核を保つ。

`ker ψ` は `Γ` 内で開き、`Γ` 自体も全群内で開くので、`H` も開く。
開部分群は閉じてもいるため、無限 Galois 対応から

\[
\boxed{M.\operatorname{fixingSubgroup}=H}
\]

を得る。この等式と `H` の開性から `M/ℚ` の有限性が従う。
`characterField_numberField` は同じ構成体の数体構造も供給する。
また `H≤Γ` より `F≤M`。拡大体の存在・有限性を新しい入力にしていない。

## 5. 共役則から Galois 性、全射性から次数を得る

逆指標の共役則は、`ψ(u)=0` なら `ψ(gug⁻¹)=0` を与える。
従って `H` は `G_ℚ` 全体で正規であり、`M/ℚ` は Galois 拡大となる。

`ψ` が全射なら、第一同型定理と部分群指数の積により

\[
[G_{\mathbb Q}:H]=[\Gamma:\ker\psi]\,[G_{\mathbb Q}:\Gamma]
=|C|(p-1).
\]

これを固定体の実際の次数へ運び、`[M:ℚ]=|C|(p-1)` を得る。

相対拡大構造は、同じ包含 `F≤M` の `IntermediateField.inclusion` から
`extensionAlgebra ψ hζ` として定義する。次数の塔の公式から

\[
(p-1)[M:F]=|C|(p-1)
\]

であり、`p-1>0` を使って `[M:F]=|C|` を得る。
同じ拡大構造で `M/F` も Galois、相対 Galois 群の位数も `|C|`。
`|C|=p` なら位数が素数の群の巡回性から、巡回 `p` 拡大となる。

`relative_finrank`、`relative_isGalois`、`relative_card_aut`、`relative_isCyclic` が
この計算を実装する。全射性だけで次数 `p` とはせず、値域の濃度も保持する。

## 6. 非分裂から実際の巡回 `p` 拡大へ到達する Frey 終点

```lean
residual_nonsplit_has_cyclotomic_cyclic_extension
```

は、元の Source・Cofixed 直線・巡回段と大域非分裂を入力する。
前章の実際の定理で全射指標 `ψ_v` を一つ選び、上の `M` を構成する。
公開された結論は、同じ `v` について次をまとめて返す。

- `ψ_v` の全射性。
- `M/ℚ` の有限性・Galois 性と、同じ円分体の包含 `F≤M`。
- 絶対次数 `p(p-1)`。
- 同じ包含による相対次数 `p`、相対 Galois 性、Galois 群の位数 `p` と巡回性。

`hopen`、共役則、有限性、拡大体、次数を外部 provider として残していない。
原始根 `ζ` の選択は明示するが、その存在は代数閉包の既存の定理から得られる。
一般の大域 extension 消滅を新たに仮定していない。

## 7. 指標の局所消滅を、構成した体の全元の固定性へ移す

`p` 上では、同じ商の実際の局所補直線により `Γ∩D(A/ℚ)` 上で `ψ_v=0` だった。
分解群の輸送と固定体の定義から、`D(A/F)` の全元は構成体 `M` の全元を固定する。

`q≠p` では、同じ慣性群の輸送を使って `I(A/F)` の全元が `M` を固定することを得る。
ここには、共鳴する悪い住所

\[
q\ge5,\quad q\ne p,\quad q\mid abc,\quad q\equiv\pm1\pmod p
\]

での逆像上の吸収 `hbad` が依然明示入力として残る。

```lean
residual_characterField_decomposition_fixed_at_p
residual_characterField_inertia_fixed_away
```

は、指標値だけでなく実際の `M` の任意の元 `x` に対する固定性を結論する。
今回形式化したのは同じ延長付値環における実際の局所群の作用である。
数体の整数環の全素イデアルに対する不分岐述語や、類体論の Artin 写像への接続は、まだ別の工程である。

## 8. 零指標・自明値域を除外し忘れない

零指標では `H=Γ` だから `M=F` となる。`characterField_one_eq_rootField` がこの等式を証明する。
回帰例は `p=5` でこの体の絶対次数が4であり、20ではないことを確認する。

また自明な値域 `PUnit` への零指標は全射だが、相対次数は1である。
次数 `p` の結論に値域の濃度 `p` が必要であることを、この例で確認する。
`p=2` の円分核の指数1も検証し、一般の体 API と Frey 側の `p≥5` を区別する。

## 9. 一般 `hno` に残る算術

今回閉じたのは、有限指標から実際の数体・巡回 `p` 拡大・同じ局所群の作用へ進む接続である。
次を引き続き形式化する必要がある。

1. この付値環上の固定性を、必要な数体の素イデアル・不分岐条件へ接続すること。
2. 構成した拡大と具体的な指標を、類群・単数の該当する固有成分へ送ること。
3. 固定直線値の逆指標から `μ_p` 値への捩り・Kummer 双対化を構成し、omega 二乗成分の消滅を適用すること。
4. 共鳴住所の吸収を閉じ、指標の大域消滅から必要な長さの巡回塔を反復構成すること。

次数が `p` というだけで、この拡大が存在しないとは結論できない。
類群の `p` 部分全体の消滅も仮定しない。指定された固有成分と局所条件を保つ必要がある。
前章で閉じた最終計数矛盾には、引き続き `hCH` は不要である。

検証記録: `evidence/validation-note032-cyclotomic-character-field.txt`。
主要14宣言の公理依存、7終点の再帰依存と7終点の公開入力を監査する。
