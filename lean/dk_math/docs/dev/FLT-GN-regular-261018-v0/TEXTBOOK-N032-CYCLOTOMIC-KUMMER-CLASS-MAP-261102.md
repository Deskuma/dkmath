# NOTE-032 教科書: 同じ Selmer 類の類群写像と単元核

日付: 2026-11-02。
前章: [同じベクトルの整数化と Selmer 付値](TEXTBOOK-N032-CYCLOTOMIC-KUMMER-ARITHMETIC-261102.md)。
実装: `KummerSelmerClassMap`、`KummerSelmerExact`、`CyclotomicKummerClassMap`、
`FreyCyclotomicKummerClassMap`。

今回は、前章の存在定理 `J^p=(b)` を、代表元によらない実際の準同型

\[
\Phi:\operatorname{Selmer}(\varnothing,p)\longrightarrow\operatorname{Cl}(R)[p]
\]

へまとめた。さらに単元冪商の単射性、核と像の一致、右側の全射性を証明し、

\[
\boxed{1\longrightarrow R^\times/(R^\times)^p
\longrightarrow\operatorname{Selmer}(\varnothing,p)
\overset\Phi\longrightarrow\operatorname{Cl}(R)[p]\longrightarrow1}
\]

の三つの完全性条件を閉じた。同じ付値部分加群からの `ZMod p` 線形写像も構成する。
一般の構成は Dedekind 整域 `R` とその分数体 `F`、正の指数 `p` で成立し、素数性は要求しない。
Frey への適用では従来どおり素数 `p` を使う。

**元の Frey ベクトルの Selmer 所属、Galois 同変性、類群・単数成分の消滅は未完成である。**
したがって一般 `hno` は未完成である。

## 1. 同じ代表元のイデアル冪根を使う

同じ Kummer 商を `𝒦=Fˣ/(Fˣ)^p` とし、前章の付値条件を満たす群を `Selmer R F p` とする。
`x∈Fˣ` がその条件を満たせば、前章の定理は同じ主分数イデアルについて

\[
J_x\ne0,\qquad J_x^p=(x)
\]

を構成する。`rootIdeal p x hx` はこの根を非零分数イデアルの単元として読む。
`rootIdeal_pow` は、実際の準同型 `toPrincipalIdeal R F` について

\[
J_x^p=\operatorname{principal}(x)
\]

を証明する。新しいイデアル根の provider を要求しない。

## 2. 非零冪根の一意性が代表元独立性を与える

前章の `fractionalIdeal_pow_injective` を単元群へ移した
`idealUnits_pow_injective` は、`p>0` のとき冪が単射であることを述べる。

代表元を `x=c^p y` と変えたとする。実際の分数イデアル群で

\[
\bigl((c)J_y\bigr)^p=(c)^pJ_y^p=(c^p y)=(x)=J_x^p.
\]

よって冪根の一意性から

\[
\boxed{J_x=(c)J_y}.
\]

`rootIdeal_change_representative` がこの等式を証明する。
主分数イデアルの類は1なので `[J_x]=[J_y]`。
Kummer 商で `[x]=[y]` なら、商の等式の判定から実際の `c∈Fˣ` を取り出せる。
`rootClass_independent` は、この代表元独立性を証明する。

## 3. 選択した根の類を実際の準同型にする

`classMapValue` は、Selmer 群の元から実際の代表元 `x` を選び、根 `J_x` を構成し、
`ClassGroup.mk F J_x` を取る。
`classMapValue_eq` は任意の同じ代表元で計算できることを保証する。
選択関数への依存を未証明のまま残さない。

積についても

\[
(J_xJ_y)^p=(xy)=J_{xy}^p
\]

から `J_{xy}=J_xJ_y`。単位元の根は1。
従って `toClassGroup` は実際の `MonoidHom` となる。
`J_x^p=(x)` からその像は `p` 捩れなので、

```lean
KummerSelmerClassMap.toClassTorsion p hp
```

は実際の部分群 `(powMonoidHom p : ClassGroup R →* ClassGroup R).ker` に値を取る。
ここでの `ClassGroup R` は理想類群であり、体の乗法群の冪商 `KummerClass F p` と区別する。

## 4. 元の付値部分加群からの線形写像

同じ付値部分加群の元 `w` を `ofValuationSpace` で同じ Selmer 群の元に読む。
類群の `p` 捩れ部分群も、積を加法へ読み替えて `ZMod p` 加群にする。
`toClassTorsionAdd` と `toClassTorsionLinear` は

\[
\mathcal K_{\mathrm{val}}\longrightarrow
\operatorname{Additive}(\operatorname{Cl}(R)[p])
\]

を加法準同型・`ZMod p` 線形写像として構成する。
これで元の `constantVector` を別の抽象的なベクトルへ置き換えずに類群へ送れる。
線形性だけでは Galois 同変性とはならない。円分固有成分への接続には、その別の証明が必要である。

## 5. 類群像が零なら同じ類は実際の単元から来る

`Φ([x])=1` とする。同じ根 `J_x` の類が1なので

\[
J_x=(c),\qquad c\in F^\times.
\]

`principal_of_class_eq_one` は、実際の同じ分数体の生成元 `c` を取り出す。
`J_x^p=(x)` より `(c^p)=(x)`。
主分数イデアルの等式の判定を使うと、実際の整数環単元 `ε∈Rˣ` が存在して

\[
\boxed{x=\iota(\varepsilon)c^p}.
\]

`unit_decomposition` は、この同じ代表元について単元と冪根を返す。
分解後も `c` は分数体の単元であり、証明なしに整数環の元へ強めてはいない。

逆に `ε∈Rˣ` は主分数イデアル1を生成するため、その Kummer 類の類群像は1。
`toClassGroup_eq_one_iff_unit` は、同じ Selmer 群の元について

\[
\Phi(z)=1\iff\exists\varepsilon\in R^\times,
\quad\operatorname{fromUnit}(\varepsilon)=z
\]

を証明する。核に属することを、別の同型な群の元の存在へ置き換えない。

## 6. 単元冪商の単射性と核・像の一致

`unitInclusion` は、Mathlib の実際の単元写像 `selmerGroup.fromUnit` を単元冪商へ降ろす。
Mathlib の `fromUnit_ker` が、正の指数と Dedekind 整域の整閉性を使って
その核が単元の `p` 乗部分群に一致することを証明している。
これを使い、`unitInclusion_injective` で左側の単射性を得る。

前節の零像の判定と商の代表元を使えば

\[
\boxed{\ker\Phi=\operatorname{range}(\mathrm{unitInclusion})}.
\]

`kernel_eq_unit_range` が、実際の同じ二つの準同型についてこの等式を証明する。

## 7. 類群捩れへの全射性

任意の `a∈Cl(R)[p]` を、同じ分数体の非零分数イデアル `J` で表す。
`a^p=1` より `[J^p]=1`。従って実際の `x∈Fˣ` が存在して `J^p=(x)` となる。

この等式から各素点の指数は `p` の倍数となるため、`[x]` は Selmer 群に入る。
同じ `x` から構成した根と `J` は、冪根の一意性により等しい。
よって `Φ([x])=[J]=a` である。
`toClassTorsion_surjective` がこの全射性を証明する。

```lean
KummerSelmerExact.short_exact p hp
```

は、左の単射性・核と像の一致・右の全射性をまとめて返す。
今回の完全性は、これら三つの条件を実際の群準同型に対して証明したものである。
完全列や代表元独立性を新しい仮定として追加してはいない。

## 8. 同じ円分 Kummer 類の像を固定する

`CyclotomicKummerClassMap.selmerElement` は、元の `P` の同じベクトルに Selmer 所属の証明を添える。
`classImage` はその実際の円分類群捩れへの像である。
`classImage_via_root` により、同じ `P.constant` の任意の同じ冪根でこの像を計算できる。
`rescale_classImage` は、前章の整数化の前後でこの像が変わらないことも証明する。

この像が1なら `unit_of_classImage_eq_one` は

\[
b=\iota(\varepsilon)c^p,\qquad
w=[\iota(\varepsilon)],\qquad
[\varepsilon]\ne1\text{ in }R^\times/(R^\times)^p
\]

を返す。元の同じ非零 Kummer ベクトルが、同じ単元の類として残る。
非自明性は、単元が `R` で `p` 乗ならその体の像も `p` 乗となり、
元の `constantClass_ne_one` に反することから従う。
これは単元成分を消滅させる定理ではない。

## 9. Frey の条件付き受け口

```lean
residual_kummer_unit_of_classImage_eq_one
```

は、元の Source・Cofixed 直線・同じ巡回段の不変量・同じ `v`・同じ表示 `P` を保持する。
Selmer 所属 `hval` と、この実際の類群像の零化 `hzero` を**別々の明示入力**として受け、
同じ定数の単元倍冪分解、元のベクトルとの一致、単元冪商の非自明性を返す。

前章までの非分裂から表示・整数モデルを構成する定理には、これらの入力を追加していない。
今回の受け口は算術的な仮定が証明された後の構造的還元であり、`hno` の閉包ではない。

## 10. 回帰例と次の工程

`R=ℤ,F=ℚ,p=2` の実際の単元 `-1` を使い、
単元冪商の類と Selmer 群の類が非自明である一方、類群像は零となることを確認する。
従って類群像が零でも、元の Selmer 類を零と結論できない。
同じ類の代表元 `-4` を単元倍平方へ戻す回帰例も追加した。

指数1では Selmer 群全体が自明になる境界を確認する。
指数0では非零分数イデアル `(2)` と1が異なるのに同じ0乗を持つため、
冪根の一意性と写像の構成に正の指数の仮定が必要であることも検証する。
有限計算で既存の完成済み FLT 終点へ置き換える検証は行わない。

再帰監査は実際のイデアル根・代表元独立性・積・単元核・類群代表元からの全射性・線形化と、
元の同じ Frey 表示への到達を要求する。
条件付きの受け口で `hval` と `hzero` が公開入力に残ることも確認する。
結果は [検証記録](evidence/validation-note032-cyclotomic-kummer-class-map.txt) に記す。

今回、前章に残した商上の写像と群としての完全性を閉じた。
残るのは円分 Galois 作用との同変性、元の Frey ベクトルの Selmer 所属、
類群・単数の該当成分の消滅、`p` 上の局所 `p` 乗条件、共鳴住所の吸収と巡回塔の反復である。
類群の像が `ω²` 成分に入るという結論には、線形性に加えて同変性の証明が必要となる。
最終固定点計数の `hCH` 除去は保たれている。**一般 `hno` は未完成である。**
