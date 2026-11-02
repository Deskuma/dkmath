# NOTE-032 教科書: 同じ Kummer ベクトルの整数化と Selmer 付値

日付: 2026-11-02。
前章: [同じ類の円分二乗作用](TEXTBOOK-N032-CYCLOTOMIC-KUMMER-WEIGHT-261102.md)。
実装: `CyclicKummerIntegral`、`KummerSelmer`、`CyclotomicKummerArithmetic`、
`FreyCyclotomicKummerArithmetic`。

今回は、非分裂から得た同じ非零 Kummer ベクトルを保ちながら、根と定数を整数環の実際の元へ移した。
さらに全有限素点の付値条件を同じ商の部分加群として定義し、Mathlib の Selmer 群との一致、
主分数イデアルの指数による判定、条件が満たされた場合の `p` 乗根と実際の類群 `p` 捩れへの接続を証明した。

**元の Frey ベクトルがこの部分加群に属するという局所算術は、まだ証明していない。**
類群・単数の消滅と一般 `hno` も未完成である。

## 1. 同じ表示と同じベクトルを出発点にする

同じ Frey Source、Cofixed 直線、巡回段 `K` とその全不変量を保つ。
非分裂から構成した同じ全射指標 `ψ_v`、その核の固定体 `M` と
`F=ℚ(ζ_p)` 上の表示 `P` は

\[
\alpha^p=b,\quad M=F(\alpha),\quad X^p-b\text{ 既約},\quad
w=[b]\ne0,\quad \gamma(w)=\omega(\gamma)^2w
\]

を満たす。今回の整数化では新しい体・指標・Kummer 類を選び直さない。
元の巡回段やその濃度・底の包含も変更しない。

## 2. 分母は `p` 乗で払う

非零の `c∈F` に対し

\[
\alpha'=\iota(c)\alpha,\qquad b'=c^p b
\]

とおけば、`α'^p=ι(b')` である。`rescale` は、この同じ `M/F` 上の表示を構成する。

生成性は `c≠0` より `F(cα)=F(α)`。
もし `z^p=c^p b` なら `(z/c)^p=b` となり、元の既約性に反する。
素数次数についての Mathlib の既約判定で、`X^p-b'` の既約性を戻す。
従って根の冪の等式・生成性・既約性を持つ `Presentation` のままで整数化できる。

`c b` のように一度だけ掛ける操作では、元の Kummer 類を保てない。
例えば `b=1/2,p=5` なら、`2b=1` は類を変えるが、

\[
2^5b=16
\]

は同じ類を表す。

## 3. 非零整数の分母を実際に構成する

数体の元 `b` は `ℚ` 上整である。Mathlib の

```lean
IsIntegral.exists_multiple_integral_of_isLocalization
```

を `ℤ⊆ℚ` に適用し、非零整数 `d` と `d b` の `ℤ` 上の整性を得る。
`p≥1` なので

\[
d^p b=d^{p-1}(d b)
\]

も整である。これが `exists_integral_power_multiple`。
新しい根 `α'=ι(d)α` は、その `p` 乗が整であることから、`IsIntegral.of_pow` により整となる。

`IntegralModel P` は次の実際のデータをまとめる。

- 非零整数 `denominator` と、`F` 内でも零でないこと。
- `constant : 𝓞 F` と `radical : 𝓞 M`。
- それぞれが、元の `P` をその整数でスカラー倍した表示の元に等しいこと。

`D.presentation` はこのスカラー倍した表示であり、
`D.radical_pow` は同じ包含について

\[
(D.\mathrm{radical})^p=\iota(D.\mathrm{constant})
\]

を証明する。両方の整数環の元の非零性も証明する。
整数環の元であることから単元であるとは結論しない。

## 4. 元の Kummer 類・非零ベクトル・二乗作用を保つ

底体の実際の乗法群で `b'=c^p b` を書き、商 `Fˣ/(Fˣ)^p` に移す。
`c^p` の類は1なので

\[
[b']=[b],\qquad w'=w
\]

となる。`rescale_constantClass` と `rescale_constantVector` がこの正確な等式を証明する。
従って元の非零性と全自己同型についての `ω²` 固有条件を、そのまま同じベクトルへ輸送できる。

Frey の公開終点

```lean
residual_nonsplit_has_integral_weight_two_kummer_model
```

は元の非分裂から、同じ `v` の全射指標、同じ `M/F` の表示 `P`、整数モデル `D` を構成する。
実際の整数環の非零元、元のベクトルとの等式、非零性、二乗固有性、全素点の付値剰余の一致を返す。
整数代表・分母・類・固有性・付値条件への所属の provider は入力しない。
既存の同じ付値環での局所固定性は `D.presentation` にも適用できる。

## 5. 付値条件は既存の Selmer 群で読む

`R` を Dedekind 整域、`F` をその分数体とする。
Mathlib には実際の `IsDedekindDomain.selmerGroup` がある。
`S=∅` では、全ての高さ1素点で付値が `p` の倍数となる Kummer 類の部分群である。

同じ `KummerClass F p` 上で、Mathlib の
`HeightOneSpectrum.valuationOfNeZeroMod` を加法的な `F_p` 線形写像に読む。
その共通核を

\[
\mathcal K_{\mathrm{val}}=\bigcap_v\ker(\nu_v\bmod p)
\]

とする。`valuationSpace` がこの部分加群であり、`mem_valuationSpace_iff_selmer` が
Mathlib の `S=∅` Selmer 群と同じ商で一致することを証明する。

この部分加群は付値条件を記述するものであり、それだけで `p` 上の不分岐や局所 `p` 乗を主張しない。
レビューで提案された局所算術への接続を進めるための、正確な受け口である。

## 6. 同じ主分数イデアルの指数で所属を判定する

`x∈Fˣ` と高さ1素点 `v` に対し、

\[
\operatorname{ord}_v(x)
=\operatorname{count}_v((x))
=-\bigl(\text{Mathlib の乗法的付値の加法表示}\bigr)
\]

を証明する。`count_span_eq_neg_valuation` は既存の
`DedekindFractionalValuation.count_spanSingleton` を同じ `x` に適用する。
符号を暗黙に読み替えていない。

`valuationLinear_eq_zero_iff` と `mem_valuationSpace_mk_iff` より

\[
\boxed{[x]\in\mathcal K_{\mathrm{val}}
\iff \forall v,\quad p\mid\operatorname{count}_v((x))}.
\]

`constantVector_mem_valuationSpace_iff` は、これを元の同じ `P.constant` に接続する。
さらに `count_span_mul_pow` は

\[
\operatorname{count}_v((c^p x))
=p\operatorname{count}_v((c))+\operatorname{count}_v((x))
\]

を証明する。整数化しても各素点の剰余は変わらず、部分加群への所属は元のままである。
分母払いによって不足している付値条件を作り出すことはできない。

## 7. 付値条件から実際の分数イデアルの冪根へ

同じ非零分数イデアル `I` の全指数が `p` の倍数だと仮定する。
各素点で

\[
e_v=\operatorname{count}_v(I)/p,\qquad J=\prod_v v^{e_v}
\]

と定義する。分数イデアルの指数は有限個を除いて0なので、この有限積は実際の分数イデアルを与える。
各素イデアルの冪は非零であり `J≠0`。
`count_finprod` と指数の可除性から全素点で `count_v(J^p)=count_v(I)` を得る。
既存の `ext_count` によって

\[
\boxed{J^p=I}
\]

となる。`exists_fractionalIdeal_pow` がこの構成を証明する。
`p>0` では、全指数を `p` で消去することで非零冪根の一意性も証明する。

従って所属 `[x]∈𝒦_val` が証明された場合、`exists_principal_fractionalIdeal_pow` が
**同じ** `x` の主分数イデアルについて `J^p=(x)` を返す。

## 8. 実際の類群捩れへの条件付き接続

構成した `J` を非零分数イデアルの単元として `ClassGroup.mk` へ渡す。
`J^p=(x)` は主分数イデアルなので

\[
[J]^p=[J^p]=[(x)]=1\quad\text{in }\operatorname{Cl}(R).
\]

`exists_classGroup_torsion` は、付値部分加群への所属を明示入力に残し、
同じ `J` とこの実際の類群の捩れ条件を返す。
ここでの `ClassGroup R` は、体の冪商である `KummerClass F p` と区別する。
この類群の類が非自明とは主張しない。元の Kummer 類が非零でも、単数由来なら類群の像は自明になり得る。

今回は、商上での写像の代表元独立性、準同型性、Galois 同変性、完全列の完全性まで証明したとは主張しない。
レビューの完全列は引き続き次段の設計目標である。
また `unit_mem_valuationSpace` は整数環の実際の単元がこの部分加群に入ることを、
Mathlib の `selmerGroup.fromUnit` を使って証明する。単数成分の消滅は別の義務である。

## 9. 回帰例と残る証明義務

実際の `ℚ(i)` を `AdjoinRoot (X²+1)` で構成し、根 `i/2`、定数 `-1/4` から
両方の整数環の非零元と同じ二乗方程式を内部構成する回帰例を追加した。

もう一つの重要な回帰例は `R=ℤ,F=ℚ,p=5,x=2`。
`2` は整だが、素点 `(2)` での主分数イデアルの指数は1であり、5で割り切れない。
従ってその Kummer 類は付値部分加群に属さない。
これは「整数化だけで Selmer 所属を得る」という誤った接続を防ぐ。
逆数 `1/2` の類も非自明である。一方、実際の5乗と整数環の単元 `-1` は所属する。

監査は整数分母払い、同じ類への復帰、Mathlib の Selmer 定義、指数と付値の符号、
有限支持による冪根、実際の類群の捩れ、および元の Frey 非分裂への到達を要求する。
結果は [検証記録](evidence/validation-note032-cyclotomic-kummer-arithmetic.txt) に記す。

残る核心は、元の同じ Frey ベクトルに対して、局所固定性から全素点の付値条件を実際に供給すること。
共鳴住所の吸収、`p` 上の局所 `p` 乗条件、整数環の不分岐・完全分解述語との接続が残る。
類群・単数の該当成分への同変な写像と消滅、巡回塔の反復を閉じる必要もある。
最終固定点計数の `hCH` 除去は保たれている。**一般 `hno` は未完成である。**
