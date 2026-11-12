# NOTE-032 教科書: 冪商から捩れへの固有成分消滅移送

更新日: 2026-11-03

前章で同じ非零 `ω²` 単元類への条件付き還元を閉じた。
本章は、レビューで残された類群の二つの型の橋を証明する。

\[
 \boxed{(A/pA)^{(\chi)}=0\quad\Longrightarrow\quad A[p]^{(\chi)}=0}.
\]

有限アーベル群 `A` に有限群 `Γ` が作用し、指標 `χ : Γ → (ZMod p)ˣ` を考える。
群の位数が `ZMod p` で可逆であることを明示する。
その後、同じ実際の円分類群と Galois 作用へ適用し、商側の消滅を条件に同じ `classImage` を零化する。

商側の算術的消滅そのものは未実装である。一般 `hno` は未完成である。

## 1. 自然写像の単射性は使えない

\(A=\mathbb Z/9\mathbb Z,p=3\) とすると、元 `3` は非零3捩れだが `3A` に属する。
その自然な商への像は零となる。

\[
 3\ne0,\qquad3\cdot3=0,\qquad[3]=0\text{ in }A/3A.
\]

したがって、捩れ元の像が零であることから元の零化を結論する証明は使わない。
本章の `multiples p A` は実際の `nsmulAddMonoidHom p` の像であり、
`ModQuotient p A` はその実際の商である。

## 2. 有限自己準同型の核補題

`f : A →+ A` を考え、同じ商上の核の条件を

\[
 f(a)\in pA\Longrightarrow a\in pA
\]

と書く。この条件から、有限群では

\[
 \boxed{px=0,\ f(x)=0\Longrightarrow x=0}
\]

を得られる。

```lean
theorem torsion_kernel_eq_zero [Finite A] (p : ℕ) (f : A →+ A)
    (hmod : ∀ x : A, f x ∈ multiples p A → x ∈ multiples p A)
    (x : A) (hpx : p • x = 0) (hfx : f x = 0) : x = 0
```

この段階では `p` の素数性も正値性も必要ない。
有限性の用途は次の二つであり、証明の入力から消していない。

1. 整数線形な自己準同型 `F=f.toIntLinearMap` の Fitting 分解を取る。
   十分大きい正の `n` に対して
   \(A=K\oplus L\), \(K=\ker F^n\), \(L=\operatorname{range}F^n\) となる。
2. 有限な `K` 上で、`p` 倍写像の全射性から単射性を得る。

`hmod` を繰り返すと、`F^n(a)=0` なら `a∈pA` である。
`a∈K` の `p` 乗根を加法的に `a=py` と書き、`y=u+v` を Fitting 分解する。
`a,pu∈K` より `pv∈K`、一方 `pv∈L` でもあるため `pv=0` である。
したがって `a=pu`、しかも `u∈K` となり、`p:K→K` は全射になる。

`f(x)=0` である元は正の `n` に対して `x∈K` である。
`p:K→K` の単射性と `px=0` を合わせて `x=0` を得る。
自然な `A[p]→A/pA` を単射としたのではない。

Lean では有限群を整数加群と読み、Mathlib の
`LinearMap.eventually_isCompl_ker_pow_range_pow` を使う。
有限性から Artinian・Noetherian 条件を供給し、最後は `Finite.injective_iff_surjective` を使う。

## 3. 商上の重み付き和

`ρ : Γ →* (A ≃ₗ[ℤ] A)` は同じ実際の群作用である。
`quotientAction` は同じ自己同型と逆自己同型から商上の作用を構成し、恒等・合成を証明する。
商は実際に `ZMod p` 加群である。

群の位数 `m=|Γ|` でまだ割らず、標数 `p` の加群上で

\[
 B(v)=\sum_{g\in\Gamma}\chi(g)^{-1}\rho(g)v
\]

と定義する。有限和の添字を `g↦hg` で置換すると

\[
 \boxed{\rho(h)B(v)=\chi(h)B(v)}
\]

となる。`weightedSum_eigen` がこの式を証明する。
`Γ` 自体の可換性は要求せず、指標が一次元の単元値準同型であることを用いる。

商上の `χ` 固有成分が零なら、どの `v` に対しても `B(v)=0` である。

## 4. 整数持ち上げと欠損自己準同型

元の `A` は一般には `ZMod p` 加群ではない。
`χ(g)^{-1}` の標準自然数代表元を整数係数として使い、元の同じ群上の準同型

\[
 S(a)=\sum_{g\in\Gamma}(\chi(g)^{-1}).\mathrm{val}\,\rho(g)a
\]

を `liftedWeightedSum` と定義する。
自然な商写像 `q:A→A/pA` に対して

\[
 qS(a)=B(q(a))
\]

を証明する。従って商の固有成分消滅があれば `qS(a)=0` である。
ただし **`S(a)=0` を元の群で結論してはいけない**。
回帰例では `A=Z/9Z` の `S(1)=3≠0` を確認する。

一方、元の `p` 捩れ固有ベクトル `x` については `A[p]` の `ZMod p` 加群構造を使い、

\[
 S(x)=mx
\]

を証明できる。

そこで元の同じ有限群上の自己準同型を

\[
 \boxed{T=m\operatorname{id}-S}
\]

と置く。商上では `qT(a)=m q(a)` である。
`m` が `ZMod p` で可逆なら、`T(a)∈pA` から `a∈pA` が従う。
また元の捩れ固有ベクトルは `T(x)=0` を満たす。
第2節の核補題をこの実際の `T` に適用し、`x=0` を得る。

これが `torsion_eigen_eq_zero` の証明である。
`[Finite A]`、`[Fintype Γ]`、`[NeZero p]`、`IsUnit (|Γ| : ZMod p)` を明示する。
素数 `p` と `p∤|Γ|` の場合を含むが、汎用定理自体は素数性を要求しない。

## 5. 実際の類群と同じ Galois 作用への適用

`ClassModP F p` は

```lean
ModQuotient p (Additive (ClassGroup (NumberField.RingOfIntegers F)))
```

である。類群を `p` 倍で割った加法商であり、`ClassTorsion` と同一視していない。
前章の同じ `classGroupAction` を `additiveAction` で整数線形に読む。
`classModPAction` はその実際の商への移送である。

数体の類群の有限性は Mathlib の `NumberField.RingOfIntegers.instFintypeClassGroup` から供給する。
`classTorsion_eq_one_of_quotient_eigen_vanishing` は、同じ類群の商の固有成分消滅と
同じ捩れ元の固有条件から、その元が1であることを返す。

円分体 `F=rootField ζ` では、既存の同じ原始根から円分拡大性と Galois 性を供給し、

\[
 |\operatorname{Gal}(F/\mathbb Q)|=[F:\mathbb Q]=p-1
\]

を証明する。`root_galois_card_isUnit` は、これから標数 `p` での可逆性を内部供給する。
群の位数や類群の有限性を新たな provider にしない。

`classImage_eq_one_of_quotient_weight_square_vanishing` は、元の同じ `classImage` の
既存の `ω²` 条件に上記の橋を適用し、商側の `ω²` 消滅を条件として `classImage=1` を得る。

## 6. Frey への接続と残る条件

`residual_kummer_classImage_eq_one_of_quotient_vanishing` は
同じ `S,L,K,m,v,P` を保ち、元の指標の開核・共役則を内部供給する。
`hsurj`、元の `hval`、実際の商の消滅 `hvanish` は明示入力である。
同じ類群像の `hzero` は本章の橋から内部で導く。

`residual_kummer_unit_weight_square_of_quotient_vanishing` は、その同じ `hzero` を前章へ渡し、
元の同じ定数の単元倍冪表示、元のベクトルとの一致、その同じ非自明な単元類の
すべての Galois 自己同型に対する `ω²` 条件を返す。

商側の消滅を仮定した条件付き接続であり、算術的な類群消滅を証明した定理ではない。
上流の別の作用や別の商表示との比較定理も、この実装には含めていない。
上流定理を将来使う場合には、実際の作用・商写像・指標の一致を別途確認する必要がある。

元の Frey ベクトルの Selmer 所属、`p` 上の局所 `p` 乗、共鳴住所の吸収、
商側の類群消滅と局所条件付き単元消滅、巡回塔の反復は残る。
本章の結果から一般 `hno` や無条件の矛盾を結論しない。

## 7. 回帰例・依存監査

回帰例は、`Z/9Z` の自然写像の非単射性、実際の有限自己準同型の核補題、
非自明な指標に対する商の固有成分消滅と捩れへの移送、整数持ち上げの `S(1)=3` を確認する。
同じ実際の3円分体の Galois 群の位数・可逆性、類群商の有限性、同じ類群作用との両立も確認する。
有限計算は `decide +kernel` で検証し、native oracle は使わない。

選択した11宣言の公理を表示する。
`Note032CyclotomicClassVanishingDependencyAudit` は11入口の型・コンストラクタ・opaque 証明本体、
7入口の公開入力、2入口の有限性・係数条件を監査する。
Fitting 分解、有限な全射から単射、重み付き和の二つの実際の比較、類群の有限性と
元の同じ `ω²` 条件を要求する。
検証記録は `evidence/validation-note032-finite-eigen-torsion-bridge.txt` に置く。
