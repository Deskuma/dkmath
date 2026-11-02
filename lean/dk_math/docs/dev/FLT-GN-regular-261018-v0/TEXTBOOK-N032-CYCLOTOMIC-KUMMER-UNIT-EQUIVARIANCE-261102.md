# NOTE-032 教科書: 同変な短完全列から同じ非零 ω² 単元類へ

更新日: 2026-11-02

前章は同じ Selmer 類から類群への写像 `Φ` の同変性を証明した。
本章では単元側を閉じ、実際の Galois 作用を備えた群の短完全列を構成する。
元の同じ Frey ベクトルの Selmer 所属と類群像の零化を仮定すると、
同じ定数の単元倍冪表示を保ちながら、その同じ非自明な単元類の `ω²` 固有性を得る。

一般 `hno` は未完成である。元の Selmer 所属や算術的消滅を証明したわけではない。

## 1. 保つ対象と既存の列

`R` は Dedekind 整域、`F` はその分数体、`hp : 0 < p` とする。
前章までに構成した同じ写像を使う。

\[
 1\longrightarrow U_p:=R^\times/(R^\times)^p
 \xrightarrow{\iota}\operatorname{Selmer}(\varnothing,p)
 \xrightarrow{\Phi}\operatorname{Cl}(R)[p]\longrightarrow1.
\]

`unitInclusion` と `toClassTorsion` の定義を変更していない。
`short_exact` は単射性・核と像の一致・全射性を実際の群準同型について証明している。

`CompatibleAut R F` の `integers` と `field` は埋め込みを保つ。
Frey では同じ `S,L,K,m,v,ψ,P` を維持し、別の単元や別の Kummer 類への交換を避ける。

## 2. 整数側の自己同型から単元冪商へ

整数側の自己同型は単元を単元へ、`p` 乗を `p` 乗へ移す。
そのため、実際の商上の準同型を定義できる。

```lean
def unitClassMap (p : ℕ) (σ : CompatibleAut R F) : UnitClass R p →* UnitClass R p :=
  QuotientGroup.map _ _ (Units.map σ.integers.toMonoidHom) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map σ.integers.toMonoidHom u, (map_pow _ _ _).symm⟩)
```

`unitClassMap_refl` と `unitClassMap_trans` は恒等と合成を証明する。
`unitClassEquiv` は整数側の逆自己同型を使って実際の逆写像を作る。
この作用自体は指数0でも定義できる。一方、単元埋め込みと完全性には `hp` を保つ。

前章の `selmerMap` にも恒等・合成を証明し、逆写像を備えた `selmerEquiv` を構成した。
`classTorsionEquiv` は前章の実際の類群自己同型の逆写像を同じ捩れ部分群へ制限する。

## 3. 単元埋め込みとの同変性

証明の核心は、単元の実際の代表元 `u : Rˣ` に戻ることである。

\[
 \gamma(\operatorname{algebraMap}(u))
   =\operatorname{algebraMap}(\gamma u).
\]

これは `CompatibleAut.commutes` そのものである。
単元の等式を `Units.ext` で得て、同じ Kummer 商へ送る。

```lean
theorem unitInclusion_equivariant (p : ℕ) (hp : 0 < p) (σ : CompatibleAut R F)
    (u : UnitClass R p) :
    σ.selmerMap p (unitInclusion p hp u) = unitInclusion p hp (unitClassMap p σ u)
```

同変性を provider として仮定していない。
前章の `Φ` の同変性と合わせ、`short_exact_equivariant` は同じ短完全列の
三つの完全性条件と二つの写像の同変性を返す。

## 4. 数体の実際の Galois 作用

`CyclotomicKummerUnitEquivariance` は、任意の数体 `F` に対して

```lean
unitClassAction : (F ≃ₐ[ℚ] F) →* MulAut (UnitClass (NumberField.RingOfIntegers F) p)
selmerAction : (F ≃ₐ[ℚ] F) →* MulAut (Selmer (NumberField.RingOfIntegers F) F p)
classTorsionAction : (F ≃ₐ[ℚ] F) →* MulAut (ClassTorsion (NumberField.RingOfIntegers F) p)
```

を構成する。いずれも同じ `integerAut γ` を使う。
群の積は関数合成なので、`integerAut_mul` と `trans` の順序を合わせる。
恒等・積の保存は各準同型の実際の証明フィールドである。

`numberField_short_exact_equivariant` は、これら三つの実際の作用について

\[
 \gamma\iota(u)=\iota(\gamma u),\qquad
 \Phi(\gamma z)=\gamma\Phi(z)
\]

と、元の列の単射性・核と像の一致・全射性をまとめる。
固有成分を取った列の完全性を、ここから無条件に結論してはいない。

## 5. 類群像が零なら、同じ単元逆像は一意

`Φ(z)=1` なら、核と像の一致から `ι(u)=z` を満たす `u : UnitClass R p` が存在する。
さらに `ι` の単射性から、この単元冪商の類は一意である。

\[
 \boxed{\exists!u\in U_p,\quad\iota(u)=z}.
\]

`existsUnique_unitClass` を使い、`unitPreimage p hp z hzero` を定義する。

- `unitPreimage_spec`: 同じ Selmer 類を表す。
- `unitPreimage_eq`: 別の実際の単元代表元で同じ Selmer 類を表しても、同じ単元冪商の類になる。
- `unitPreimage_ne_one`: `z≠1` なら、その同じ逆像も非自明。
- `unitPreimage_equivariant`: この一意な逆像も自己同型と可換。

整数環単元の代表元そのものが一意なのではない。`p` 乗を法とした類が一意なのである。

## 6. 元の固有条件を同じ単元類へ戻す

同じ `u,z` に対し、`ι(u)=z` と `γz=z^r` を仮定する。
同変性と準同型性から、

\[
 \iota(\gamma u)=\gamma\iota(u)=\gamma z=z^r=\iota(u^r).
\]

`unitInclusion_injective` を適用すると、

\[
 \boxed{\gamma u=u^r}
\]

を得る。`unitClass_weight` がこの証明であり、単元の固有性を新たな入力にしない。

`unitClassModule` は商の定義による `u^p=1` から、加法記法の同じ群を `ZMod p` 加群にする。
`unitClassLinearMap_weight` は `r=a.val` の等式を

\[
 T_\gamma(u)=a\,u
\]

という同じ単元類の線形な固有条件に読み替える。

## 7. 元の円分 Kummer 定数と実際の単元を保つ

元の表示は `α^p=b` であり、定数類 `[b]` と非零ベクトル `w` を既に固定している。
`hval` と `hzero` を別々に明示して、同じ Selmer 類の一意な逆像を

```lean
unitImage ψ hζ P hval hzero
```

と定義する。`unitImage_ne_one` は、既存の同じ定数類の非自明性から証明する。
`unitImage_weight_square` は既存の `constantClass_weight_square` と第6節により、

\[
 \boxed{T_\gamma(\operatorname{unitImage})
   =\omega(\gamma)^2\operatorname{unitImage},\qquad\operatorname{unitImage}\ne0}
\]

を得る。乗法記法では非零の条件は `unitImage ≠ 1` である。

`unit_of_classImage_eq_one_weight_square` は、前々章で得た同じ実際の `ε∈𝓞_Fˣ,c∈Fˣ` を保ち、

\[
 b=\iota(\varepsilon)c^p,\quad
 w=[\iota(\varepsilon)],\quad
 \operatorname{unitImage}=[\varepsilon]\ne1,
 \quad\forall\gamma,\ T_\gamma[\varepsilon]=\omega(\gamma)^2[\varepsilon]
\]

をまとめて返す。Galois 自己同型ごとに違う単元を選ぶ結論ではなく、**一つの同じ単元**を返す。

Frey の入口 `Source.residual_kummer_unit_weight_square` は同じ表示を維持する。
既存の同じ指標から開核と逆指標共役則を内部供給する。
`hsurj`、元のベクトルの `hval`、同じ類群像の `hzero` は明示入力である。
単元の存在・同変性・固有性や消滅の provider は追加していない。

## 8. 回帰例と公理・依存監査

`FreyCyclotomicKummerUnitEquivariance` の回帰例は次を確認する。

- 実際の `ℚ(i)` と整数環単元 `i` を構成する。実際の共役が `i↦−i` を誘導する。
  指数0の商ではその単元類を本当に動かし、作用を恒等写像で代用できないことを確認する。
  指数0は作用の検証であり、正指数の完全性定理へ適用していない。
- 同じ非恒等共役と、指数2の単元埋め込みの同変性を確認する。
- `ℤˣ` の `−1` は平方を法として非自明であり、実際の Selmer 像の類群像は零である。
  その一意な単元逆像が同じ `−1` の類になることと、その同じ類への固有条件の移送を確認する。
- `Z/9Z` の実際の元 `3` は非零3捩れだが、3倍部分群で割った商では零になる。
  捩れ部分群から冪商への自然な写像を、単射と扱わない。

選択した17宣言の公理を表示する。
`Note032CyclotomicKummerUnitEquivarianceDependencyAudit` は12入口の型・コンストラクタ・
opaque 証明本体を再帰走査し、9入口の公開入力も確認する。
実際の単元埋め込みの同変性と単射性、一意な逆像、元の二乗則を要求する。
検証記録は `evidence/validation-note032-cyclotomic-kummer-unit-equivariance.txt` に置く。

## 9. 残る算術と型の境界

元の同じ Frey ベクトルの Selmer 所属は未解決である。
慣性・分解群の固定性からの付値可除性、`p` 上の局所 `p` 乗、共鳴住所の吸収を供給する必要がある。
類群・単元の該当成分の消滅、巡回塔の反復も残る。
非自明な `ω²` 単元類の存在だけでは矛盾にならず、必要な局所条件もまだ供給していない。

本章の類群側は `Cl(R)[p]` である。上流の `Cl(R)/pCl(R)` の固有成分消滅を
そのまま適用する型の一致はない。有限性などを使った消滅移送の別証明が必要であり、
その移送も算術的な類群消滅も本章では実装していない。

`ω²` は複素共役に対して偶なので、奇成分の消滅だけで閉じない。
今回閉じたのは、所属と類群像の零化を条件とする**同じ非零単元類への同変な還元**である。
一般 `hno` の完成や、元の非零 Kummer 類の無条件の零化とは区別する。
