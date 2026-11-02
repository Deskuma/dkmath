# NOTE-032 教科書: 同じ Selmer 類の同変性と実際の類群の ω² 条件

更新日: 2026-11-02

本章は前章 `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-CLASS-MAP-261102.md` の写像を進める。
同じ代表元のイデアル根を移し、Selmer 類群写像の同変性を証明した。
元の Frey ベクトルが Selmer 群に属するなら、その**同じ類群像**が実際の
Galois 作用の `ω²` 固有条件を満たす。像が非零であることや、その成分の消滅は結論しない。
一般 `hno` は未完成である。

## 1. 固定する対象と前提

`R` は Dedekind 整域、`F` はその分数体とする。前章の同じ写像を使う。

\[
 \Phi:\operatorname{Selmer}(\varnothing,p)\longrightarrow\operatorname{Cl}(R)[p],
 \qquad [x]\longmapsto[J_x],\qquad J_x^p=(x).
\]

正の指数 `hp : 0 < p` はイデアル根の一意性に必要である。
自己同型のデータは、別々の無関係な作用ではなく、埋め込みを保つ組である。

```lean
structure CompatibleAut (R F : Type*) [CommRing R] [Field F] [Algebra R F] where
  integers : R ≃+* R
  field : F ≃+* F
  commutes : ∀ r : R, field (algebraMap R F r) = algebraMap R F (integers r)
```

Frey への適用では `R = 𝓞 F` であり、この組を追加の provider にしない。
`CyclotomicKummerEquivariance.integerAut γ` が、実際の底体自己同型 `γ` と
Mathlib の `NumberField.RingOfIntegers.mapRingEquiv γ.toRingEquiv` から内部構成する。

## 2. 半線形なイデアルの移送

一般に `γ` は `R` の各元を固定しない。そのため、固定された `R`-線形写像として
分数イデアルを移す方法は適切ではない。`FractionalIdeal.extendedHom'` で
整数側の自己同型に沿って移す実際の環準同型 `idealMap` を作る。

分母の非零性は整数側の自己同型の単射性が保つ。
`IsLocalization.map_unique` と `commutes` により、局所化した写像は同じ `field` に一致する。
`extended_spanSingleton` を適用すると、次の等式を得る。

\[
 T_\gamma((x))=(\gamma x).
\]

Lean の入口は `CompatibleAut.idealMap_span` と `idealUnitsMap_principal` である。
非零イデアルの移送は、環準同型を `Units.map` で単元へ移した実際の写像であり、
移したイデアルの存在を別途仮定していない。

## 3. 同じ Selmer 条件を保つ

元の `x` に対する `hx` から前章の `rootIdeal p x hx` を取る。

\[
 T_\gamma(J_x)^p=T_\gamma(J_x^p)
 =T_\gamma((x))=(\gamma x).
\]

任意の素イデアルで右辺の指数が `p` 可除になるため、同じ `γx` が Selmer 条件を満たす。
`map_mem` は、この所属の保存をイデアル冪の等式から証明する。
すべての素点の置換を先に構成する必要はない。

ただしこれは「所属する元を移しても所属する」という定理である。
元の Frey 定数が所属することは証明していない。

## 4. 選んだ根そのものが一致する

`γx` の条件が得られたので、その選ばれた根 `J_{γx}` と、移した根 `T_γ(J_x)` を比較する。
両者の `p` 乗は同じ主イデアルである。非零分数イデアルの正の冪の単射性から、

\[
 \boxed{J_{\gamma x}=T_\gamma(J_x)}
\]

を得る。これは存在命題や類群での等式だけでなく、実際の単元化分数イデアルの等式である。

```lean
theorem rootIdeal_map {p : ℕ} (hp : 0 < p) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    rootIdeal p (Units.map σ.field.toMonoidHom x) (σ.map_mem x hx) =
      σ.idealUnitsMap (rootIdeal p x hx)
```

証明は `idealUnits_pow_injective hp`、`rootIdeal_pow`、`map_pow`、
`idealUnitsMap_principal` で閉じる。指数0では冪根は一意にならないため、`hp` を消さない。

## 5. 実際の類群とその自己同型

`classGroupMap` は `ClassGroup.equiv F` と商の普遍性を使って構成する。
主イデアルの像が主イデアルであることは第2節で証明済みである。

\[
 \gamma[J]=[T_\gamma(J)].
\]

`classGroupMap_refl` と `classGroupMap_trans` は恒等と合成を証明する。
`classGroupEquiv` は同じ整数側・分数体側の逆自己同型を用いて逆写像を与える。
数体の場合、`classGroupAction` は実際に

```lean
(F ≃ₐ[ℚ] F) →* MulAut (ClassGroup (NumberField.RingOfIntegers F))
```

を返す。自己同型群の積は関数の合成順に注意し、`integerAut_mul` で順序を明示した。

`toClassGroup_equivariant` は任意の元 `z` の同じ代表元 `x` を取り、第4節の等式を
類群へ送って証明する。`toClassTorsion_equivariant` は `p` 捩れ部分群への制限である。

\[
 \boxed{\Phi(\gamma z)=\gamma\Phi(z)}.
\]

`classTorsionLinearMap` でこの実際の作用を `ZMod p` 線形写像にする。
その恒等・合成法則も証明した。短完全列全体の単元側の作用や固有成分の完全性を
本章で新たに証明したわけではない。

## 6. 元の二乗則を同じ類群像へ移す

既に同じ Kummer 定数類について

\[
 \gamma[b]=[b]^{(\omega(\gamma)^2).\mathrm{val}}
\]

が証明されている。所属 `hval` を明示して同じ `selmerElement` を作り、
同変性と `Φ` の冪の保存を組み合わせると、

\[
 \gamma\Phi([b])=\Phi([b])^{(\omega(\gamma)^2).\mathrm{val}}
\]

を得る。加法記法では、`classImage_weight_square` が

\[
 T_\gamma(\operatorname{classImage})
   =\omega(\gamma)^2\,\operatorname{classImage}
\]

を返す。線形性だけからの推論ではなく、実際の同変性を経由する。

`Frey.Source.residual_kummer_classImage_weight_square` は同じ `S,L,K,m,v,P` を保つ。
指標の開核と逆指標共役則を既存の同じ Frey 構成から内部供給する。
`hsurj` と元のベクトルの `hval` は明示する。類群像の零化や同変性の provider は要求しない。
`hsurj` は非分裂から得る既存の同じ指標の全射性に対応する。

## 7. 回帰検証と監査

`DkMathTest.FLT.FreyCyclotomicKummerEquivariance` は `F=ℚ(i)` を
`AdjoinRoot (X²+1)` として構成し、実際の `i↦−i` 自己同型を作る。
この自己同型は恒等でないこと、`(2+i)` を `(2−i)` に移すこと、実際の三乗の
Selmer 所属とその選んだイデアル根の移送を確認する。
実際の類群上の作用の恒等・合成も確認する。

`Note032CyclotomicKummerEquivarianceDependencyAudit` は10入口の型・コンストラクタ・
opaque 証明本体を再帰走査する。根の一意性、実際の主イデアル移送、
同変性、元の二乗則、同じ Frey 指標の共役則を要求する。
別途7入口で残る入力を検査する。選択した12宣言の公理も表示する。
検証記録は `evidence/validation-note032-cyclotomic-kummer-equivariance.txt` に置く。

## 8. 次の算術的境界

元の同じ Frey ベクトルの Selmer 所属は残る。局所慣性の固定性から全素点の
付値条件を導く接続、共鳴住所の吸収、`p` 上の局所 `p` 乗条件が必要である。
類群・単数の該当成分の消滅と巡回塔の反復も残る。

類群像の零化は元の Kummer 類の零化ではない。零化時に得る同じ非自明な単元類へ
固有条件を移すには、単元側の作用と写像の両立をさらに証明する必要がある。
二乗指標は複素共役に対して偶であり、奇成分の消滅をそのまま流用しない。
今回の `ω²` 条件から無条件の消滅や一般 `hno` の完成を結論しない。
