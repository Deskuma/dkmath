# NOTE-032 教科書: 同じ指標核の固定体を Kummer 根で表示する

日付: 2026-11-02。
前章: [実際の円分巡回拡大](TEXTBOOK-N032-CYCLOTOMIC-CHARACTER-FIELD-261102.md)。
実装: `CyclicKummer`、`CyclotomicCharacterKummer`、`FreyCyclotomicKummer`。

大域非分裂から構成済みの同じ体 `M/F` に対して、

\[
F=\mathbb Q(\zeta_p),\qquad M=F(\alpha),\qquad
\alpha^p=b\in F,\qquad b\notin F^{\times p}
\]

を Lean で証明した。根と定数はいずれも非零であり、`X^p-b` は既約、`M` 自身がその分解体となる。
さらに相対 Galois 群と `μ_p(F)` の同型、同じ根への作用公式、元の指標核との一致を得る。
これは非自明な Kummer 拡大の構成である。その排除と一般 `hno` は未完成である。

## 1. 出発点と今回の選択

同じ Frey Source、Cofixed 直線、大域安定な巡回段 `K`、
`|K|=p^m`、`m≥1`、底の包含を保つ。前章までの逆像商と指標は

\[
V=(p^{-1}K)/K,\quad C=\operatorname{image}(E[p]\to V),\quad
\Gamma=\ker\chi_p,\quad \psi_v:\Gamma\to(C,+),\quad |C|=p.
\]

非分裂なら一つの `ψ_v` が全射となり、同じ代数閉包内で

\[
H=\ker\psi_v\subset G_{\mathbb Q},\quad
M=\overline{\mathbb Q}^{H},\quad F\subset M,\quad [M:F]=p
\]

を得る。`M/F` は Galois で、その Galois 群は巡回である。
添付レビューには Artin・Herbrand の経路と Kummer の経路の提案がある。
今回は実際に使用可能な Mathlib の逆 Kummer 定理へ接続した。
Artin 写像や Herbrand の消滅定理を仮定として追加してはいない。

## 2. Kummer 表示は根だけでなく生成性と既約性を持つ

一般の体拡大 `M/F` について、次のデータを束ねる。

```lean
structure CyclicKummer.Presentation (n : ℕ) (F M : Type*)
    [Field F] [Field M] [Algebra F M] where
  radical : M
  constant : F
  radical_pow : radical ^ n = algebraMap F M constant
  adjoin_eq_top : IntermediateField.adjoin F {radical} = ⊤
  irreducible : Irreducible (Polynomial.X ^ n - Polynomial.C constant)
```

`radical_pow` だけでは非自明な拡大は得られない。例えば `α=1,b=1` はどの体でもその等式を満たす。
`adjoin_eq_top` は選んだ根が同じ拡大全体を生成することを保証し、既約性は底体での冪への退化を除く。
底体の代数構造はパラメータで固定され、同型な別の拡大への取り替えは行わない。

## 3. 巡回拡大から根を実際に選ぶ

`CyclicKummer.exists_presentation` は、有限性・Galois 性・巡回性、
実際の次数 `[M:F]=n`、底体の原始 `n` 乗根から表示を構成する。
使用する Mathlib の定理は

```lean
exists_root_adjoin_eq_top_of_isCyclic
irreducible_X_pow_sub_C_of_root_adjoin_eq_top
```

である。第一の定理の内部では巡回 Galois 群の生成元を線形写像とみなし、
その最小多項式の原始根に対応する非零固有ベクトルを選ぶ。
その `n` 乗は Galois 群に固定されて底体に入り、生成元の位数と原始根の位数から
根を固定する部分群は自明となる。従ってその根で拡大全体を生成する。
第二の定理は、根の最小多項式と次数を比較して `X^n-b` の既約性を得る。
これらの証明への到達を再帰依存監査でも要求する。

今回の `F=ℚ(ζ_p)` には、指定した同じ `ζ_p` が原始根として入る。
`rootField_primitiveRoots` は、`ζ_p` を部分体の元に包装し、包含の単射性で原始性を戻す。
底体の原始根を別の provider として入力しない。

`CyclotomicCharacterKummer.exists_presentation` は前章の
`relative_finrank`、`relative_isGalois`、`relative_isCyclic` を使う。
Frey 終点 `residual_nonsplit_has_kummer_presentation` の入力には
根・定数・生成性・既約多項式・拡大体・次数・全射性の provider は残らない。
元の大域非分裂から同じ全射指標を選び、同じ核の固定体で表示を得る。

## 4. 定数は底体の `p` 乗ではない

一般の `n≠1` に対し、既約性から

\[
\forall c\in F,\quad c^n\ne b
\]

を得る。`Presentation.constant_not_pow` がこの結論である。
`1<n` なら `c=0` も代入でき、`b≠0`。根の冪の等式と包含の単射性から `α≠0` も従う。
ここでは `b` を整数や単数とは仮定していない。現段階では `b:F` であり、
整数化・素イデアルの付値・単数への分解は次の工程である。

## 5. 同じ根から相対 Galois 群を `μ_p` と同定する

生成性、根の冪の等式、底体の原始根から、同じ `M` が `X^p-b` の分解体であることを得る。
`Presentation.isSplittingField` はこれを証明する。
Mathlib の Kummer 自己同型の同型を使い、

\[
e:\operatorname{Gal}(M/F)\overset\sim\longrightarrow\mu_p(F),\qquad
\iota(e(\sigma))\alpha=\sigma(\alpha)
\]

を構成する。`autEquivRoots` と `autEquivRoots_smul` が対応する。
`α≠0` を用いれば、`autEquivRoots_ratio` より

\[
\boxed{\iota(e(\sigma))=\sigma(\alpha)/\alpha}
\]

となる。`ι:F→M` は前章と同じ包含から定義した写像である。
根を取り替えて別の作用公式を証明しているのではない。
`aut_fix_radical_iff` は `σ(α)=α ↔ σ=1` を保証する。

この相対 Galois 群の同定だけでは、`G_ℚ` の共役で根の直線がどう動くかはまだ結論できない。
元の逆円分指標の共役則から Kummer の `ω²` 固有成分を取り出す計算は未実装である。

## 6. 元の指標核を同じ根の固定群で検出する

`g∈Γ` を同じ `Gal(ℚ̄/F)` の元とみなす `kernelEquiv hζ` を使う。
`character_eq_one_iff_fix_radical` は

\[
\boxed{\psi_v(g)=0\iff g(\alpha)=\alpha}
\]

を証明する。Lean では値域を `Multiplicative C` としているので零値は `ψ_v g = 1` と書く。

順方向は `α∈M=ℚ̄^H` と同じ核への所属から従う。
逆方向では包含 `i:M→ℚ̄` と `g∘i` を `F` 上の準同型として比較する。
根で一致すれば `F(α)=M` により全元で一致する。
`Presentation.algHom_ext` は体の生成に関する帰納法でこの一致を示す。
従って `g` は `M` の fixing subgroup に入る。
開核の正確な無限 Galois 対応 `fixingSubgroup_characterField` により元の `H` に戻り、`ψ_v(g)=0` を得る。
核の閉包や別の指標へ置き換えないことが要点である。

## 7. 局所条件を同じ根に保持する

`residual_kummer_radical_decomposition_fixed_at_p` は、`p` 上の同じ付値環 `A` と
同じ円分体上の分解群の元が、この `α` を固定することを証明する。
`residual_kummer_radical_inertia_fixed_away` は `q≠p` での同じ慣性について同様に証明する。
後者には元の `hbad` が残る。その範囲は

\[
q\ge5,\quad q\ne p,\quad q\mid abc,\quad q\bmod p=\pm1
\]

の共鳴する悪い住所であり、一般的な不分岐 provider に取り替えていない。
これらは前章の体の全元の固定性を同じ `P.radical` に適用する。
整数環の素イデアルでの不分岐・完全分解の述語への接続は、引き続き別工程である。

## 8. 回帰例と監査

`DkMathTest.FLT.FreyCyclotomicKummer` では、実際の `GaloisField 3 2`、すなわち
`𝔽₉/𝔽₃` で次数2の表示を構成する。得られる定数は `𝔽₃` の唯一の非平方 `2` である。
同じ根を動かす相対自己同型も、Kummer 同型の逆写像で構成する。
自明な拡大 `𝔽₃/𝔽₃` では次数2の既約表示が存在しないこと、
次数1の表示では定数が実際に1乗であることを確認する。
これにより非自明な次数と生成性・既約性の境界を検証する。

依存監査は証明本体・型・帰納型の構成子を再帰的にたどり、
標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理、
外部 FLT 実装や完成済み FLT 終点への依存を拒否する。
公開入力の監査は、Frey 終点に Kummer 根や次数の provider が増えていないことと、
局所終点で元の `hbad` が保持されていることを確認する。
実行結果は [検証記録](evidence/validation-note032-cyclotomic-kummer.txt) に記す。

## 9. 残る算術

今回閉じたのは、非分裂から構成した同じ巡回拡大の Kummer 表示、
相対 Galois 群と根の群との同定、元の核の検出、同じ根の局所固定性である。
指標の零化は証明していない。

次には、根の空間の円分共役作用から `ω²` の重みを証明し、
定数の整数化・素イデアルの付値を整え、同じ Kummer 類を類群・単数の該当固有成分へ渡す必要がある。
その消滅、必要な長さの大域巡回塔の反復、共鳴住所の吸収と供給する幾何も残る。
前章までの良還元の固定点計数による最終障害は、引き続き `hCH` を必要としない。
**一般 `hno` は未完成である。**
