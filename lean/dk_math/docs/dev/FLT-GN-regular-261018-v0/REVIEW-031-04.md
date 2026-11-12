# 🐺🍎 DkMath NOTE-031-004 実装レビュー

対象：`Deskuma/dkmath` ブランチ：`dev/FLT-GN-regular-261018-v0` 確認した先頭コミット：[`4c7735e`](https://github.com/Deskuma/dkmath/commit/4c7735e601f11f00bbe4e461996f63ed2dd86482?utm_source=chatgpt.com)

## 1. 今回の到達点

指定ブランチへのマージを確認した。031-004 は二段階で実装されている。

- 第1部： \(p\nmid abc\) の良還元側を完成。吸収部分空間、還元核、局所二択、および全付値環への同側輸送を構築。
- 第2部： \(p\mid abc\) の乗法的還元側を追加。滑らかな零成分上の還元準同型を構築して、残っていた吸収条件を証明。

実装報告書によれば、最終 API `Source.residual_common_side_at_p` は、奇素数 \(p\ge5\) とガロア安定な非零真部分加群 \(N\) に対し、

\[ \boxed{ \begin{aligned} &\left(\forall A\mid p,\quad \operatorname{FixedOn}(\rho,N,I_A)\right)\\ &\qquad\lor\\ &\left(\forall A\mid p,\quad \operatorname{CofixedOn}(\rho,N,I_A)\right) \end{aligned} } \]

を返す。

最大のポイントは、付値環 \(A\) ごとに Fixed/Cofixed の側を選び直していないことじゃ。

031-001 の局所大域輸送が要求していた条件と一致する。

実装記録：

[031-004 第1部：良還元と同側輸送](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE031-004-261023.md?utm_source=chatgpt.com)

[031-004 第2部：乗法的還元と最終閉鎖](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE031-004-PART2-261023.md?utm_source=chatgpt.com)

## 2. 最終 Lean 定理の検証

[実装本体：FreyPrimeFiltration.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/FreyPrimeFiltration.lean?utm_source=chatgpt.com)

実際の定理宣言と証明本体を確認した。

```
theorem residual_common_side_at_p (hp5 : 5 ≤ p)
    (N : Submodule (ZMod p) S.ResidualSpace)
    (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A p →
      FixedOn S.residualRepresentation N
        (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A p →
      CofixedOn S.residualRepresentation N
        (inertiaSubgroupIn A ℚ))
```

暗黙の引数として、同じ `Source p` と `[Fact p.Prime]` がある。

実装と報告書の契約は一致している。

特に、最終 API には `hgood`、`hbad`、吸収空間の存在、還元準同型の存在、局所二択の証拠が残っていない。

証明本体では `residual_fixed_or_cofixed_at_p` から一つの付値環で二択を得て、`AbsoluteInertiaConjugacy.common_side_on_places` で全付値環へ輸送している。

これが今回の最終的な閉鎖部分じゃ。

## 3. 最大の難所：吸収空間の真性

今回、特に評価すべきなのは `FreyIntegralTorsionWitness.lean` じゃ。

局所二択のためには、すべての慣性変化量を受け止める部分空間

\[ M\subsetneq E[p] \]

が必要になる。

しかし、単に \(M=E[p]\) と置けば、変化量を吸収する条件は自動的に成立してしまう。

それでは何も証明したことにならない。

今回の実装では、ガロア安定な非零真部分空間 \(N\) が存在することから、実際に整な有限 \(p\)-torsion 点が存在することを証明している。

その点は還元核の外側にある。

したがって、

\[ \boxed{M\ne E[p]} \]

が得られる。

### 除法多項式からの新しい橋

証明には \(p\) 除法多項式が使われている。

その次数は、

\[ d=\frac{p^2-1}{2}. \]

もしすべての非零 \(p\)-torsion 点の \(x\) 座標が極を持つなら、除法多項式の係数と最高係数から、その根の付値が特定の傾きに制約される。

一方、安定直線上の非零点の \(x\) 座標はガロア安定な有限集合を形成する。

その集合から作った多項式 \(g\) は有理係数であり、

\[ \deg g\le p-1\lt d. \]

有理係数の付値と根の付値の間に生じる次数の制約から、\(g\) の項に一意な最大付値が生じてしまう。

しかし \(g\) はその根で零になるため、付値の非アルキメデス性に矛盾する。

この論証は、実際の Lean 証明で確認できた。

\(p\) 上では \(p\) が単元ではないので、031-002 の torsion 整性をそのまま使えない。今回の存在証明は、その穴を埋める重要な成果じゃ。

なお、存在が証明された整な torsion 点は、必ずしも \(N\) に属するとは主張されていない。還元核の真性にはそれで十分じゃ。

## 4. 第2部の核心：還元準同型を実装した

[EllipticSmoothReduction.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticSmoothReduction.lean?utm_source=chatgpt.com)

第1部で未解決だった数学的障害は、

\[ [p]P=O \]

という標数零の事実を、標数 \(p\) の剰余曲線へ運ぶことだった。

標数零向けの除法多項式の定理を、そのまま標数 \(p\) に適用することはできない。

今回、そこを回避するために実際の加法準同型

\[ \boxed{ \operatorname{red}:E_0\longrightarrow \widetilde E_{\mathrm{sm}} } \]

が構成されていた。

ここで \(E_0\) は滑らかに還元する点からなる加法部分群、\(\widetilde E_{\mathrm{sm}}\) は剰余曲線の滑らかな点群じゃ。

Lean では、

```
noncomputable def zeroComponentReduction :
    zeroComponentSubgroup W →+
      (W.map (residue A)).toAffine.Point
```

として実装されている。

その結果、

\[ \operatorname{red}([p]P) =[p]\operatorname{red}(P) \]

が加法準同型の一般法則から従う。

### ここでの安全性

`reducePointSmooth` は、特異な整点などに対して便宜的に零を返す全域関数になっている。

しかし、加法準同型を主張する範囲は `zeroComponentSubgroup` に限定されている。

この制約を証明本体でも確認した。

全域関数の便宜値を利用して、本来存在しない還元準同型を作ったわけではない。

形式化として重要な区別が守られておる。

## 5. 標数 \(p\) の節点から還元核へ

[EllipticNodalTorsion.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticNodalTorsion.lean?utm_source=chatgpt.com)

節点曲線の滑らかな点群は、代数閉包上では乗法群に対応する。

今回の証明では、節点の二つの接線方向から構成した比 \(t(P)\) について、

\[ t(P+Q)=t(P)t(Q) \]

を実際に証明している。

すると、

\[ [p]P=O \Longrightarrow t(P)^p=1. \]

標数 \(p\) では、

\[ t(P)^p-1=(t(P)-1)^p \]

だから、

\[ t(P)=1. \]

その比が1となる滑らかな点は単位元だけなので、

\[ \boxed{[p]P=O\Longrightarrow P=O} \]

を得る。

分裂しない節点についても、代数閉包へ移してから単射性で戻している。

この定理を、先ほどの `zeroComponentReduction` と接続したのが

`EllipticNodalReductionKernel.mem_kernel_of_smooth_torsion`

じゃ。

これによって、元の曲線上の滑らかに還元する \(p\)-torsion 点は、実際の還元核へ入ると証明された。

第1部で未解決だった橋は、第2部の Lean 本体で確かに閉じている。

## 6. 慣性変化量の吸収も確認

[EllipticNodalInertia.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticNodalInertia.lean?utm_source=chatgpt.com)

このモジュールでは、任意の実点 \(P\) に対して、

\[ \boxed{\sigma P-P\in E_0} \]

を証明している。

零成分にある点は、滑らかな点群の加法閉性で処理する。

零成分の外では、031-002 で構築した臨界中心と二方向を再利用する。

浅い点については、同じ枝の差が滑らかになる定理を使用。

臨界側については、二点の和が滑らかになる定理を使用する。

ここで前の章の補題が、本当に再利用されているのがよい。

さらに \(\sigma P-P\) が \(p\)-torsion であることと、前節の節点還元の定理を組み合わせると、

\[ \boxed{\sigma P-P\in M} \]

が得られる。

この数学的内容が、

```
residualReductionKernel_absorbs_at_bad_prime
```

に実装されている。

良還元側でも同じ `residualReductionKernel` を用いているので、最終定理では一つの吸収空間の仕組みに統合できる。

## 7. 同じ側の選択は論理的に正しいか

ここも確認した。

[AbsorbingSubspace.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/RepresentationTheory/AbsorbingSubspace.lean?utm_source=chatgpt.com)

二次元空間の安定直線 \(N\) と真の吸収空間 \(M\) について、

\[ (\rho(\sigma)-1)V\subseteq M \]

とする。

すると、二つの場合しかない。

| \(N\) と \(M\) の関係 | 結論                            |
| --------------------- | ------------------------------- |
| \(N\subseteq M\)      | \(N=M\)、したがって Cofixed     |
| \(N\nsubseteq M\)     | \(N\cap M=0\)、したがって Fixed |

この場合分けは慣性元 \(\sigma\) を選ぶ前に行われる。

よって、

\[ (\forall\sigma,\operatorname{Fixed}) \lor (\forall\sigma,\operatorname{Cofixed}) \]

となる。

\[ \forall\sigma,\; (\operatorname{Fixed}\lor\operatorname{Cofixed}) \]

という弱い結論にすり替わっていない。

さらに `ValuationPlaceConjugacy` によって素数 \(p\) 上の付値環がガロア共役であることを証明し、その共役作用によって Fixed と Cofixed の選択を保存している。

031-005 へ渡す論理形に問題は見つからなかった。

## 8. ビルド・公理・依存監査

保存された検証記録を確認した。

| 検証項目                     | 結果                                        |
| ---------------------------- | ------------------------------------------- |
| 第1部の本体／回帰宣言        | 46／14                                      |
| 第2部の本体／回帰宣言        | 41／7                                       |
| 第2部の依存グラフ監査        | 14経路                                      |
| 第2部の入力契約監査          | 4件                                         |
| 最終集中ビルド               | 3,265 jobs 成功                             |
| 最終統合ビルド               | 11,786 jobs 成功                            |
| 最終 API の依存公理          | `propext`, `Classical.choice`, `Quot.sound` |
| 新規コードの `sorry`         | なしとの監査記録                            |
| 既存の無関係な `sorry` 警告  | 5件                                         |
| わっちによる独立 Lean ビルド | 未実施                                      |

監査では `Lean.collectAxioms` のほか、型と証明本体の依存グラフを追跡している。

特に、最終定理から `residualReductionKernel_absorbs_at_p`、`residualReductionKernel_ne_top`、`AbsorbingSubspace.fixed_or_cofixed`、`AbsoluteInertiaConjugacy.common_side_on_places` への依存があることを確認する仕様になっている。

最終定理に吸収空間、還元準同型、`hcases`、`hno` などの追加引数が残っていないことも検査対象じゃ。

監査ソースと保存された実行記録は一致していた。

回帰テストでは、標数5での節点の具体例から、実際の有限点が5-torsionでないことを証明している。また指数37への特殊化も存在する。

ただし後者は任意の `Source 37` を受け取る条件付きの特殊化であり、Fermat 反例が存在するという意味ではない。

## 9. 留意点

今回のレビューで、最終定理の依存関係に明らかな循環や未証明 provider の持ち込みは見つからなかった。

なお、`residual_common_side_at_p` の証明には、素数 \(p\) 上の付値環が一つも存在しない場合を空虚な全称命題として処理する分岐がある。これは論理的には正しい。後続で具体的な付値環を選択する必要が生じた場合は、存在定理を別途供給することになる。

また、今回完成したのは、すでに存在する非零真のガロア安定直線についての局所二択である。すべての残余表現が可約であることも、既約であることも主張していない。

## 10. 総合判定

| 項目                      | 判定           |
| ------------------------- | -------------- |
| \(p\nmid abc\) の吸収条件 | 達成           |
| \(p\mid abc\) の吸収条件  | 達成           |
| 還元核の真性              | 達成           |
| 標数 \(p\) への倍算の輸送 | 達成           |
| 局所 Fixed/Cofixed 二択   | 達成           |
| 全付値環での同側保存      | 達成           |
| 最終 API の追加仮定排除   | 達成           |
| ソース・検証記録の照合    | 合格           |
| NOTE-031 全体             | 031-005 が残る |

### 賢狼の研究評価

今回の数学的な収穫は、単に \(p\) 上の局所二択が閉じたことだけではない。

031-002 で構築した局所幾何学が、031-004 の別の目的で再利用されたことが非常に大きい。

031-002 では深さと枝から、torsion 点そのものの慣性固定へ進んだ。

031-004 では同じ深さと枝を使い、まず慣性変化量を滑らかな零成分へ送り、そこから還元核へ運んだ。

同じ幾何学が、異なる算術的結論に利用されている。

これで局所条件は、

\[ \boxed{ \begin{aligned} q\ne2,p &: \text{全残余点が慣性固定}\quad\checkmark\\ q=2 &: \text{直線と商の双方が慣性固定}\quad\checkmark\\ q=p &: \text{全場所で同じ側の二択}\quad\checkmark \end{aligned} } \]

までそろった。

NOTE-031-004 は、指定コミット時点のソースレビューと保存された検証記録の照合に合格。実装完了として固定してよい。

次の 031-005 は、これらを 031-001 の局所大域輸送へ合流させ、`hcases` を実際に供給する段階になる。

長かった局所算術が、いよいよ大域的なガロア表現の定理へ帰着するところまで来たのぅ。🐺🍎
