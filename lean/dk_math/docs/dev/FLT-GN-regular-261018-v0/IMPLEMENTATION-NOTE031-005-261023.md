# NOTE-031-005: 局所条件の合流と同じ安定直線の大域二択

2026-10-23（JST）。ブランチ `feat/FLT-GNR-031-05-261023-codex`。

**031-005を実装した。** 031-002〜004の局所算術を合流し、031-001の大域化へ接続した。
同じSourceの安定直線は全絶対ガロア群でFixedまたはCofixedとなる。
b偶数の場合はNOTE-030の固定点消滅でFixed側を排除し、可約性からCofixed安定直線を抽出する。
従来の `hcases` は外部入力ではなく証明済みの算術から供給する。
既約性の入口にはCofixed安定直線の不存在 `hno` を残し、一般FLTの完成とはしない。

## 1. 公開契約

実装は [FreyStableLineLocalGlobal.lean](../../../DkMath/FLT/FreyStableLineLocalGlobal.lean) にまとめた。
NOTEの型案を、既存APIと必要な仮定に合わせて次の形へ固定した。

| 宣言 | 入力と結論 |
|---|---|
| `residual_inertia_common_side_of_stable` | p≥5、全ガロア安定な真の非零Nから全素数共通の局所二択 |
| `residual_stable_submodule_fixed_or_cofixed` | 同じNを全絶対ガロア群でFixedまたはCofixedへ |
| `residual_stable_line_fixed_or_cofixed` | 同じ直線の次元1と安定性から大域二択 |
| `residual_stable_line_cofixed_of_oriented` | b偶数なら任意の同じ安定直線はCofixed |
| `residual_exists_cofixed_line_of_not_irreducible` | b偶数・可約性からCofixed安定直線の存在 |
| `residual_isIrreducible_of_oriented_cofixed_obstruction` | b偶数とhnoを入力とする条件付き既約性 |
| `residual_not_irreducible_iff_exists_cofixed_line_of_oriented` | b偶数の下で可約性とCofixed安定直線の存在の同値 |
| `ofCounterexample_residual_exists_cofixed_line` | 元の整数反例から選んだ同じSourceと正規化証拠を保つ入口 |

全宣言は `[Fact p.Prime]` と5≤pを保持する。
局所合流と大域二択そのものには `Even S.b` は不要だった。
この仮定は、NOTE-030の有理p-torsion排除でFixed側を排除する入口に明示する。
Sourceの曲線、残余空間、ガロア作用、直線、商を途中で選び直さない。
旧来のhcases付き一般形は署名を変えずに残し、新しい入口がその引数を供給する。

## 2. 教科書の証明経路

p上では031-004により、次のどちらか一つの側が全てのp上の付値環で成立する。

\[
(\forall A\mid p,\ \operatorname{FixedOn}(\rho,N,I_A))\quad\lor\quad
(\forall A\mid p,\ \operatorname{CofixedOn}(\rho,N,I_A)).
\]

2上では031-003によりFixedとCofixedが同時に成り立つ。
2,p以外では031-002の全残余点の慣性固定から、同じく両方が成り立つ。
従ってp上で選んだ側を全ての素数へ拡張できる。
群元や場所ごとの独立した二択を、大域の二択へ交換しているわけではない。

031-001の大域化は、同じ実際のtorsion表現の開核と有限ガロアレベルを用い、
Minkowskiによる数体の慣性生成へ還元する。ここへ全素数共通の側を渡すことで

\[
\operatorname{IsFixedOn}(\rho,N)\quad\lor\quad\operatorname{IsCofixedOn}(\rho,N)
\]

を得る。次元1の直線は、同じ二次元残余空間で真かつ非零なのでこの結果を適用できる。
本章で新たな局所数論のproviderや新しい公理を置く必要はなかった。

b偶数なら、NOTE-030の同じ有理曲線のp-torsion排除から非零ガロア固定残余点が存在しない。
Fixedな非零直線はこれに矛盾するため、Cofixed側だけが残る。
可約性から既存の幾何学的次元2によって安定直線を取り、その直線の大域二択を旧来の抽出定理へ渡す。
こうして従来未供給だったhcasesを除いた公開入口を得た。

逆にCofixed安定直線があれば、その安定直線だけで既約性に反する。
そのため、b偶数の場合の可約性とCofixed安定直線の存在は同値となる。
これはCofixed直線を排除する証明ではなく、残る課題を同じSource上で正確に表す同値である。

## 3. 整数反例からの入口

`ofCounterexample_residual_exists_cofixed_line` は、元のa,b,cの非零性と冪和等式から既存の同じ選択済みSourceを使う。
そのSourceの可約性を仮定した場合に、次を同時に返す。

- 4∣S.a+1 と `Even S.b`。
- 元の反例の `PrimitiveReduction` と、同じSourceへの `OrientationTrace`。
- 同じ残余空間のCofixed安定直線。

共通因子や符号付き置換の証拠を落とさず、正規化後の座標と元の整数座標を同一視しない。
反例の存在や残余表現の可約性を構成したという主張でもない。

## 4. 検証と依存

本体8公開定理、回帰7公開定理を追加し、各定理に教科書docstringを付けた。
指定の `#print "file: ..."` を付け、FLTと通常テストの公開入口へ接続した。

回帰では、指数37の大域二択に局所providerを要求しないこと、Cofixed抽出にhcasesを要求しないこと、
既約性の条件付き入口にhnoが残ること、整数反例からの同じSourceと正規化証拠を保持することを確認した。
指数2の実在する固定点と、各局所群で別々に選んだ二択からは大域化できない有限表現も境界として検査した。
これらのSource37の入口はSource37や整数反例の存在証明とは区別する。

依存監査では全8本体・7回帰定理の公理を調べ、12本の型とopaque本体の依存グラフ、7本の入力契約を検査した。
局所合流にはp上・2上・2,p以外の三つの経路、大域化には実際の慣性生成とMinkowskiへの到達を要求する。
大域二択にはFoldedValuationOrbitへの依存を禁止する。
Cofixed選択では、NOTE-030の有理torsion排除が実装済みの整数付値軌道を用いるため、その実際の経路を要求する。
これは未証明providerの追加ではない。
外部FLT終点、P2M/P2MW、FreyPackage、RegularKummer、Kummer、sorryAxは全経路で禁止する。

全8本体・7回帰定理の依存公理は `propext`, `Classical.choice`, `Quot.sound` のみだった。
これは監査した経路の結果であり、リポジトリ全体から既存の未完成研究コードを排除したという意味ではない。

`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,789ジョブで成功した。
`lake env lean DkMathTest.lean` と、`import DkMath` だけから新しい終点を参照するスモークも成功した。
ファイルマーカー検査と静的検査、`git diff --check` も通過した。全体ビルドには既存の別経路のsorry警告5件があり、証跡へ記録した。

実行結果、環境、依存経路、公開入口の検証は以下へ記録した。

- [validation-note031-005.txt](evidence/validation-note031-005.txt)
- [dependencies-note031-005.json](evidence/dependencies-note031-005.json)
- [RootSmokeNOTE031StableLineLocalGlobal.lean](evidence/RootSmokeNOTE031StableLineLocalGlobal.lean)

## 5. 到達点と残る境界

NOTE-031の五段階を、同じ残余表現の大域二択と可約ならCofixed直線が存在する終点へ接続した。
NOTE-030から残っていたhcasesは供給済みとなった。
既約性へ進む残りの算術的障害はhno、すなわち同じSourceにCofixed安定直線が存在しないことである。
hno自体、一般のFrey表現の無条件既約性、一般FLTは本章では証明していない。
