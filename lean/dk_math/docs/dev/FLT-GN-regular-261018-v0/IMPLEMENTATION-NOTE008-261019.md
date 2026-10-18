# NOTE-008 素数・指標射影・深度輸送の教科書実装

日付: 2026-10-19。NOTE-008 の数学的な提案を、既存の実際の対象へ接続して実装した。
本文の過去成果の評価と将来の見通しは記録として保持した。

## 1. 今回の接続

| 系統 | 実装した内容 | 残る境界 |
| --- | --- | --- |
| IRR-009 | 実際の37-torsion類群の36指標射影、直交・冪等性、復元、直和同型 | 非零類の存在・成分次元・Herbrand–Ribet |
| State37 | 整数座標での全消滅／非零位相全残存の二分律、記録済み障害の指標射影 | 全障害の消去・単元の37乗化・FLT37 |
| Frey | 素数指数p≥5で `p∣vℓ(Δ_min) ↔ ℓ≠2`、mod-p剰余の統一式 | Artin導手・残余表現・レベル降下 |
| Legendre | `v_q(j)=3v_q(Qₙ)`、厳密な有限深度証明書、Hensel次桁と深度実現 | 素数存在・無限枝・Legendre予想・CM |
| 素数での比較 | 同じqで二曲線の付値公式を並べ、旧支持q≤nを保持 | 二曲線やガロア表現の同一視 |

追加は本体6モジュール、回帰2モジュール、依存監査1モジュールである。
全ての新規Leanモジュールに import 後の `#print "file: モジュール名"` と解説を置いた。

## 2. 有限補間から指標射影へ

`DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors` は、体F上の線形作用素Tに対し、
相異なる有限節点vᵢの消失多項式 `∏ᵢ(X−vᵢ)` がTを消すという条件から始める。

1. Lagrange基底多項式LᵢをTに代入して `Pᵢ=Lᵢ(T)` を定義する。
2. `(X−vᵢ)Lᵢ = cᵢ∏ⱼ(X−vⱼ)` より、`T(Pᵢx)=vᵢPᵢx`。
3. 固有空間j上の `Pᵢ` はi=jなら恒等、それ以外なら零。
4. `∑Lᵢ=1` より `∑Pᵢ=id`。冪等性と直交性も従う。
5. `x↦(Pᵢx)ᵢ` と成分の和を互いに逆として、固有空間の実際の有限直和との線形同型を構成する。

有限次元性や固有基底の存在を追加の仮定にしていない。
非空な索引の条件は和による復元と分解だけに要求する。

`DkMath.Lib.NumberTheory.Cyclotomic37CharacterDecomposition` は、この一般構成を
円分体K/ℚの実際の類群へ適用する。

- `torsionGroup K` は類群の37乗準同型の核。`Space K` は同じ部分群の加法記法。
- `underlying` は元の類への単射。零は主イデアル類、スカラーcの作用は `w^c.val`。
- `actionMul` は既存の `ClassGroup.mulEquiv (sigma a)` の制限。
  これをF₃₇線形にし、既存の自己同型の合成則から群作用 `action` を構成する。
- F₃₇ˣの生成元gを選び、`T=action g` とする。群の位数36から `T^36=1`。
- F₃₇ˣの36個の元はX³⁶−1の相異なる根なので、有限補間の仮定を供給できる。

固有値ラベルaごとに、gをaへ送る乗法指標 `character a` を構成した。
`character_injective` はこれらが相異なることを示す。
`mem_component_iff` は線形な固有成分の所属と、既存の実際の類群上の
`characterComponent (character a)` の所属を同値にする。
生成元に対する固有値等式を全てのガロア元へ広げる部分も証明している。

`decomposition` の型は次の通りである。

```lean
Space K ≃ₗ[ZMod 37] ⨁ a : (ZMod 37)ˣ, component (K := K) a
```

`sum_projector` は元の類のベクトルを射影の和から復元する。
`component_one` と `projector_one` は、前回の算術的な全共役ノルムによって
自明指標成分が零となることを証明する。単なる形式的な表現分解だけでは、この消滅は得られない。
`exists_nontrivial_component` は、入力の非零類があれば非自明指標のどれかで非零となることを示す。
生成元と指標のラベルは選択に依存する。Bernoulli非正則対の標準的な指数ラベルとの同定は行っていない。
対象は37で消える部分であり、37²以上で消える類全体の分解ではない。

## 3. Stateの同じ障害を分解する

`DkMath.FLT.Kummer.IrregularCharacter37` の
`observe_obstruction_dichotomy` は、x,yが整数A,Bに由来する仮定を保持する。
位相1の障害が自明かどうかで場合分けし、既存の位相0消滅と非零位相の同値を使う。
従って、全37位相で障害が消えるか、位相0のみ自明で残り36位相は全て非自明である。

`observeVector E i` は記録済みの同じ障害と、その37乗が1である証拠を
実際の `Space Cyclotomic37` に入れる。イデアル根や障害を選び直さない。
`underlying_observeVector` で同じ類が戻ることを確認できる。
`observe_nontrivial_character` は、非自明な障害という入力から、非自明指標の非零射影を得る。
このベクトル化と射影自体には整数座標条件は不要である。

任意の類の全共役ノルムが1である以上、それを繰り返すだけでは残りの障害は消えない。
今回の構成は障害の成分を観測するものであり、Stateの非存在証明ではない。

## 4. 素数2の補正をmod-pで読む

`DkMath.FLT.FreyPrimeProfile` は同じ `Source p` の同じ有理最小モデルを使う。

\[
 v_\ell(\Delta_{\min})\bmod p=
 \begin{cases}-8&\ell=2,\\0&\ell\ne2.\end{cases}
\]

`two_discriminant_cast` と `discriminant_cast_profile` がこの剰余体での等式を与える。
`prime_not_dvd_eight` により、p≥5の素数について補正は消えず、
`exponent_dvd_valuation_iff_ne_two` が全素数ℓでのp倍性を分類する。
算術式はℓ=pも含む。これは残余表現のpでの局所理論を証明したという意味ではない。

回帰ではp=2の実際のSource `(a,b,c)=(4,3,5)` を構成した。
同じ正規化条件を満たし、2での判別式付値はp倍となる。
p≥5という前提を落とせないことを、空の仮定からではなく実例で確認する。
還元型から独自の0/1関数を定義して導手と呼ぶ実装は追加していない。

## 5. 中央席のHensel住所とj深度

`DkMath.NumberTheory.Legendre.FreyJDepth` は、既存の実際の `WeierstrassCurve.j` の
有理公式から付値を計算する。素数q∣Qₙならq≠2かつq∤n(n+1)なので、
256と分母の付値は零である。従って `rationalJ_valuation` が

\[
 v_q(j(E_n))=3v_q(Q_n),\qquad Q_n=n^2+n+1
\]

を得る。n>0とqの素数性・整除を保持し、q=3を除いていない。
`rationalJ_depth_of_exact_divisibility` は `q^k∣Qₙ` と `¬q^(k+1)∣Qₙ` を
入力とする有限証明書を付値3kへ送る。旧支持の入口ではq≤nを残す。

整数多項式 `centralPolynomial=X²+X+1` を、既存の有限Hensel桁APIへ渡す。
`4Qₙ−(2n+1)²=3` からq≠3なら微分がqで割れない。
`existsUnique_central_next_digit` は一段上がる桁の一意性を証明する。
`exists_central_exact_jDepth` はその桁以外を選び、正の自然数の同じ住所
`n+q^k*s.val` における厳密なQ深度kとj深度3kを同時に実現する。

数値回帰は、n=18,q=7,k=3でj深度9、上昇桁3によるn=1047でj深度12。
q=3,n=1ではj深度3となる一方、微分も3で割れるため単純根の分岐例外になる。
q=2,n=1ではj深度6であり、q∣Qₙという前提を省いた公式は成立しない。

`DkMath.FLT.PrimeDepthBridge` は中央席の同じ素因子qで、Legendre曲線のj深度3倍と
独立なSourceのFrey曲線の最小判別式深度2p倍を並べる。
これは独立の二曲線の比較であり、互いの一致や円分体のガロア表現との同一視ではない。

## 6. 検証と公開入口

公開入口は `DkMath.Lib`、`DkMath.FLT.Kummer`、`DkMath.FLT`、
`DkMath.NumberTheory.Legendre` とルート `DkMath`。
回帰23件と依存監査は `DkMathTest.lean` に接続した。
監査は新規公開64宣言の使用公理と、主要10経路の実際の型・証明本体を調べる。
標準論理公理のみを許し、外部FLT終点・全域的な正則性providerを禁止する。

検証結果とコマンドは [検証証跡](evidence/validation-note008.txt) に記録した。
focused監査build（9,018 jobs）、統合build（11,520 jobs）、ルートsmoke、
統合build後の `DkMathTest.lean` 直接検査は全て成功した。
公開64宣言の公理監査と主要10経路の依存監査も通過した。
新規9モジュールの警告はなく、指定のマーカーはログ上でも全て一致する。
`git diff --check` と、新規本体での `sorry`・`admit`・独自 `axiom`・`native_decide` の不使用検査も通過した。
