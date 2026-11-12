# NOTE-032 同じ有限核の剰余モデル・局所還元・整数標的の最小性

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 到達点

**同じ有限核Hで構成した付値環標的を既存kernelModelと同定し、全非零核点が特異点へ落ちる側では、源と商の剰余モデルの完全一致を証明した。同じSourceの既存整数標的への乗法的還元の輸送は、この側で完了した。さらに核の分岐に依らず、同じ整数標的の2での正式な最小性を証明した。**

滑らかな核の側も、同じHの還元準同型・単射性・正確な点数と、同じ商の剰余係数を同じ還元核から書くところまで実装した。節点曲線上の商不変量計算は残っており、両側を合わせた一般の還元保持はまだ結論しない。細かな内部枝番は追加していない。

| 数学的部品 | 今回の状態 |
| --- | --- |
| 同じHの付値環係数標的、一般ファイバー＝既存kernelModel | 証明済み |
| 係数構成と剰余写像の可換性 | 同じ添字・同じ核座標で証明済み |
| 特異点での二つの補正モーメントの消滅 | 任意標数で証明済み |
| 全非零核点が特異に還元する場合の源と商の剰余一致 | 証明済み |
| 同じ一次元Lの滑らかな側／零成分と交わらない側への分類 | Sourceで内部供給済み |
| 交わらない側、悪い奇素数q≠pでの整数標的の乗法的還元 | **正式なHasMultiplicativeReductionとして証明済み**。Disjoint仮定を保持 |
| c₄′=c₄+240T、c₆′=c₆+504b₂T+6048U | 任意可換環で証明済み |
| q∣240でのc₄単元性の輸送 | 核の分岐に依らず証明済み。q≠pを保持 |
| 同じ既存整数標的のc₄奇数性、2でのIsMinimal | **p≠2・一次元安定Lから証明済み** |
| abcを割る3,5での同じ標的のIsMinimal | q≠pの下、核の分岐に依らず証明済み |
| 滑らかな同じ核の還元準同型・単射性・像の点数p | 証明済み。位数・単元条件を内部供給 |
| 滑らかな側の同じ剰余標的の半核表示 | 証明済み |
| 滑らかな側での節点商の不変量、一般の良還元保持 | 未証明 |
| Δの深さの輸送、標的零成分への全点輸送 | 未証明 |
| スキームisogeny、標的有理捩れ排除、一般hno | 未完了 |

ここでSourceの「無条件の2での最小性」とは、核の局所分岐・未証明の幾何providerを追加しないという意味である。Source、p≠2、一次元L、Galois安定性という通常の入力は保持する。**2でのΔ非単元性・乗法的還元・Δ深さは、この結論に含まれない。**

## 1. 既存標的を同じ付値環で実現する

前段で、標数0・奇数有限核について

```lean
halfKernelPolynomialModel E H = kernelModel E H
```

を証明済みである。今回は同じHをnが消し、同じ源の付値環モデルMがあり、v(n)=1であるとする。既存の捩れ座標整性から、各核点のx,yを同じ付値環Aの元として包める。

`valuationKernelModel` は、この同じ半核と同じ座標で作るA係数の多項式モデルである。そのA→幾何学的係数体への像が、既存kernelModelに一致する。別の商モデルの存在を仮定する構成ではない。

A→剰余体κを適用すると、係数構成が同じ添字の座標の剰余と可換になる。ここでは `Finset.image` で重複を除かない。異なる核点が同じ特異点へ還元する側でも、元の有限和の重複度を保つためである。

## 2. 特異核側では剰余モデルが源と一致する

一般Weierstrass方程式の左右差をFとし、

```text
F_x = a₁y − 3x² − 2a₂x − a₄
F_y = 2y + a₁x + a₃
```

とする。同じ非特異性の定義から、方程式上の特異点では両式が零である。既存の補正項は

```text
t = 6x²+b₂x+b₄ = a₁ F_y − 2 F_x
w = F_y² + xt
```

なのでt=w=0となる。2も3も約分せず、標数2,3を含む任意の体で成立する。

全ての非零核点が滑らかに還元しなければ、半核の全代表についてこの消滅を適用できる。従ってT=Σt、U=Σwの剰余が零となり、商の五係数の剰余が源と一致する。Oは半核に含まれず、Oの便宜座標(0,0)を特異な有限点と見なす推論は使わない。

付値環の整な元aについて、

```text
res(a)=0  ↔ v(a)<1
res(a)≠0 ↔ v(a)=1
```

を一般化した。剰余モデルの一致をΔ,c₄へ適用すれば、源と商のΔ非単元性・c₄単元性が双方向に対応する。これは**付値の値そのものや深さの一致ではない**。

## 3. 同じSource・同じ整数標的へ運ぶ

Lは一次元なので、既存の同じ零成分残余空間E₀[p]に対して

```lean
L ≤ S.residualZeroComponent A ∨ Disjoint L (S.residualZeroComponent A)
```

が成り立つ。部分加群の原子性だけで証明する。第二の側では、非零H点の滑らかさを仮定すると対応するLの元が交わりに入り、零になるため矛盾する。

この側の剰余一致を、前段で証明済みの「同じ整数化の倍率dはq≠pで単元」と接続した。比較を三つに分けている。

1. 同じ源Mと同じ付値環商モデルの剰余が一致する。
2. 同じ付値環商モデルの一般ファイバーが既存の幾何学的標的に一致する。
3. 既存の同じℚ標的と既存整数標的は、q≠pでΔ,c₄の付値が一致する。

こうして、同じ整数標的のΔ非単元性・c₄単元性を同じ源へ比較する。悪い奇素数q≠pについて、源の既存算術からq∣Δ、q∤c₄を供給し、正式な `HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)` まで閉じた。これは最小性も含む既存の定義である。

`Disjoint` はこの定理の入力として残る。直線の二分を証明しても、一方しか処理していなければ全体の乗法的還元保持は結論できない。

## 4. 240という補正係数から、2での最小性を先に閉じる

同じ多項式モデルのb不変量公式から、任意可換環で

```text
c₄′ = c₄ + 240T
c₆′ = c₆ + 504b₂T + 6048U
```

を環計算で証明した。v(240)<1なら剰余体で240=0なので、c₄の単元性は**核のどちらの側でも**保持される。

同じSourceのp以外での核座標整性、既存整数化の単元倍率を接続すると、q∈{2,3,5}、q≠pで源のc₄単元性が既存整数標的へ移る。Sourceの正規化は源のc₄が奇数であることを既に与えるので、

```lean
S.residual_integer_target_c4_odd hp2 L hl hs
S.residual_integer_target_minimal_at_two hp2 L hl hs
```

には局所核の分岐仮定がない。Aと2上の住所も内部構成する。またabcを割る3,5では、源の既存算術から同様に正式な最小性を得る。

c₄の単元性は最小性を与えるが、Δが剰余で零かどうかを決めない。このため「2で最小」から「2で乗法的還元」へ進んだとは報告しない。

## 5. 滑らかな側の接続を、同じ核で整える

L≤E₀[p]の側では、同じHの全点が滑らかに還元する。モデル等式による実点加法同型と既存の零成分還元準同型を合成して

```lean
smoothKernelReduction E H A M hM hs : H →+ (M.map (residue A)).toAffine.Point
```

を構成した。v(n)=1で消える捩れに対する既存の還元単射性を使い、この同じ準同型が単射であること、像が有限でHと同じ点数であることを証明した。Sourceのn=pでは像の点数は正確にpとなる。

反転対の半核の像も点数を保ち、2×代表数+1=|H|となる。同じ準同型のx,yが、元の同じ整座標の剰余に一致することもOを含めて証明した。従って既存の付値環標的の剰余を、同じ還元核の半核座標で作る多項式モデルに書き直せる。

ここで得たものは**核Hの還元準同型**である。源の任意の零成分点を商標的の零成分へ送ることは別の命題であり、今回構成していない。

## 6. 実曲線の3点核で二つの側を検証する

実例を

```text
E : y²+xy+7y=x³
Q=(0,0), −Q=(0,−7), H={O,Q,−Q}
```

とした。接線群法から2Q=−Q、Hの閉性・点数3・3倍消滅を証明する。同じ半核がどちらの代表を選んでも、**既存kernelModelそのもの**が

```text
E′ : y²+xy+7y=x³−35x−350
```

であることを証明した。

| 不変量・還元 | 源E | 同じ既存標的E′ |
| --- | --- | --- |
| 整数判別式 | −2²·7³·47 = −64484 | −2⁶·7·47³ = −46512704 |
| c₄ | −167 | 1513 |
| 7上の非零核点 | 二点とも特異な剰余点へ落ちる | 源と剰余モデルが一致する |
| 47上の核 | 全点が滑らかに還元 | 同じ還元核の像は3点。剰余モデルは源と異なる |

整数不変量と因数分解、7上での特異性と同じ付値環標的の剰余一致、47上の滑らかさ・還元像の点数、ZMod 47上での係数モデルの不一致をLeanで検証した。7上で剰余モデルが一致しても、Δの素数7の指数は3と1で異なる。この例は剰余一致と付値の深さの一致を区別する教科書にもなる。

## 7. 模範解答との対応と残る命題

参照先は [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)。今回閲覧したファイルはいずれも `P2M/Sol/` 以下であり、取得内容のGit blob SHAを検証した。

| 参照した証明ファイル名（先頭S_WeierstrassCurve_を省略） | Git blob SHA | 今回の利用 |
| --- | --- | --- |
| dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale.lean | bb843e9595da6d9ce0e35ac31265d6a7faf55628 | 整数化と正式な還元判定の接続を確認 |
| exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.lean | e5fa016e031b0aaa4cfcb5c5dce3b9ada5e526ed | 付値環モデル・一般ファイバー・剰余の三者の対応を確認 |
| valuation_c4_add_veluTSum_lt_one_of_formal_kernel.lean | 2b1131a74343c767372dd1b5fd627297d9c6e918 | 特異核側の補正消滅の経路を確認 |
| valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative.lean | 3cc425db800fb824f7030fb6592f50b7f6b8dde8 | 滑らかな核と特異核の二分を確認 |
| veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.lean | fbe8b46b385ec6f97df009c8cb22a7e62c104cc8 | c₄,c₆補正式を添字付きモデルへ翻訳。節点公式の残件を確認 |

最後の証明は約1900行で、節点曲線の位数nの点が生成する奇数核についてc₄′=n⁴c₄、c₆′=n⁶c₆、Δ′=0へ進む。今回はその主結論をimport・公理・未証明の仮定で持ち込まず、同じ還元核と同じ標的への接続を先に固定した。

新規 `WeierstrassVeluReduction` の不変量補正式にはApache-2.0の翻訳元・blob・変更内容を記載し、既存の `RegularKummer/LICENSE` と `ANTHROPIC-NOTICE` を参照する。他の新規所有者は既存DkMathの整性・モデル同型・還元単射性・源算術から再構成した。外部の証明モジュールのimportは追加していない。

次は、滑らかな同じ還元核に対する節点商の不変量を閉じる。必要なのは、上で構成済みの同じ `polynomialModel` についての定理であり、異なる商曲線の存在だけでは不足する。Sourceで模範証明の巡回表示を使うなら、p点の同じ還元像から生成元を取り、既存半核との代表選択の差を反転不変性で吸収する接続も必要である。その後に一般の良還元保持、Δ深さ、全点零成分輸送を接続する。スキーム射としてのisogeny、標的有理捩れの排除と一般hnoは引き続き残る。

## 8. 実装と検証

本体は新規5所有者、公開39定理・5定義。Lib側4所有者とSource側1所有者に分けた。

- [WeierstrassVeluReduction](../../../DkMath/Lib/NumberTheory/WeierstrassVeluReduction.lean): 特異点のモーメント消滅、c₄,c₆補正。
- [WeierstrassResidueModel](../../../DkMath/Lib/NumberTheory/WeierstrassResidueModel.lean): 剰余・単元・不変量条件の輸送。
- [EllipticFiniteKernelReduction](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelReduction.lean): 同じ付値環モデルと特異核側。
- [EllipticFiniteKernelSmoothReduction](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelSmoothReduction.lean): 同じ滑らかな核の還元・点数・剰余座標。
- [FreyFiniteKernelReduction](../../../DkMath/FLT/FreyFiniteKernelReduction.lean): 同じSourceと既存整数標的への接続。

実行した検証は次の通り。

```text
./lean-build.sh DkMath.FLT.FreyFiniteKernelReduction
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReduction
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032LocalReductionSmoke.lean
lake env lean tmp/note032-local-reduction/Axioms.lean
```

本体と対象テスト、Source37の8定理、公開71宣言の公理監査は警告なしで通過した。対象テストは14定理・5定義で、上の実際の3点核を使う。公理依存は `propext`、`Classical.choice`、`Quot.sound` の範囲である。

Libの依存方向、教科書docstring・昇格マーカー、import直後のファイルマーカー、トラッカー、入口への静的登録、禁止構文と外部証明import、新旧ファイルの空白、旧数学所有者・NOTE・直前証拠の不変性も確認した。フルビルド・集約ルート・全テストは今回の実行範囲に含めず、ユーザー側の分担を維持する。

失敗した試行では、PointsとPointの群構造の差によるrewrite、Subtypeの係数・剰余座標の数値化、余分なFintype引数の警告を確認した。型付き等式・加法準同型でのnsmulの輸送、座標の剰余を明示する補題、未使用引数の除去で修正した。これらは数学的な仮定を弱める変更ではない。

[Source37スモーク](evidence/Note032LocalReductionSmoke.lean)、
[機械可読な検証記録](evidence/note032-local-reduction.json)、
[検証要約](evidence/validation-note032-local-reduction.txt)。
