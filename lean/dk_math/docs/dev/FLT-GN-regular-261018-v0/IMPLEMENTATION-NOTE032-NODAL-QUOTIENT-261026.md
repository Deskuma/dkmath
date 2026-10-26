# NOTE-032 節点商の不変量と、悪い素数での乗法的還元

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 到達点

**前回残った滑らかな核の節点商公式を証明し、同じSourceの既存整数標的について、悪い奇素数q≠pでの正式な乗法的還元からDisjoint仮定を除去した。p≥5では2でも正式な乗法的還元まで証明した。**

同じL、実点核H、既存半核、付値環モデル、幾何学的kernelModel、降下したℚ標的、前段の整数標的を維持している。新しい商曲線の存在だけで代用せず、同じ剰余座標の多項式モデルに不変量公式を適用した。細かな内部枝番は追加していない。

| 内容 | 今回の到達点 |
| --- | --- |
| 有限群の反転対の代表を変えた半集合和 | 反転不変な関数について一致。2による約分不要 |
| Pascal係数と反転対の積表示 | 有限多項式として証明済み |
| 逆数の一次・二次・三次冪和 | 整数係数を介した分母払い済みの式で証明済み |
| 節点比tcの原始根性、同じ実点のx座標表示 | 既存Frame・点群から証明済み |
| 同じ巡回核・任意の同じ半集合による商 | c₄′=n⁴c₄、c₆′=n⁶c₆、Δ′=0を任意標数で証明済み |
| 同じ素数位数核の巡回表示 | 正確な位数pから内部構成済み |
| 付値環標的の剰余と同じ還元核の接続 | 前段の接続を利用し、滑らかな側の節点不変量を証明済み |
| 滑らかな側／特異な側の一括処理 | 両側で同じ既存標的のΔ非単元・c₄単元を証明済み |
| Sourceの悪い奇素数q≠pでの乗法的還元 | **Disjoint・住所・中心・方向の追加入力なし** |
| Sourceの2での乗法的還元 | **p≥5で正式に証明済み**。前回の最小性だけの結論を拡張 |
| 良い素数での良還元保持、q=pの制御 | 未証明 |
| Δの深さ、全点零成分輸送 | 未証明 |
| スキームisogeny、標的有理捩れ排除、一般hno | 未完了 |

通常のSource・一次元直線L・Galois安定性という入力は保持する。q≠pも保持しており、大域的な半安定性全体を閉じたとは主張しない。

## 1. 半核の代表を変えても同じ有限和となる

有限加法群Gの半集合sを

```text
s ∪ (−s) = G \ {0},    s ∩ (−s) = ∅
```

で定義した。反転不変なfについて、二つの半集合s,tの和は一致する。証明は、s∩tの和を共通部分として分離し、残るs\tとt\sを反転で一対一に対応させる。

全非零点の和を2で割る議論ではない。値を取る群の標数が2でも成立する。巡回表示e:ZMod n≃+Gに対して、奇数nなら1,…,⌊n/2⌋の像が半集合となることも証明した。

この一般補題により、DkMathの既存 `halfKernel` と、模範証明の巡回生成元による正の半周の違いを吸収する。既存の半核を定義から置き換える必要はない。

## 2. Pascalの係数比較から、反転対の冪和へ

uを奇数位数nの原始根、m=⌊n/2⌋とする。

```text
τ_l = (1−u^l)(1−u^(n−l))
z_l = u^l/(1−u^l)^2
τ_l z_l = −1
∏ τ_l = n                     (1≤l≤m)
```

核心となる有限多項式恒等式は

```text
(1−X)^n + X^n = ∏ (1 + τ_l (X²−X))
```

である。左辺のn次項は奇数性によって相殺する。両辺の次数・最高係数と同じn−1個の相異なる根を比較して積表示を証明し、右辺を有限対称和で展開する。

下から1,3,5,7次の係数を比較し、整数上の補正係数A₁,A₂,A₃を得る。

```text
A₁ = choose(n,3) − n choose(m,2)
A₂ = choose(n,5) − choose(m−1,2) A₁ − n choose(m,4)
A₃ = choose(n,7) − choose(m−2,2) A₂ − choose(m−1,4) A₁ − n choose(m,6)
```

Newtonの最初の三恒等式と、補集合による逆数の対称和の比較から

```text
n Σz_l     = −A₁
n²Σz_l²    = A₁² − 2nA₂
n³Σz_l³    = −A₁³ + 3nA₁A₂ − 3n²A₃
```

を得る。`firstCoefficient`、`secondCoefficient`、`thirdCoefficient` と `power_sums` を独立したLib APIとして公開した。

整数係数の計算に有理数を使う箇所はあるが、**等式を一度整数上で確定してから任意の体へ写す**。剰余体で2,3,6等を割る推論は含まない。n=1,3,5の小さい場合は、空になる対称和を別に検証している。

今回使ったのは、DkMathにも馴染む二項係数・有限和・対称和の計算である。GNの既存定理から直接hnoを導いたわけではなく、この係数算術を独立に固定した。

## 3. 商の不変量を決める三つの証明書

正の半周に沿う重み付きモーメントを

```text
T = Σ(z_l+6z_l²)
U = Σ(2z_l²+10z_l³)
```

とすると、上の整数係数から次を証明できる。

```text
240T = n⁴−1
504T+6048U = 1−n⁶
T+7U−47T²−3528TU−21168U²+8000T³ = 0
```

最初の二式がc₄,c₆の補正を決め、第三式がΔ=0を直接決める。**c₄³−c₆²=1728Δから1728を約分していない。** これが標数2・3での使用に必要な点である。

原始n乗根が体に存在すれば、その体でnは非零となることも内部で証明する。最後の係数比較で約分するのは、この非零なnの冪だけである。

## 4. 既存の節点比から、同じ核座標を読む

既存 `EllipticNodalTorsion.NodalTorsion.Frame` は、同じ節点(x₀,y₀)と接方向αの方程式・偏微分条件を持つ。もう一方向をβ=−a₁−α、差をδ=α−β=2α+a₁とする。

既存の節点比

```text
tc(P) = (y−y₀−α(x−x₀))/(y−y₀−β(x−x₀))
```

は実際の点の和を積へ写す。比が1となる滑らかな点はOだけなので、tc(P)はPの実際の加法位数の原始根である。

Frameの因数分解から

```text
(x−x₀)(1−tc(P))² = δ²tc(P)
x(P) = x₀ + δ² tc(P)/(1−tc(P))²         (P≠O)
```

を証明した。同じFrameからb₂,b₄,b₆,b₈、c₄=δ⁴、c₆=−δ⁶も表せる。新しい標準形へ点を移す工程は不要であり、2,3を約分しない。

これを同じ半核へ適用すると、既存の二つのモーメント和はδ⁴Tとδ⁶U+x₀δ⁴Tになる。前回のc₄,c₆補正式と今回の分母払い済みb₈補正式に代入し、上の三証明書から

```text
c₄_target = n⁴c₄_source
c₆_target = n⁶c₆_source
Δ_target = 0
```

を得る。この定理の対象は、任意標数の節点曲線へ単射に写る同じ奇数巡回核と、任意の同じ半集合である。楕円性を剰余曲線に要求しない。

## 5. 同じ既存整数標的へ戻す

滑らかな側では、前回構成した同じHの還元準同型が単射で、像は正確にp点である。素数位数から巡回表示を内部構成し、既存 `halfKernel_partition` を上の半集合の条件へ渡す。従って同じ付値環標的の剰余に、節点商の三不変量公式が適用できる。

特異な側では、前回の源との剰余一致を使う。Sourceの一次元Lについて二つの側を内部で分類済みなので、両側で

```text
v(Δ_target)<1,   v(c₄_target)=1
```

が得られる。滑らかな側でc₄が非零となることには、q≠pから得るpの剰余非零性を使う。

同じ付値環標的の一般ファイバー＝既存kernelModel、同じℚ標的の降下、同じ整数化の倍率がq≠pで単元という前段の接続を保ったまま、既存整数標的へ運ぶ。最終的に正式な

```lean
HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
  ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ))
```

を得る。

公開する一括終点は次である。

- `residual_integer_target_multiplicative_at_bad_prime`: p≠2、悪い奇素数q≠p。住所・中心・方向・Disjointの追加入力なし。
- `residual_integer_target_multiplicative_at_two`: p≥5。2上の住所・同じ節点幾何を内部供給。
- `residual_integer_target_multiplicative_at_bad_place`: p≥5、q≠p、q=2またはq∣abcを一つの入口で処理。

前回の「2では最小性のみ」という境界は、今回同じ標的の乗法的還元へ進んだ。判別式の2進深さの正確な値は、まだ結論していない。

## 6. 実際の核による小標数と37の検証

Sourceは反例を条件とする型なので、Source37のスモークだけでは非空の幾何学例の検証にならない。そこで節点曲線

```text
y²+xy=x³
```

上に、原始根u≠0,1から

```text
P_u = (u/(1−u)², u²/(1−u)³)
```

を実際の滑らかな点として構成した。tc(P_u)=uを証明するため、uが原始p乗根なら同じ点の加法位数は正確にpとなる。

同じ点の生成部分群を核とし、その実際の点数p、同じ半核座標による多項式標的の不変量を検証した。

| 係数体 | 核 | 検証した内容 |
| --- | --- | --- |
| AlgebraicClosure (ZMod 2) | 実3点核 | 原始根の存在、点の構成、同じ核の点数、同じ商のΔ=0・c₄=1 |
| AlgebraicClosure (ZMod 3) | 実5点核 | 同上。三次対称和が空になる境界も通る |
| AlgebraicClosure (ZMod 2) | 実37点核 | 同上。37乗の直接展開を要求しない |
| AlgebraicClosure (ZMod 3) | 実37点核 | 同上。三つの係数窓をすべて使用する |
| ZMod 2の加法群 | 偶数位数2 | 正の半周は反転固定点を含み、半集合の条件が破れる |

Source37では、同じ既存整数標的について2、悪い3、任意の悪い奇素数q≠37、2を含む悪い素数住所の一括入口を確認した。

## 7. 模範証明との対応・所有者

参照したのは前回取得した [節点商の模範証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.lean) で、取得内容のGit blobは `fbe8b46b385ec6f97df009c8cb22a7e62c104cc8`、1907行である。今回もキャッシュ内容のblob hashを検証した。

有限対称和・整数係数のモーメント計算を独立したLib所有者へ翻訳した。節点の標準形・点群演算・基底変換を重複実装せず、既存DkMathのFrame、tc、点群と還元準同型を使う構成にした。巡回的に選んだ半核を既存の半核と同一視せず、反転不変な和の一般定理を介して接続した。

不変量とモーメントの翻訳元を持つ二所有者にはApache-2.0、参照blob、変更内容、既存 `RegularKummer/LICENSE`・`ANTHROPIC-NOTICE` を記載した。外部証明モジュールやP2Mのコマンドはimportしていない。

本体は新規6所有者、公開26定理・5定義である。

- [FiniteInversionHalf](../../../DkMath/Lib/Algebra/FiniteInversionHalf.lean): 半集合と代表選択の独立性。
- [OddRootPairMoments](../../../DkMath/Lib/NumberTheory/OddRootPairMoments.lean): Pascal係数・対称和・整数証明書。
- [WeierstrassNodalFrame](../../../DkMath/Lib/NumberTheory/WeierstrassNodalFrame.lean): 同じFrameと節点比の座標算術。
- [WeierstrassNodalVelu](../../../DkMath/Lib/NumberTheory/WeierstrassNodalVelu.lean): 同じ半核による三不変量公式。
- [EllipticFiniteKernelNodalReduction](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelNodalReduction.lean): 同じ還元核・付値環標的との接続と両側の一括処理。
- [FreyFiniteKernelNodalReduction](../../../DkMath/FLT/FreyFiniteKernelNodalReduction.lean): 同じSourceの既存整数標的の正式な乗法的還元。

## 8. 検証と残る境界

実行した対象検証は次の通り。

```text
./lean-build.sh DkMath.FLT.FreyFiniteKernelNodalReduction
./lean-build.sh DkMathTest.Lib.NumberTheory.WeierstrassNodalVelu
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032NodalQuotientSmoke.lean
lake env lean tmp/note032-nodal-quotient/Axioms.lean
```

本体・対象テスト9定理と4定義・Source37の4定理、公理監査48公開宣言は警告なしで通過した。公理依存は `propext`、`Classical.choice`、`Quot.sound` の範囲である。Lib依存方向、docstring・昇格マーカー、import後のファイルマーカーとトラッカー、入口の静的登録、禁止構文、参照blobとライセンス、前段の数学所有者・NOTE・証拠の不変性、空白とリンクも確認した。

初期の試行では、必要な組合せ論importの不足、翻訳元の旧版書式によるlint、節点比の依存型上のsimp、剰余体での自然数castと数値リテラルの差を確認した。直接の型付き等式・明示的な分母払い・既存の環写像を使って修正した。数学的な前提を弱める変更や未証明providerの追加はしていない。

残るのは、良い素数での良還元保持、q=pでの制御、Δの正確な深さ、源の全零成分の点の商標的への輸送である。今回の判別式零・非単元性を深さ公式へ読み替えない。スキームisogeny、標的の有理捩れの算術的排除、一般hnoも残る。

フルビルド・集約ルート・全テストは今回の実行範囲に含めず、従来通りユーザー側の分担とした。

[Source37スモーク](evidence/Note032NodalQuotientSmoke.lean)、
[機械可読な検証記録](evidence/note032-nodal-quotient.json)、
[検証要約](evidence/validation-note032-nodal-quotient.txt)。
