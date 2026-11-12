# GN-LIB-006a — 位数・円分根・LTEの中立化

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
006を006a（今回）と006b（斉次carrierの互換移管）に分けた。
今回は25宣言の移管と全余因子の5定理を実装し、対象モジュール単位で検証した。
**GN-LIB-006全体は継続中**である。

## 所有者の分離

| 新Lib所有者 | 移管したもの | 旧入口 |
| --- | --- | --- |
| [PrimeRatioOrder](../../../../DkMath/Lib/NumberTheory/PrimeRatioOrder.lean) | 比・位数の2定義、7定理 | GapFocusing.PrimeOrder |
| [CyclotomicAddress](../../../../DkMath/Lib/NumberTheory/CyclotomicAddress.lean) | 円分根と通常評価の住所8定理 | GapFocusing.CyclotomicAddress |
| [CyclotomicLayerValuation](../../../../DkMath/Lib/NumberTheory/CyclotomicLayerValuation.lean) | 基本層の付値・奇素数LTE・2進LTE等8定理 | GapFocusing.LayerValuation |

移管は歴史的namespace `DkMath.NumberTheory.GapFocusing` のまま行った。
全修飾名・公開型・証明／定義本体を保存し、旧定義を重複して置いていない。
各docstringに由来と `[DkMath.Lib]` を付け、旧importから同じ宣言を使えるようにした。
PrimeOrderのZsigmondy固有の4定理は旧所有者に残し、本文は変更していない。
新しい有限体比の核はZsigmondyをimportしない。
4つの新Lib所有者のDkMath依存閉包はLib内に留まる。

## 全余因子R_nの素数住所

新設した [PowerDifferenceCofactorPrimeAddress](../../../../DkMath/Lib/NumberTheory/PowerDifferenceCofactorPrimeAddress.lean)
に、namespace `DkMath.Lib.NumberTheory` の5定理を固定した。
qを素数、bをqで割れない座標、rをa/bの剰余体での乗法位数とする。

1. `r=1 ↔ q ∣ a-b`。これがgapを約分できない枝である。
2. qがgapを割らない場合、整数上で `q ∣ R_n ↔ r ∣ n`。
3. `1<r` からgap非可除性を得て、同じ全余因子の出現条件を供給する。
4. 自然数座標の有限和を整数へcastし、同じ条件を座標の大小制限なしで得る。
5. 自然数の位数1の枝では `q ∣ R_n ↔ q ∣ n`。

位数1の枝は、剰余体でa=bとなるのでR_nが `n*b^(n-1)` に一致することから証明した。
全余因子のこれらの定理はn=0も含む。
qが分子を割る場合の位数0と、分母を割る場合の比の退化を暗黙に除去していない。
公開型で必要な非可除条件を保った。

## 全余因子と単一円分層の違い

通常の円分評価の住所は、正次数nについて
`q ∣ Φ_n(a) ↔ ∃k, n=orderOf(a mod q)*q^k` である。
これを全余因子の `r∣n` と同じ条件にはしていない。
一般の斉次評価で同じ単一層条件を供給する既存B11/B12は、
CFBRCの `cyclotomicShiftedEval` を使うため今回のLibへ逆importしていない。
そのcarrierと旧APIを変更せず、consumerのビルドと型・公理監査で互換性を確認した。

006bでは中立な斉次円分評価を設計し、旧評価器とのdefinitionalな互換性または明示的な等値を先に固定する。
その後で写像・剰余体rootとの同値・B11/B12と位数1の最初の非自明層を移す。
新carrierを別名で定義しただけで移管済みとは扱わない。

## LTEで保持した条件

| 結果 | 明示した条件／補正 |
| --- | --- |
| 奇素数での次数r*q^k | q素数・奇数、b<a、r≠0、q∤a、q∣a^r-b^r。付値は基本差の付値+k |
| 2進での次数r*2^(k+1) | b<a、r≠0、a奇数、差が偶数。`v₂(a^r+b^r)+v₂(a^r-b^r)+k` |
| 基本住所の通常円分評価 | 正次数、位数一致、冪差非零。基本差の付値を全て保持 |
| 単位anchorの2冪層 | 最初の層ではa+1の付値を保持し、その後の層の付値1とは区別 |

基本住所の付値を1に制限していない。
`R_3(18,1)=343=7³` の7進付値3、7進の次数膨張、2進の和の補正を教科書例にした。

## 検証結果

所有モジュール内の13例は、
`7∣R_n(18,1) ↔ 3∣n`、位数1の奇素数3の枝、特性2の枝、
付値3、奇素数LTE、2進LTE、分子／分母の退化、次数0を含む。

- 新Lib4本、旧入口3本、既存HomogeneousAddressの計8ターゲット：8958 jobs、成功、警告0。
- 移管25宣言、新5定理、旧primitive橋4定理、斉次consumer2定理の計36宣言：型照会・公理監査成功。
  許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 移管25宣言の旧型と証明／定義本体の一致、残すcarrierの本文保持、下位import閉包を確認。
- 元資料24ファイルのSHA256、ファイルマーカーと昇格説明、禁止構文不在を確認。
- Lib集約入口とREADMEを更新。集約入口は静的確認に限る。

ユーザー指定によりフルビルド・DkMathTest・lake testは実行していない。
[所有・型・ハッシュ・依存](evidence/gn-lib-006a.json) と [検証記録](evidence/validation-gn-lib-006a.txt) に証跡を記録した。
次は006bであり、006全体や偶数不足の精密gcd（005c）を完了とはしていない。
