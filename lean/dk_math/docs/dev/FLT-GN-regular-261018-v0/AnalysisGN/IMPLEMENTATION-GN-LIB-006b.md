# GN-LIB-006b — 斉次円分評価・carrier互換・単一層住所

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
25宣言を移管し、1定義・13定理を追加した。006aと合わせ、GN-LIB-006の中立化契約を対象module単位で完了した。

## 数学的carrierと所有者

[HomogeneousCyclotomic.lean](../../../../DkMath/Lib/NumberTheory/HomogeneousCyclotomic.lean)
へ、旧CFBRCの普通円分評価、shifted斉次評価、非零anchorでの脱斉次化の3宣言を移した。
これらはMathlibの整数円分多項式と斉次化だけで定義・証明されている。
旧CFBRC名を互換名として保持し、型・定義／証明本体を変えず、研究用product/GNの橋は元の所有者へ残した。
新LibからCFBRCの応用モジュールをimportしない。

Libの標準入口 `homogeneousCyclotomicEval n a b` は、旧関数を `(a-b,b)` で呼ぶ透明な定義である。
旧carrierを別物に置き換えたのではなく、同じ評価器の実座標表示を与えた。

```text
H_n(a,b) = shiftedEval n (a-b) b                 -- definitional compatibility
shiftedEval n x u = H_n(x+u,u)                  -- additive coordinate bridge
H_n(a,b) = eval ![a,b] (map(Φ_n).homogenize deg Φ_n)
```

整数係数円分多項式の元の次数を使い、係数の写像後の次数が小さくなる場合も元の定義を保持した。
教科書コメントの「常にm-1次」と読める古い説明は、実際の `deg Φ_m` に訂正した。
普通円分評価のCFBRC名とLib名のdefinitionalな一致も明示した。
体上の `H_n(a,b)=Φ_n(a/b)*b^(deg Φ_n)` は `b≠0` を保持する。
零分母でこの式を使用していない。

## 住所・支持・最初の層の移管

[HomogeneousCyclotomicAddress.lean](../../../../DkMath/Lib/NumberTheory/HomogeneousCyclotomicAddress.lean)
へ、旧GapFocusingの3定義・12定理を移した。
`primeLayerAddresses`、`layerPrimeSupport`、`FirstLayerAppearance` の型・本体を保存した。
写像則、単位anchor、rootへの還元、B11の住所分類、B12の最小性も旧名のままLib所有とした。
Zsigmondy固有の2橋だけは旧HomogeneousAddressへ残し、本文を変更していない。

[HomogeneousCyclotomicBoundary.lean](../../../../DkMath/Lib/NumberTheory/HomogeneousCyclotomicBoundary.lean)
へ、零anchor・分母消失・共通座標素数等の7境界定理を移した。
これも研究層へのimportなしで成立する一般核である。

## 実座標の新API

[HomogeneousCyclotomicPrimeAddress.lean](../../../../DkMath/Lib/NumberTheory/HomogeneousCyclotomicPrimeAddress.lean)
に、Lib名の評価器に対する8定理を固定した。

- 係数写像に関する自然性。
- anchor=1での普通評価、anchor=0での `a^φ(n)`、次数0での値1。
- q素数、正次数、q∤bのもとで `q∣H_n(a,b) ↔ ∃k,n=r*q^k`。
- q∤nのもとでの基本住所 `r=n`。
- q∣bの場合の別の枝 `q∣H_n(a,b) ↔ q∣a`。
- qが分子だけを割る場合、正次数の層に出現しないこと。

ここでrはa/bの剰余体での乗法位数である。
全余因子R_nの `r∣n` と単一層の `n=r*q^k` を区別した。
分母の非可除性、正次数、q=2の境界を暗黙に消していない。

## 教科書例

11例を所有モジュール内で確認した。

- (q,a,b)=(7,18,1)の正次数の層は `n=3*7^k`。
- n=6では7は全余因子R_6を割るが、単一層H_6を割らない。
- 位数1の(3,4,1)では最初の正次数は1、最初の非自明次数は3。
- 特性2の(2,3,1)では最初の非自明次数は2。
- qが分子だけ、分母だけ、両座標を割る場合を別々に確認。
- n=0では両座標が0でもH_0=1。正次数の境界分類をn=0へ延ばさない。
- H_3(18,1)=343で7進付値は3。基本住所の付値を1に制限しない。

## 互換性と検証

- 新Lib4本、旧所有者／入口3本、既存CFBRC.CyclotomicNorm consumerの計8ターゲット：8964 jobs、成功、警告0。
- 移管25宣言の旧型・定義／証明本体の一致を確認。旧所有者に残す15宣言も本文を保持。
- 新旧54宣言の型・公理監査成功。内訳は新所有39宣言と旧所有15宣言。
  許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 4中立所有者のDkMath依存閉包がLibだけに留まることを確認。
  ソース中のCFBRC namespaceは互換名であり、CFBRC応用層への依存ではない。
- ファイルマーカー、昇格マーカー、禁止構文不在、元資料24ファイルのSHA256を確認。
- Lib集約入口とREADMEを更新し、import登録を静的確認。

ユーザー指定によりフルビルド・DkMathTest・lake testは実行していない。
これらの結果は一般の原始素数の新規存在、付値1、FLTの降下・矛盾を主張しない。
006の一般核は完了し、次は005cの偶数完成不足D_nの精密gcdへ進む。

[所有・型・依存・ハッシュ](evidence/gn-lib-006b.json) と [検証記録](evidence/validation-gn-lib-006b.txt) に証跡を記録した。
