# findings-016 — seventh-power permutation primes

2026-10-14。Outcome A。

## 既存 API と新規性

actual `centeredSevenSextic`、既存整数版 `centered_seventh_power_difference`、same-r centered equivalence、gate 013 support consumer、gate 015 coefficient support bridge、full-sieve witness fields を読んだ。既存整数版は64*((x+D)^7-x^7)という別の座標表示だったため、今回の q±D の表示を新しい cast identity として追加した。既存 source/index の permutation 検索で同じ API は見つからず、新規名の実ソース検索でも重複なし。索引は過去 snapshot の補助検索であり、証明の根拠ではない。

Mathlib `Nat.Coprime.pow_left_bijective` は群の Nat.card と指数が互いに素なら冪写像が全単射になる。`ZMod.card_units` は素数 ℓ に対し単元群の位数をℓ−1とする。この2定理を用い、単元の7乗単射性を得て、零の場合を別に扱って全 ZMod ℓ 上の単射性を証明した。有限個の素数に対する decide による主定理ではない。

## 数学的推論と成立条件

任意 CommRing R と自然数 D,q の cast に対して (q+D)^7−(q−D)^7=2D*F(D,q) を ring で証明した。減算は常に target ring の減算であり、自然数の切り捨て減算ではない。

ℓ 素数、ℓ≠2、Nat.Coprime 7 (ℓ−1)、ℓ∤D を仮定する。F の cast が零なら恒等式から q+D と q−D の7乗が等しい。単射性で基底が等しくなり、2D=0。ℓ≠2 により2の cast は非零、ℓ∤D によりDも非零なので矛盾する。D で除算していない。ring だけで非零性を主張していない。

receiver では D=7^27*r^49。ℓ≠7 を別途明示して固定因子7が unit であることを保証し、ℓ∤r からℓ∤Dを導いた。補因子へのℓ整除から448*(M/r)^49は零となる。同じ r と実際の自然数商を保持して既存 centered equivalence の必要方向を使い、両 receiver を排除した。追加の r∣M guard はこの consumer に必要ない。

任意素数に対する generic polynomial theorem の条件は sufficient criterion である。ℓ=7 も polynomial criterion を満たすが、receiver gap には固定因子7があるため、この consumer の ℓ≠7 は意味を持つ。

## Lean で試した例と反例

- ℓ=13: 任意自然数 D,q の旧非零性を新しい structural theorem の特殊化として回復。旧 production は編集していない。
- ℓ=11: 任意 D,q の unit-gap 非零性、ZMod11 の7乗単射性、M=11,r=1 の両 receiver 排除を確認。
- optional schema: gate 015 bridge を再利用し、全 c≤343,n>0 の c*ℓ^n に対する conditional full-sieve 排除を形式化。法11と法13への任意 coefficient/positive exponent の特殊化を test に保存。
- ℓ=29: Nat.Prime 29、29≠2、29∤1、29∣F(1,5)、Nat.Coprime 7 28 の不成立を単一 countermodel として kernel 検証。無条件の奇素数一般化は偽である。
- ℓ=2: unit D=1 に対し F(1,1)=64 が偶数。奇数条件を外すと非零性は偽。
- ℓ=7: polynomial criterion は通るが actual gap 7^27*1^49 を割ることを diagnostic として確認。

指示書の BigInt precheck は証明の仮定にしていない。今回 Python 数学 precheck は実行せず、各数値主張は Lean decide で確認した。modular zero は自然数 exact receiver の存在を意味しない。

## 検証経過

初回 calibration は零分岐の等式向きの不一致で exit 1。第2回も simp の向きの問題で exit 1。零の場合に y=0 を明示して反転するよう修正し、不要な instance binding style 警告も除去した。修正後 calibration は exit 0。数学的仮定や主張は変更していない。

focused build は exit 0 (9090 jobs)、最終 test は exit 0。全5公開宣言と3 named test 宣言を公理監査した。ring identity は propext、Quot.sound、それ以外は propext、Classical.choice、Quot.sound のみ。sorryAx なし。

## 次の研究優先順位と境界

この structural criterion で個別法13の機構を説明でき、さらに同じ support consumer の素数族への十分条件が得られた。今後は追加の modular family の列挙より、gate 005 の同一 packet に関する source/carrier/real-pair/chart bridge を優先するのが有益と判断する。今回その bridge は着手していない。

証明は special abstract cores の full-sieve 排除までである。実際の internalDepthFourSeventhCore が条件を満たすこと、packet の存在・不存在、exact endpoint の構成、FLT7 は証明していない。gate 017 に進まず、016 で終了する。
