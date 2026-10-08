# Instruction 007 — incidence 上限と uncovered deficit

被覆を仮定しない構造上限を実装し、N=20 の指定幅20,10,5,4,3,2,1で被覆失敗を証明した。最小幅は1、具体的な殻は21。20殻では incidence の上限425から未被覆候補65個以上、殻21では上限7から5個以上を得る。殻21の素数存在も既存 consumer で導いた。一様な N に関する結果ではない。

[Production](../../../DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean) · [Regression](../../../DkMathTest/NumberTheory/LegendreIncidenceUpper.lean) · [Source inventory](source-inventory-007.md) · [Findings](findings-007.md) · [Validation](validation-007.md)

既存の台帳 I+U=A+E を使用する。ここで I は incidence、U は未被覆候補数、A は候補数、E は support excess。ブロックの添字は006と同じ successor 規約、殻 N+i+1（i<T）である。

## 1. 最も強い採用済みの、一波に対する独立上限は何か

L=⌊n²/q⌋、H=⌊(n²+2n)/q⌋ とする。奇数 quotient の端点個数を

```text
O(n,q) = ⌊(H+1)/2⌋ − ⌊(L+1)/2⌋
Δ_d    = (⌊H/d⌋−⌊L/d⌋) − (⌊H/(2d)⌋−⌊L/(2d)⌋)
```

と置く。d が n の奇素因数なら、reduced quotient は d の倍数を含まない。従って `card ≤ O−Δ_d`。全ての実際の奇素因数に対する最小値（空集合なら O）を Q(n,q) とする。採用した上限は

```text
W(n,q) = min(shellFrequencyCap(2q,2n), Q(n,q)).
```

`paritySafeActiveWave_card_le_waveUpper` は active q に対してこれを証明する。床関数は区間内の「一つの除外素数の倍数」を数えるもので、実際の incidence を表引きしていない。既存の完全 Möbius 式は正確な cardinality を与えるが、今回は一素数だけを除く部分上限として利用した。全ての可能な上限の最適性を主張してはいない。

## 2. 2q spacing は quotient 上限を改善するか

偶奇を無視した長さ約2n/qに対して、2q spacing は約n/qの packing 上限を与える。`paritySafeActiveWave_card_le_spacing` は実際の波を `(r−1)/(2q)` で有限 range に単射化する。

ただし、奇数端点を既に正確に保った上限より強くなるとは主張しない。主ブロックでは uniform spacing602、奇数端点510で、後者が強い。両者の minimum を保持し、さらに reduced-residue 除外で425へ下げた。n=18,q=5 の波 `{1,11,31}` は正確な2q隣接を反証する。証明に使うのは2q整除と最低間隔だけである。

## 3. 殻 incidence の上限は何か

```text
B(n) = ∑ q∈squareAnchorOddActivePrimes n, W(n,q)
I(n) ≤ B(n).
```

`paritySafeIncidenceCount_le_upper`。active 集合の prime、q≤n、q≠2、q∤n をそのまま使用する。数値回帰では同じ集合を proven equality により有限 prime filter に直す。解析的な素数個数評価は導入していない。

独立に seat 側も監査し、`activeSupport n r ⊆ (n²+r).primeFactors` とその総和上限を証明した。殻21では全ての点素因数を数えると17、波側上限は7である。大きい素因数まで数える seat 上限はこの例では弱い。persistent support の `q∣4r+1` を fresh support に適用してはいない。

## 4. ブロック上限は何か

```text
B(N,T) = ∑ i<T, B(N+i+1)
∑ i<T I(N+i+1) ≤ B(N,T).
```

`block_incidenceCount_le_upper` に被覆仮定はない。candidate/support 側と reduced quotient 側のブロック総和を切り替える等式も追加した。`not_block_fullyCovered_of_upper_lt_candidate_add_freshBound` は006の既存 consumer にこの上限を渡す。

## 5. N=20,T=20 は I=418 の評価なしに回復できたか

できた。構造的な床関数・素因数除外の和として B=425、既存候補 A=490、条件付き temporal charge b=38。425<490+38=528、slack は103。実際の incidence=418 はこの証明の依存先ではない。

更に425<490なので、被覆仮定なしに excess≥0 だけから U≥65 を得る。条件付き38を無条件 excess 下限として使っていない。

既存の奇数端点上限510でも510<528なので temporal38を用いた主ブロック回復は可能だった。新しい除外の成果は、上限を更に85下げ、temporal 条件なしの定量的不足を与えた点にある。

## 6. 証明した最小幅は何か

| N | T | 構造上限 B | 候補 A | 無条件 U 下限 |
| --- | --- | --- | --- | --- |
| 20 | 20 | 425 | 490 | 65 |
| 20 | 10 | 162 | 200 | 38 |
| 20 | 5 | 73 | 90 | 17 |
| 20 | 4 | 55 | 70 | 15 |
| 20 | 3 | 45 | 54 | 9 |
| 20 | 2 | 24 | 32 | 8 |
| 20 | 1 | 7 | 12 | 5 |

全幅について被覆失敗・正の未被覆総数・ブロック内の square-cell prime を kernel checked regression にした。最小の正の幅は1、具体的な殻21で、`∃p, Prime p ∧ 441<p ∧ p<484`。

既存の奇数端点上限だけでも殻21では10<12。したがってこの一殻の成功を一素数除外に固有の新発見とはしない。新上限はそこでの deficit を2から5へ強める。

## 7. 正の uncovered 下限が得られるか

一般定理は Nat のまま

```text
e ≤ E(n) → A(n)+e−B(n) ≤ U(n)
e ≤ ∑ E → ∑ A+e−∑ B ≤ ∑ U.
```

`paritySafeUncovered_card_ge_candidate_add_excess_sub_upper` とブロック版である。既存の二つの正確な partition/balance 等式と I≤B を組み合わせるため、切り捨て減算の問題はない。独立に正当化された e のみを受け取る。今回の無条件数値結果は全て e=0。

殻・ブロックの正の deficit から既存 nonempty→prime consumer を使う二つの generic theorem も facade に公開した。

## 8. 残る slack を支配する波・剰余類は何か

主ブロックの q≤7 の cap 総和は261/425。低 q が総容量を支配する。一方、新上限と実際の incidence の差は425−418=7のみで、次の六波の過大評価が合計7を占める（診断としてのみ実際の波を評価）。

| n | q | W | 実際の波 cardinality |
| --- | --- | --- | --- |
| 21 | 5 | 3 | 2 |
| 30 | 11 | 2 | 1 |
| 35 | 3 | 10 | 8 |
| 39 | 7 | 3 | 2 |
| 39 | 11 | 3 | 2 |
| 39 | 17 | 1 | 0 |

一つの奇素因数を除いても、別の奇素因数が割る quotient が残ることが原因である。たとえば n=21,q=5 の上限3は実際の2と等しくない。最良一素数除外を「正確な cardinality」とする式は false。

失敗する上限候補も保持した。主ブロックの uniform spacing602は528を上回る。殻29の新上限31は候補28を上回り、e=0 の十分条件は失敗する。後者は全Nへの拡張の障害であって、素数不存在の主張ではない。

## 9. 一様 T=1 の Legendre 目標からどれだけ遠いか

今回得たのは明示的な有限ブロックの階層1・2である。全Nの固定幅結果、uniform T=2、uniform T=1 は得ていない。殻29では既に B<A の一様化が破れるため、幅1を一例で達成したことは Legendre への一様な provider にはならない。

## 次なる展開の提案（今回未実装）

第一候補は二つの奇素因数の union 除外である。相異なる奇素数 d,e が n を割るとき、次を Nat-safe に証明する。

```text
reducedQuotient.card ≤ (O + Δ_(d*e)) − (Δ_d + Δ_e).
```

二つの除外集合の intersection が d*e の倍数であることを使う。既存の公開した odd-multiple counting lemma と union cardinality を再利用できる。各ペアの cap と今回の cap の minimum を取る。主ブロックの残差7を説明する二素数除外を直接扱えるが、これだけで全Nの Legendre 条件を満たすとは限らない。

第二候補は、上限が候補を超える殻に対する独立の excess certificate。殻29では B=31,A=28なので `4 ≤ paritySafeSupportExcess 29` があれば U≥1になる。具体的な候補は r=14 の点855=3²·5·19と、r=56 の点897=3·13·23。両座席の三つの admissible support prime を証明し、各座席が excess を2ずつ支払うことを有限 sum に埋め込む。これは次段階の局所証明案であり、今回その excess theorem を実装したとは報告しない。

一様化の本当の次目標は、各殻について構造上限 B と独立 excess 下限 e を与え、A+e>B を保証する provider である。上限を実際の I に近づけることと、正の未被覆を保証することは別の定理義務として残る。

Outcome A — BLOCK WIDTH SHRINKS
