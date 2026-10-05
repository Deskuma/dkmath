# Report 013 — sqrt-cutoff rough moments and product waves

今回の実装は既存 rough/head/tail carrier を保ったまま、√cutoff における pair/triple moment の厳密な保存則を追加した。さらに三支持席の完全積分解、二支持席の反復素数形、三支持 cost の実際の殻内積による計数を証明した。一様な素数存在不等式は未証明である。

## 1. 局所 k≤3 恒等式

中立 namespace `DkMath.NumberTheory` の `zero_pair_triple_balance` と `excess_pair_triple_balance` は、明示的な k≤3 仮定のもとで次を証明する。

```text
(if k=0 then 1 else 0) + k + choose(k,3) = 1 + choose(k,2)
(k-1) + choose(k,3) = choose(k,2)
```

証明は `interval_cases k` と kernel 決定による四ケース。公開式は ℕ の加算と切り捨て減算のみ。k=4 では第一式の左辺8・右辺7、第二式の左辺7・右辺6となることを `four_labels_break_truncation` で検証し、仮定の実質性を残した。

組合せは [RoughMomentCombinatorics](../../../DkMath/NumberTheory/Legendre/Internal/RoughMomentCombinatorics.lean) に実装した。既存 `upperPairs` を再利用し、三支持局所 carrier 用の `upperTriples` と bounded cardinal lemma を追加した。外側の active-prime universe に card≤3 を要求していない。

## 2. 空支持席と全体保存則

`rough_empty_eq_uncovered n P` は every n/P について、

```text
R(n,P).filter (support.card=0) = paritySafeUncoveredCandidates n
```

を証明する。既存の uncovered をそのまま zero class とした。新しい uncovered notion は導入していない。

`roughPairMoment` / `roughTripleMoment` は実際の既存 R を carrier として choose(support.card,2/3) を加算する。factorization や primeFactors の評価から moment を定義していない。

`rough_moment_balance` は support.card≤3 の一般 cutoff 版、`sqrt_rough_moment_balance` は既存 `sqrtCutoff_support_card_le_three` を消費する全 n 版である。

```text
U.card + roughI + M3 = R.card + M2
```

roughI は既存 `canonicalRoughWave` の card 和。`roughWave_sum_eq_support_sum` を使って席方向へ転置し、局所四ケース恒等式を加算した。n=0 を含む。素数 anchor 仮定は保存則には不要。

## 3. tail 保存則と exact consumer

`rough_tail_moment_balance` / `sqrt_tail_moment_balance` は既存 tail の切り捨て multiplicity 和を使い、正確に

```text
tail.card + M3 = M2
```

を証明する。さらに `sqrt_covered_moment_balance` は

```text
roughCovered.card + M2 = roughI + M3
```

を証明する。Nat subtraction を早期に行わない。

`sqrt_uncovered_card_pos_iff_moment`、`sqrt_uncovered_nonempty_iff_moment` は

```text
U.card > 0  iff  roughI + M3 < R.card + M2
```

を証明する。`sqrt_uncovered_card_eq_moment_margin` によって、切り捨て差 `R+M2-(roughI+M3)` は U.card に正確に一致する。`prime_squareCell_of_sqrt_moment` は n>0 のとき既存 uncovered consumer に接続する。

これらは [ParitySafeSqrtRoughMoments](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughMoments.lean) にある。直接比較 roughI<R は依然十分だが、moment consumer は回復した pair credit を使える。

## 4. M2/M3 を実現する有限 incidence

[ParitySafeSqrtRoughProductWaves](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughProductWaves.lean) の outer universe は

```text
roughActiveLabels = actual active primes filtered by P<p
roughPairs       = upperPairs roughActiveLabels
roughTriples     = upperTriples roughActiveLabels
```

である。`roughPairIncidences` は (r,(p,q))、`roughTripleIncidences` は (r,(p,q,s)) で、r は既存 rough candidate、p<q / p<q<s は実際の active support に属する。

`roughPairIncidences_card` は全 cutoff で card=M2。`sqrt_roughTripleIncidences_card` は sqrt cutoff で card=M3。pair は既存 `card_upperPairs_eq_choose`、triple は局所 support.card≤3 と ordered triple の一意性から証明した。

## 5. 積 wave の exact fiber と regrouping

`roughPair_support_iff_product`、`roughTriple_support_iff_product` は、outer key membership の仮定を明示して support membership と product divisibility を同値にする。相異なる素数の coprimality を使用した。

```text
roughPairWave   = R.filter (p*q divides n²+r)
roughTripleWave = R.filter (p*q*s divides n²+r)
M2 = sum over roughPairs of roughPairWave.card
M3 = sum over roughTriples of roughTripleWave.card  [sqrt cutoff]
```

fiber equality は `roughPair_fiber_eq_wave` / `roughTriple_fiber_eq_wave`、和の等式は `roughPairMoment_eq_wave_sum` / `sqrt_roughTripleMoment_eq_wave_sum`。min-free、canonical-root-free である。

`roughPairWave_eq_candidate_product_filter` / triple 版によって既存 candidate product wave に実際の cutoff filter を付ける表現も証明した。奇素数 anchor では pair/triple の card を既存 `primeAnchorProductWaveCount` 以下とする floor bridge を証明し、parity と anchor 除外の補正を保持した。rough filter を無視して floor count と等しいとは主張しない。

構造的 endpoint は `prime_squareCell_of_sqrt_product_moment` を使い、上記 regrouping を通じて moment inequality を消費する。

## 6. period / occupancy bounds

L=floor√n+1 とすると `sqrt_successor_square_gt` は n<L²。各 rough support label は L 以上なので n<p*q。triple は s≥2 と pair bound から 2n<p*q*s。

既存 `card_squareWaveOffsets_eq_div_add_carry` と `squareWaveCarry_le_one` を消費して、raw pair wave.card≤2、raw triple wave.card≤1 を証明した。rough fiber は raw wave の subset なのでこれらを継承する。小さな n にも隠れた positivity 仮定はない。key membership が prime の正値性を供給し、空の universe は空のままである。

さらに候補点が odd であるため、同じ odd product wave の異なる候補は 2*p*q 以上離れる。したがって実際の候補 wave と rough pair wave では card≤1 という、raw の≤2より強い一様な bound を追加した：`candidateProductWave_card_le_one_of_anchor_lt`、`sqrt_roughPairWave_card_le_one`。

## 7. 三支持完全積分解と二支持診断

[ParitySafeSqrtRoughFactorization](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughFactorization.lean) の `sqrt_roughTriple_point_eq_product` は、rough candidate と supported p<q<s に対し

```text
n²+r = p*q*s
```

を証明した。support.card=3 の仮定を別に要求しない。三つの実際の支持と既存 card≤3 bound があるため他支持は残らない。

証明の重要な範囲確認は次のとおり。

- p*q*s divides point は product-wave membership theorem から得る。
- point>0、point≤n²+2n<L⁴、p*q*s≥L³ から相補商 c は正かつ c<L。
- c≠1 なら prime divisor u≤c≤P が存在する。
- 候補点の Coprime(2n,point) は u=2 と u divides n を排除する。
- u≤P≤n は actual active prime となり、roughness と矛盾する。

`sqrt_rough_prime_divisor_gt` は point のすべての prime divisor が P より大きいことを証明する。active universe 外の因子を無視していない。

その結果、`sqrt_roughTripleWave_card_eq_product_indicator` は card を

```text
if n²<p*q*s and p*q*s≤n²+2n then 1 else 0
```

と正確に同定する。`sqrt_roughTripleMoment_eq_product_count` は M3 を `sqrtRoughTripleProductsInShell.card` と同定した。raw multiples の carry 和から、実際の三素数積の計数へ進んだ。

二支持についても分類は成功した。相補商 c<L² が composite なら minFac(c)²≤c と rough prime lower bound が矛盾する。よって c=1 または c 自身が prime。n<p*q と shell upper endpoint から c≤n を証明し、c は actual support に戻る。support={p,q} なら

```text
point = p*q or p²*q or p*q²
```

となる。さらに p,q≤n なので pq≤n²。開いた下端により pq は排除され、`sqrt_two_support_repeated_prime` は point=p²q または pq² と証明する。分類の反例はなかった。n=13,r=6 の5²7、n=29,r=6 の7·11²を kernel 回帰に残した。

## 8. 校正 anchor

[Counts](../../../DkMathTest/NumberTheory/LegendreSqrtRoughMomentCounts.lean) は5 anchor の実際の active inventories と cutoff filters を kernel-check し、sqrt-rough carrier と moments だけを数値評価した。[Calibration](../../../DkMathTest/NumberTheory/LegendreSqrtRoughMomentCalibration.lean) が既存 carrier/wave と有限 normal forms の一致を証明し、保存式から U.card を回復する。

|n|P|roughSeats|roughI|M2|M3|U.card|direct margin (truncated)|moment margin|
|---|---|---|---|---|---|---|---|---|
|211|14|82|49|13|4|42|33|42|
|503|22|169|105|24|7|81|64|81|
|1009|31|307|188|46|14|151|119|151|
|1013|31|311|181|24|7|147|130|147|
|1019|31|312|196|28|9|135|116|135|

最後の margin=U.card は外部算術の一致だけではなく、`recovered_uncovered_checked` が `sqrt_rough_moment_balance` から証明する。pair/triple regrouping は generic theorem の各 anchor instance として kernel-check した。`checkpoints_prime_from_moments` と `shell1019_prime` は product moment consumer から prime square-cell を証明する。全 E や全 I を endpoint の証明として評価していない。

追加の quantitative regression：n=503 の key(23,31,71) は actual sqrt-rough label key、r=106 は既存 odd/coprime candidate product wave に属する。prime-anchor floor count は1。しかし point=253115=5*(23*31*71) なので actual rough triple cost は0。`false_raw_triple_rough_empty` は新しい product indicator theorem から0を導き、rough seats を直接列挙しない。この strict refinement と pair occupancy≤1 は、旧 roughI<R criterion だけでは供給されない新しい構造的 currency である。

## 9. direct-failure / moment-success の探索

[discovery script](checks/discover-013.py) で素数 anchor 2≤n≤3000 の430個を昇順に走査した（最終2999）。素数ラベルは篩で列挙し、各 shell の長さ2nと実際の odd/coprime/small-prime avoidance を有限計算した。この範囲は小さな有限 runtime に限定し、実行ログでは9.16秒だった。[discovery JSON](logs/discovery-013.json) と [log](logs/discovery-013.txt) に全430行を残した。

roughI≥roughSeats かつ moment margin>0 の素数 anchor はこの範囲で見つからなかった。したがって該当 anchor の mandatory regression は発生しない。走査結果は Python diagnostics であり全430 anchor の Lean theorem ではない。5校正 anchor の数値と構造的 prime proofs は別途 kernel-check した。

この有限探索から一様な直接比較の成立を推論しない。pair credit は表の margin を9,17,32,17,19だけ正確に増やすが、ここでは全5 anchor で旧直接比較も既に成功する。Outcome A の根拠は「旧 criterion が失敗した素数を見つけた」ことではなく、proved sharper occupancy と strict triple-product cost refinement である。

## 10. 残る一様算術 obligation と次の実装提案

正確に残る uniform target は、独立 cutoff P=√n について

```text
roughI(n,P) + sqrtRoughTripleProductsInShell(n).card
  < roughSeats(n,P).card + sum over roughPairs of roughPairWave.card
```

を算術的に証明することである。保存則自体は、この不等式を一様に供給しない。

今回の分類から、難所は singleton-support rough seats の一様制御に集中する。二支持席は p²q/pq² に限定され、三支持 cost は実際の pqs に限定された。raw wave cap を足し上げるだけでは singleton covered seats が roughSeats を埋めないことを示せない。

次の具体的な実装順序を提案する。以下は次期 theorem contracts であり今回の Lean results とは区別する。

1. `roughSingletonSeats n := R.filter (support.card=1)` を定義し、四ケース代数から
   `roughCovered.card + 2*M3 = roughSingletonSeats.card + M2`
   を証明する。exact criterion を singleton+pair credit の式へ接続する。
2. ordered pair と一ビットの反復側を使う `roughRepeatedPrimeProductsInShell` を実装する。
   point=p²q / pq² の forward classification に加え、eligible key の殻内 product が実際の rough candidate かつ support={p,q} となる converse を証明する。unique factorization を使って key→seat の重複がないことを確認してから、二支持席 card の exact product count を作る。
3. 三支持席について既存 `sqrtRoughTripleProductsInShell` と席の bijection を追加し、pair moment を「二支持反復素数積数 + 3*(三支持積数)」と同定する。moment formula を N1+N2+N3 の arithmetic provider に落とす。
4. 一つの明確な次期 uniform theorem contract は、prime n>1013、P=√n に対して
   `roughSingletonSeats.card + M2 < R.card + 2*sqrtRoughTripleProductsInShell.card`
   を証明すること。閾値1013は比較対象を固定するための提案であり、今回の有限表から正当化されない。まず1の exact consumer を実装し、次に singleton の shell cofactor/carry の一様 bound を提供する。これを仮定として隠して最終 prime theorem を無条件化しない。
5. 必要になった場合のみ、old far-triple machinery への cubic-gate/canonical-ownership adapter を実装する。三支持積の cofactor=1 は既に証明できるが、旧 residual ledger との membership equality は別の証明対象である。名前の類似だけで旧容量を流用しない。

source audit と旧 carrier の境界は [source inventory](source-inventory-013.md)、途中の durable checkpoints は [findings](findings-013.md)、ビルドと全宣言の公理監査は [validation](validation-013.md) に記録する。Legendre conjecture、一様 T=1、PNT/RH、解析的篩推定、FLT/ABC consequences は今回の成果に含まれない。

Outcome A — ROUGH MOMENT BALANCE ADDS QUANTITATIVE LEVERAGE
