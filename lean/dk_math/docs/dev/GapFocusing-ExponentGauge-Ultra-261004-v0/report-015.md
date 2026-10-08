# Instruction 015 — quotient routing と補正付き保存則

指定文書を実装仕様として、014 の既存 carrier・support・census を再利用した。新規 production は 3 モジュールで、Legendre facade に export した。元の reduced quotient carrier に small-prime rejection が含まれるため、指定文書の予想した補正なしの保存則は偽である。補正項を明示した保存則、全 owner の正常形、多重度、Cross 上界、条件付き endpoint consumer を Lean で証明した。

追加の有限な成果として、3・5・7 による rejection 下界から指定 6 アンカーの structural budget を満たし、新しい `n=1031` の square-cell prime endpoint と `U≥18` を kernel で証明した。無条件の Legendre、uniform T=1、解析的素数計数は証明していない。

## 1. 使用した exact owner-p carrier

`sqrtRoughQuotientFiber n p` は **既存の `paritySafeReducedQuotientInterval n p` の abbrev** である。

```text
Q(n,p) = { q in Ioc(n²/p, (n²+2n)/p) | Coprime(2n,q) }.
```

`p∈roughActiveLabels n (sqrt n)` のもとで `mem_sqrtRoughQuotientFiber` は
`n<q ∧ n²/p<q ∧ q≤(n²+2n)/p ∧ Coprime(2n,q)` と membership が同値であることを証明する。全整数の Ioc に拡大していない。

座標 `r=pq−n²` について `sqrt_quotient_seat_packet` は SquareOffset、point の coprimality、`n²+r=pq`、実 support の owner p、商の逆写像を供給する。roughness は自動ではない。

## 2. CrossFiber は正確な prime part か

はい。`sqrt_cross_fiber_eq_quotient_prime_filter` により

```text
CrossFiber(n,p) = Q(n,p).filter Nat.Prime.
```

商はすべて n より大きいため、追加の `n<q` filter は不要である。Cross の定義を複製していない。`sqrt_quotient_prime_composite_partition` は disjoint union と加法的 card identity を証明する。商は 0、1 のいずれでもない。

## 3. 補集合に現れるクラス

raw CompositeFiber は二つに分かれる。

- `sqrtRoughRoutedFiber` の合成数部分：再構成 seat が既存の sqrt-rough carrier に属する。
- `sqrtRoughRejectedFiber`：商に `u≤sqrt n` の素因子 u があるため rough census の外に出る。

`sqrt_quotient_seat_rough_iff` と `sqrt_quotient_rejected_iff_small_prime` がこの同値を証明する。Rejected は必ず合成数で、routed 部分と disjoint。追加の prime-q≤n クラス、0/1 クラス、endpoint 補正クラスはない。

最小反例は `n=11,p=5,q=27`。`121<135=5·27≤143`、`Coprime(22,27)`、`5>sqrt 11=3` だが、商は 3 を因子に持つ。`rejected_eleven` と `uncorrected_conservation_eleven_false` が carrier membership と補正なしの大域恒等式の否定を kernel で証明する。`rejected_eleven_is_minimal` は n<11 の不存在も有限チェックから証明する。

## 4. Cube / Repeated / Triple の owner ごとの正常形

|point|owner|quotient|
|---|---|---|
|p³|p|p²|
|p²a|p|pa|
|p²a|a|p²|
|pa²|p|a²|
|pa²|a|pa|
|pab（相異なる）|p|ab|
|pab|a|pb|
|pab|b|pa|

`sqrt_three_factor_owner_quotients` は重複を許す 3 素因子の共通 packet。cube/repeated/triple の専用正常形は各 key packet から導いた。全 complement は composite、rough、かつ n より大きい。

`sqrt_composite_quotient_normal_forms` は任意の owner p について、`q=p²`、`q=pa` または `a²`（a≠p）、`q=ab`（a,b,p は相異なる）を尽くす。`sqrt_routed_composite_factor_packet` は、その素因子が実際の active support に入り、sqrt n より大きく n 以下であることを証明する。rough composite の prime factor に external label はない。

## 5. 正確な owner 多重度

owner は実 support の任意の素数であり、最小 label に限定されない。`sqrt_quotient_owners_eq_support` が quotient witness を持つ owner 集合と既存の `paritySafeActiveSupport` の一致を証明する。同一 owner 内の quotient は乗法の cancellation で一意。

|型|商を持つ owner 数|証明|
|---|---:|---|
|Cube|1|`sqrt_cube_quotient_owner_multiplicity`|
|Repeated|2|`sqrt_repeated_quotient_owner_multiplicity`|
|Triple|3|`sqrt_triple_quotient_owner_multiplicity`|

自然数アンカー全体での最小 multiowner 反例は `n=8,point=75=3·5²`：owner3 の商25、owner5 の商15。prime anchor に限定した最小例は `n=13,point=175=5²·7`：商35と25。さらに n=19 の triple385 の商は77、55、35。witness と最小性の有限検証を [regression](../../../DkMathTest/NumberTheory/LegendreSqrtQuotientRegression.lean) に保存した。

## 6. q>n を残すと何が変わるか

**何も変わらない。** p≤n かつ pq>n² なので q>n が必須である。
`sqrt_quotient_below_empty_above_eq` は below-or-equal slice が空、above slice が全 Q であることを証明する。`sqrt_quotient_owners_above_eq_support` は above-n owner 多重度も実 support と同じことを証明する。

指定文書 Phase13 の「complement に n 以下のものがあり、多重度が可変になる」という可能性は、この carrier のもとでは排除される。`largeComplementCount` は導入していない。

## 7. 証明した大域保存則と既存通貨との関係

以下では Qtotal を owner-p Q.card の和、Jexact を RejectedFiber.card の和とする。これらはレポート内の略記であり、production に新しい incidence ledger を作っていない。

```text
Qtotal = Cross + Cube + 2·Repeated + 3·Triple + Jexact.
RoutedTotal = roughI = Cube + Cross + 2·Repeated + 3·Triple.
CompositeTotal = Cube + 2·Repeated + 3·Triple + Jexact.
Cross + CompositeTotal = Qtotal.
```

対応する定理は `sqrt_quotient_conservation`、`sqrt_routed_quotient_sum_eq_rough_incidence`、`sqrt_composite_sum_corrected`、`sqrt_cross_add_composite_eq_total`。旧 M2=Repeated+3Triple、M3=Triple と矛盾しない。

raw Qtotal は roughI と同じではなく、**roughI+Jexact** である。`sqrt_cross_eq_total_sub_routing` は加法的保存則を先に証明した後に、正確な Nat subtraction residual が Cross であることを証明する。

奇素数アンカーでは `primeAnchor_quotient_fiber_card_eq_floor` により owner ごとに

```text
Q.card = Δodd(n²,n²+2n,p) − Δodd(n²,n²+2n,n·p),
Δodd(A,B,d) = (B/d−A/d) − (B/(2d)−A/(2d)).
```

旧 `primeAnchorProductWaveCount` の endpoint carry、parity、anchor exclusion をそのまま保持する。rough subcarrier の card をこの floor と同一視していない。

## 8. 得られた Cross 上界

任意の `J≤Jexact` に対し、Nat-safe な主定理は

```text
Cross + Cube + 2·Repeated + 3·Triple + J ≤ Qtotal.
```

したがって

```text
Cross ≤ Qtotal − (Cube + 2·Repeated + 3·Triple + J).
```

`sqrt_cross_bound_of_rejected_lower` と `sqrt_cross_card_le_capacity_sub_routing` がこれを証明する。J=0 でも既存の積型 mass が正なら旧 summed floor capacity より小さいが、指定 6 アンカーでは census demand に足りない。

有限な素数集合 S のすべての元が sqrt n 以下なら、商が S のどれかで割れる部分の card は rejection 下界になる。`sqrt_rejected_card_lower_of_small_primes` が一般形を証明し、校正では S={3,5,7} を用いる。

全 6 点の exact conservation：

| n | cross | total | cube_mass | repeat_mass | triple_mass | rejected | residual |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 211 | 35 | 129 | 0 | 2 | 12 | 80 | 35 |
| 503 | 78 | 331 | 0 | 6 | 21 | 226 | 78 |
| 1009 | 138 | 627 | 0 | 8 | 42 | 439 | 138 |
| 1013 | 154 | 642 | 0 | 6 | 21 | 461 | 154 |
| 1019 | 167 | 653 | 0 | 2 | 27 | 457 | 167 |
| 1021 | 142 | 647 | 0 | 2 | 57 | 446 | 142 |

`residual=total−cube_mass−repeat_mass−triple_mass−rejected`。
[calibration](../../../DkMathTest/NumberTheory/LegendreSqrtQuotientCalibration.lean) の `quotient_full_calibration` がすべて production carrier の値であることを証明する。Exact Cross/repeated/triple は 014 の checked census から回収し、全 external q の素数判定を再実行していない。

|n|J3（3,5,7）|J=0 の Cross 上界|J3 使用の Cross 上界|J=0 の covered−R deficit|必要な rejection 下界|
|---:|---:|---:|---:|---:|---:|
|211|71|115|44|38|39|
|503|191|304|113|145|146|
|1009|334|577|243|288|289|
|1013|352|615|263|314|315|
|1019|358|624|266|322|323|
|1021|352|588|236|297|298|

deficit は `Qtotal−Repeated−2Triple−R`。strict inequality に必要な J は deficit+1。J3 は全点でその要求を超える。

owner の有限 range は `sqrt n<p≤2sqrt n` と `2sqrt n<p≤n` の 2 群。`sqrt_quotient_sum_split_owner_range` は任意の Nat-valued contribution の exact split、`primeAnchor_quotient_range_eq_floor` は各群の exact floor sum を証明する。6 点の near/far total は順に 33/96、95/236、148/479、152/490、151/502、153/494。[全 owner 出力](evidence/MANIFEST.md#log-49301e24aaa80b1b) を保存した。この regrouping 自体で容量が減るとは主張しない。

追加の初等制限として `sqrt_cross_fiber_card_le_odd_span` は

```text
CrossFiber.card ≤ floor((U+1)/2) − floor((L+1)/2),
L=max(n,n²/p), U=(n²+2n)/p
```

を証明する。奇素数の `q↦q/2` は injective で、対応する Ico に入る。旧 parity/anchor-corrected floor capacity はさらに coprimality correction を持つため、odd-span bound が常にそれより強いとは主張しない。

## 9. 新しいアンカーと有限 diagnostic の結果

`prime_squareCell_of_quotient_routing_budget` は

```text
J≤Jexact,
Qtotal < R + Repeated + 2·Triple + J
```

から square-cell prime を導く。指定 6 点は **Qtotal<R+J3** というさらに強い数値予算を kernel で満たす。これらの endpoint proof は Cross card、全 E、全 I の評価を使わない。

新アンカー 1031 では、verified active inventory を 1021 から境界更新して再利用し、rough R.card=316、exact odd floor total=661、3/5/7 rejection count=363 を kernel で確認した。`quotient1031_structural_endpoint` は `661<316+363` から prime endpoint を得る。`quotient1031_uncovered_lower` は **U≥18** を conservation と census から導き、U 自体を列挙しない。

429 個の奇素数アンカー `3≤n≤3000` を同じ範囲の 014 と比較した。所有者ごとの quotient interval、reduced condition、素因子による routed/rejected 分類を独立に計算し、全 rows を [JSON](evidence/MANIFEST.md#log-49301e24aaa80b1b)、全 aggregate rows を [text](evidence/MANIFEST.md#log-8b48cbe6d2909b6e) に保存した。有限試行割り算の範囲はこの診断の shell と quotient に十分であり、asymptotics は推論していない。

指定 6 点の Cross/Total は約 27.13%、23.56%、22.01%、23.99%、25.57%、21.95%。Repeated share は約 1.55%、1.81%、1.28%、0.93%、0.31%、0.31%；Triple share は 9.30%、6.34%、6.70%、3.27%、4.13%、8.81%。Repeated/Triple だけでは total の削減が足りず、Rejected share の約62–72%が主要な補正になる。全範囲の largest owner residual は13（2083、2477、2657、2753、2939）。

J=0 の budget が通る範囲内アンカーは 3,5,7,11,13,17,19,23,31,37,41 の 11 点のみ。小素数を cutoff 以下に限定した J3 budget は 410/429 点で通る。最初の失敗は2099。2969 では R807、total1977、Repeated1、Triple43 なので要求 J≥1084 に対し J3=1070 で、strict budget に14足りない。診断した追加集合 {3,5,7,11} は残る19点すべてで budget を満たす。[次基底 probe](evidence/MANIFEST.md#log-b6f09ce8ccd07a15) は **diagnostic** であり、その19個の kernel endpoint は今回実装していない。

## 10. 残る external-prime arithmetic と次の実装提案

分類上は external q の primality を持つ部分が Cross だけである。route や owner 多重度に未証明の bridge は残っていない。一方、全 n で census demand を満たすための素数窓容量または composite/rejected mass の下界は未証明である。有限 identity はこの uniform inequality を供給しない。

次の具体的な theorem contract を提案する。対象は `n.Prime ∧ 7≤Nat.sqrt n` のアンカーとし、各 n に対して有限小素数集合 S を選び、

```text
J_S(n) = sum over rough owners p
           card {q in Q(n,p) | exists u in S, u divides q}.

hypothesis: every u in S is prime and u≤sqrt n.
provider target:
  sum_p primeAnchorProductWaveCount(n,p)
    < R(n) + Repeated(n) + 2·Triple(n) + J_S(n).
```

`J_S≤Jexact` とこの budget の consumer は今回すでに Lean にある。残る仕事は、external prime candidates がこの要求を超えて占有できないことを示す **実際の数値不等式** である。S を固定すると全 n に通用するとは限らず、その選択と不等式は証明対象である。

次の bounded implementation は以下の順序が自然である。

1. quotient の S={3,5,7} rejection を既存の `candidateAvoidThree` に bijectively transport し、owner ごとの exact lower count を `primeAnchorProductWaveCount−primeAnchorAvoidThreeCount` に落とす。後者の exact inclusion-exclusion floor API はすでに存在する。今回の kernel 校正は finite quotient enumeration であり、この新しい bridge の証明は次の実装で行う。
2. S={3,5,7,11} の 4-exclusion inclusion-exclusion を、加法的 overlap credit を保った Nat-safe identity として実装する。まず 2099・2969 の診断値を kernel 化し、19 failure のうち新しい endpoint を追加する。
3. near/far owner ranges ごとに carry と small-divisor exclusions を exact に regroup し、range ごとの primality-aware residual budget を調べる。単なる sum split を量的改善と混同しない。
4. cutoff を有限に拡張した J_S でも deficit が残る場合、external prime q の短区間 occupancy について別の初等 provider を特定する。uniform theorem は有限 scan から外挿しない。

## 実装・検証成果物

production は [CrossQuotient](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtCrossQuotient.lean)、[CompositeRouting](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtCompositeRouting.lean)、[QuotientConservation](../../../DkMath/NumberTheory/Legendre/ParitySafeSqrtQuotientConservation.lean)。既存 support/census/moment/uncovered 定義は変更していない。全 Lean ヘッダーと import 直後の `#print "file: ..."` marker を統一した。

[Source inventory](source-inventory-015.md)・[Findings](findings-015.md)・[Validation](validation-015.md)・[declaration manifest](evidence/MANIFEST.md#log-a3b84fc5ea3bdc4c)。focused/facade/root build、全新規 public 宣言の axiom check、禁則語・header・whitespace・artifact check の範囲と結果は Validation に記録した。

判定は、raw carrier に genuine な additional quotient class が存在することによる C である。補正後の分解と summation は完成し、有限な structural gain と新 endpoint も得られたが、Rejected を落とした当初の保存則には戻せない。

Outcome C — COMPOSITE ROUTING REQUIRES A CORRECTED DECOMPOSITION
