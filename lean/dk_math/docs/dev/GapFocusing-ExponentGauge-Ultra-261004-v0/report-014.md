# Instruction014 実装レポート

singleton cofactor の予想された分類を証明し、既存 sqrt-rough carrier を uncovered、素数 cube、cross-semiprime、二支持 repeated product、三支持 distinct product に完全分解した。分類・全単射・census は全自然数アンカーについての定理であり、均一な uncovered 存在を主張しない。

実装は `ParitySafeSqrtRoughFactorization` に商補題と singleton 分類を追加し、`ParitySafeSqrtRoughStrata`、`ParitySafeSqrtRoughSingleton`、`ParitySafeSqrtRoughCensus` を導入した。Legendre facade が Census を export する。既存の rough、actual active support、uncovered、moment の各定義を保持した。

## 指定された 10 問への回答

1. **支持数による層別化**：`roughZeroSeats`, `roughSingletonSeats`, `roughDoubleSeats`, `roughTripleSeats` は既存 R の support.card=0,1,2,3 フィルタ。`rough_strata_pairwise_disjoint` と `rough_strata_union` が互いの disjointness と全分割を与える。zero は既存 U と等しい。

   `rough_stratum_sum` から `R=N0+N1+N2+N3`, `roughI=N1+2N2+3N3`, `M2=N2+3N3`, `M3=N3` を導出した。`rough_covered_add_two_triple_eq_singleton_pair` が `Covered+2M3=N1+M2`、`rough_zero_pos_iff_singleton_moment` が `N0>0 ↔ N1+M2<R+2M3` を与える。

2. **singleton の分類**：`sqrt_singleton_point_cube_or_cross` は実際の singleton rough 点が必ず `p³` または `p*q`（p は actual active prime、sqrt n<p≤n、q は素数かつ n<q）になると証明する。追加の型はない。合成 cofactor の minFac を支持に戻して p と同定し、`sqrt_rough_square_quotient_one_or_prime` と四乗境界で残りの商を制限した。数値 factorization を production proof に用いない。

3. **一意性と disjointness**：`sqrt_cube_keys_offset_injective`, `sqrt_cross_representation_unique`, `sqrt_cross_keys_offset_injective`, `sqrt_cube_cross_disjoint_products`, `rough_cube_cross_disjoint` を証明。外部素数 q>n と内部 p≤n のサイズ分離により cross 表現の所有者と cofactor は一意。cube と cross は重ならない。

4. **cube の一様上界**：`sqrtRoughCubeKeys_card_le_one` は全 n で成立。sqrt n<p により n<p²、隣接 cube の差は shell 幅 2n を超える。実数 cube root や解析的評価は使わない。

5. **singleton census**：`sqrt_cube_offset_packet`, `sqrt_cross_offset_packet` が逆方向を証明し、`rough_singleton_eq_cube_union_cross` と `rough_singleton_card_eq_cube_cross` が集合等式と `N1=Cube+Cross` を与える。奇数性、Coprime(2n,point)、roughness、exact support を確認した。

6. **二支持 census**：`sqrtRoughRepeatedKeys` は sorted p<q と Bool side を持つ。false が p²q、true が pq²。`sqrt_repeated_offset_packet`, `sqrt_repeated_keys_offset_injective`, `rough_double_eq_repeated_seats`, `rough_double_card_eq_repeated` により N2 はキー数と等しい。支持集合が sorted pair を決定し、正の積の cancellation が side を決定する。`sqrt_repeated_pair_occupancy` は固定 pair の両 side を合わせても高々 1 席とする。

7. **三支持 census**：013 の `sqrtRoughTripleProductsInShell` をそのまま使い、`sqrt_triple_offset_packet`, `sqrt_triple_keys_offset_injective`, `rough_triple_eq_product_seats`, `rough_triple_card_eq_products` を証明した。N3 はキー数に等しく、`rough_tripleMoment_eq_strata` と既存 `sqrt_roughTripleMoment_eq_product_count` の双方に一致する。各 triple wave の既存 exact 0/1 occupancy を維持した。

8. **完全 factorization census**：`sqrt_rough_point_factorization` が任意の actual rough 点に対する五型の disjunction を返す。zero 点の prime/SquareCell は `sqrt_zero_point_prime` が既存 support-escape criterion から導出する。`sqrt_product_seats_pairwise_disjoint` が五型の全 10 組の disjointness、`sqrt_product_seats_union` が actual rough carrier との集合等式を明示的に証明する。

   `sqrt_rough_factorization_census` は

   ```text
   R = U + Cube + Cross + Repeated + Triple
   ```

   を与える。`sqrt_product_pairMoment`, `sqrt_product_incidence`, `sqrt_product_covered` がそれぞれ

   ```text
   M2 = Repeated + 3*Triple
   roughI = Cube + Cross + 2*Repeated + 3*Triple
   Covered = Cube + Cross + Repeated + Triple
   ```

   を与える。M3=Triple は既存定理。`sqrt_uncovered_pos_iff_product_census` が `U>0 ↔ Cube+Cross+Repeated+Triple<R` を証明し、その正確な margin は U である。

9. **per-p quotient/fiber 公式**：`sqrtRoughCrossFiber n p` は

   ```text
   Ioc (max n (n²/p)) ((n²+2n)/p), filtered by q.Prime
   ```

   で定義した。端点は `q.Prime ∧ n<q ∧ n²/p<q≤(n²+2n)/p` に正確に一致する。積の shell 条件との同値は `mem_sqrtRoughCrossKeys`。`sqrt_cross_count_eq_fiber_sum` が

   ```text
   Cross = Σ p∈roughActiveLabels(n,sqrt n), CrossFiber(n,p).card
   ```

   を与える。区間の始点も割ったため、有限評価は短い quotient window だけを走査する。

   Optional Phase19 も実装した。`sqrt_cross_fiber_eq_reduced_quotient_filter` は既存 reduced quotient interval の `q.Prime ∧ n<q` フィルタとの等式。これを証明してから `sqrt_cross_fiber_card_le_active_wave` と `primeAnchor_cross_fiber_card_le_floor` を導出した。q は active≤n の二次ラベルではない。

10. **残る最小の明示的一様不等式**：例えば今後の範囲を prime n>1019 と設定したとき、必要な provider は次の完全に具体的な型を持つ。

    ```text
    ∀ n, n.Prime → 1019<n →
      CubeKeys(n).card
        + Σ p∈roughActiveLabels(n,sqrt n), CrossFiber(n,p).card
        + RepeatedKeys(n).card + TripleProductsInShell(n).card
        < R(n)
    ```

    この不等式は未証明。`prime_squareCell_of_cross_fiber_budget` はこの仮定から square-cell prime を得る conditional consumer である。cube≤1 を使えば、cube を 1 に置いたより強い十分条件も作れるが、cube=0 の場合に余分な 1 を払う。Repeated/Triple の一様制御と R の下界も必要で、正確なキー数が得られたことだけでそれらが小さくなるとは主張しない。

## 六つの kernel calibration

|n|R|U=N0|N1|N2|N3|Cube|Cross|Repeated|Triple|
|---|---|---|---|---|---|---|---|---|---|
|211|82|42|35|1|4|0|35|1|4|
|503|169|81|78|3|7|0|78|3|7|
|1009|307|151|138|4|14|0|138|4|14|
|1013|311|147|154|3|7|0|154|3|7|
|1019|312|135|167|1|9|0|167|1|9|
|1021|311|149|142|1|19|0|142|1|19|

`LegendreSqrtRoughCensusCounts` と `LegendreSqrtRoughCensusCalibration` が数値入力を production carrier に接続する。以前の五つの checked moment rows を再利用し、1021 の inventory を既存 1019 inventory と素数境界の比較から証明し、rough-seat moments を独立に検証する。cube は六点とも新しく kernel 評価する。N1/N2/N3 は層別代数から、Cross は singleton census と cube 数から、Repeated/Triple は全単射から、U は完全 census から回収する。`census_cross_fiber_sum_checked` は六点の exact per-p fiber sum を regrouping と回収済み Cross 数から証明する。独立な個別 fiber の kernel 評価は (211,41)、(1019,37)、(1021,41) の 3 点で行い、それぞれ 3、7、7 席を確認する。`census_endpoints` は product-count 不等式を消費し、whole E/I の直接評価を使わない。

regression は cube n=5、external-cross n=7、両 repeated side n=13/29、triple n=19、zero anchor を含む。外部 cofactor が active ではないことも明示的に検証する。

## 有限探索から分かったこと

[discovery script](checks/discover-014.py) が奇素数アンカー 3≤n≤3000 の 429 点を調べ、分類の反例を見つけなかった。全行・全非zero fiber は [JSON](evidence/MANIFEST.md#log-aef25d1adff56610)、全アンカーの要約は [log](evidence/MANIFEST.md#log-dbbe15ffb1bb3159) に保存した。これは kernel proof の代替ではない。

指定点の N1/R は約 42.7%, 46.2%, 45.0%, 49.5%, 53.5%、追加 1021 は 45.7%。今回の六点の cube は 0、全探索では cube は 7 アンカーに 1 個ずつ存在した。最大 CrossFiber は 13 席。例えば 2083 の p=47、2477 の p=53 が 13 席を持つ。全探索の Repeated の最大値は 7、Triple は 54。2999 では Cross=387、Triple=49、Repeated=0。有限範囲でも Triple は残っており、無視してよいとはいえない。

幾何のみの `sqrt_cross_fiber_card_le_quotient_span` と `sqrt_cross_fiber_card_le_div_add_one`、奇素数アンカーの parity/anchor-exclusion floor 容量は正しいが、総和としては粗い。

|n|Σ(⌊2n/p⌋+1)|Σ odd active-wave floor capacity|R|Cross|
|---|---|---|---|---|
|211|276|129|82|35|
|503|693|331|169|78|
|1009|1361|627|307|138|
|1013|1369|642|311|154|
|1019|1379|653|312|167|
|1021|1383|647|311|142|

この比較値は保存済みの Python 診断であり、上の六点の census calibration と区別する。一様不等式・漸近推定を有限 scan から推論しない。

## 次の実装提案

次の焦点は **外部素数 q の条件を保持した CrossFiber 総和の上界**。既存波の容量をそのまま足す方法は上表で既に不足している。

1. まず各 owner p の reduced quotient interval を「prime q」と「composite quotient」に分割し、cube/repeated/triple の証明済み offset maps により、composite quotient がどの型に対応するかを点別に接続する。既存 carrier と moment を使い、新しい excess ledger を作らない。`q>n` と active secondary label≤n を分離した型を保つ。
2. 次に p-range を有限に分割し、整数 endpoint と parity spacing を使った各 range の exact capacity を実装する。`sqrt_cross_fiber_card_le_quotient_span`、`primeAnchor_cross_fiber_card_le_floor` を基準とし、素数条件でどれだけ容量を削れるかを独立な補題として示す。
3. 同じ range ごとに Repeated/Triple key を product endpoint から制限し、R の既存 wheel/rough 下界へ接続する。最終 acceptance condition は上記の cross-fiber additive budget。不等式が得られなければ、その不足量を具体的な有限範囲と型で報告する。

この段階では PNT、Bertrand、Brun/Selberg、RH、解析的 sieve estimate を使っていない。Legendre の予想、uniform T=1、FLT/ABC に関する結論は追加していない。

新規 production 69 宣言を含む 119 項目の公理監査は、標準の `propext`, `Classical.choice`, `Quot.sound` の範囲で全件通過し、`sorryAx` はない。focused/facade/root build、六点の校正、regression、禁則語・ヘッダー・whitespace チェックも通過した。root の既存 5 件の placeholder 警告は変更対象と区別して validation に記録した。

検証記録は [validation](validation-014.md)、再利用判断は [source inventory](source-inventory-014.md)、段階ごとの記録は [findings](findings-014.md) を参照。

Outcome A — COMPLETE SQRT-ROUGH FACTORIZATION CENSUS
