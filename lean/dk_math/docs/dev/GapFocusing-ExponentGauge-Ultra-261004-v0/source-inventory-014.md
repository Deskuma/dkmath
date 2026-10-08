# Source inventory 014

指定文書を今回の実装契約として読み、singleton の記述は仮定ではなく証明対象とした。既存 checkout の Instruction013、報告書、校正、実装を確認した。新 helper より前に記録した名前は [findings](findings-014.md) の Source checkpoint、最終宣言一覧は [inventory log](evidence/MANIFEST.md#log-462e90324848cfa4) にある。

|監査ソース|再利用した正確な名前と判断|
|---|---|
|`ParitySafeSqrtRoughFactorization`|`sqrt_rough_prime_divisor_gt`, `prime_dvd_candidate_mem_active`, `sqrt_two_support_repeated_prime`, `sqrt_roughTriple_point_eq_product`, `sqrtRoughTripleProductsInShell`, `sqrt_roughTripleMoment_eq_product_count`。既存 013 宣言は保持し、商補題と singleton 分類のみ追加。|
|`ParitySafeSqrtRoughMoments`|`rough_empty_eq_uncovered`, `sqrt_rough_moment_balance`, `sqrt_uncovered_card_pos_iff_moment`, `prime_squareCell_of_sqrt_moment`。新しい uncovered や moment ledger は作らない。|
|`ParitySafeSqrtRoughProductWaves`|`roughActiveLabels`, `rough_support_subset_labels`, `mem_roughPairs`, `mem_roughTriples`, `sqrt_roughPairWave_card_le_one`。支持は既存 actual active labels のまま。|
|`ParitySafeCanonicalRootTail`|`canonicalRoughCandidates`, `activeSupport_prod_dvd_point`, `rough_support_pow_le_point`。独立 sqrt cutoff と canonical erasure の相違を維持。|
|`ParitySafeCanonicalRoughCount`|`mem_uncovered_iff_no_activeSupport`, `roughWave_sum_eq_support_sum`。zero class、座席方向の和は既存機構から導出。|
|`ParitySafePrimeAnchorCap`|`sqrt_successor_square_gt`, `sqrtCutoff_power_four_gt`, `sqrtCutoff_support_card_le_three`。四乗境界は全自然数で使える。|
|`ParitySafeReducedResidue`|`activePrime_reducedResidue_packet`, `mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`, `mem_paritySafeReducedQuotientInterval_iff`, `paritySafeActiveWaveOffsets_quotient_properties`, `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval`。正確な prime-above-n filter を証明してから容量を使用。|
|`PairOverlap`|`squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity` と imported `Internal.upperPairs` の組合せ論を確認。旧 full-candidate pair count を新 rough carrier と同一視しない。|
|`Internal.RoughMomentCombinatorics`|`exists_ordered_triple_of_card_three`, `upperTriples_three`。既存中立補題を三支持の復元と単射に再利用。|
|`ParitySafeIncidenceBalance`, `Frontier`, `Basic`|`mem_paritySafeUncoveredCandidates_iff`, `prime_of_squareAnchoredSupportEscape`, `supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered`。zero の点別 primality を既存 escape consumer と同じ基準から導出。|
|`Wave`, `ParitySafeCanonicalRootCharge`|`card_squareWaveOffsets_eq_div_sub_div`, `card_squareWaveOffsets_le_div_add_one`, `paritySafeProductWave_card_eq_count`, `primeAnchorProductWaveCount`。幾何上界と odd-prime-anchor floor 容量を接続。|

Mathlib の素因子・自然数分解 API は `Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.minFac_sq_le_self`, `Nat.Prime.dvd_mul`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.prime_dvd_prime_iff_eq`, `Nat.factorization_pow_self`, `Nat.Prime.factorization_pow` を確認した。数値 factorization によらず、素数の積整除と順序付き支持集合の一致、正の積の cancellation でキー一意性を証明した。

有限集合 API は `Finset.card_eq_one`, `Finset.card_eq_two`, `Finset.card_eq_three`, `Finset.card_image_of_injOn`, `Finset.card_bij`, `Finset.card_eq_sum_card_fiberwise`, `Finset.card_filter_add_card_filter_not`, `Finset.sum_ite`, `Finset.sum_boole`。商の整数端点には `Nat.div_lt_iff_lt_mul`, `Nat.le_div_iff_mul_le`, 奇数間隔には `Nat.Odd.sub_odd` を使用した。校正専用の短い試し割り条件は Mathlib `Nat.prime_def_le_sqrt` で Nat.Prime と同値と証明した。

`CrossFiber(n,p)` は `q>n` の外部素数であり、`canonicalRoughWave` の二次 active label `q≤n` と同一視しない。Optional Phase19 の接続は、既存 reduced quotient interval の prime-above-n 部分への証明済み等式に限定する。
