# リファクタリング変更履歴

- 旧名前空間 `ABC` を `DkMath.ABC` に変更
  - `namespace ABC` → `namespace DkMath.ABC`
  - `end ABC` → `end DkMath.ABC`
- `count_powers_dividing_2n1` を `DkMath.ABC.CountPowersDividing2n1` に集約
  - これに伴い、ABC020.lean での `count_powers_dividing_2n1` を廃止
  - ABC023.lean での重複 `lemma count_powers_dividing_2n1'` を廃止
  - 参照先である ABC024.lean で、インポートを追加
    - `import DkMath.ABC.CountPowersDividing2n1`
    - 以降の ABC025.lean, ABC028.lean も同様にインポートを追加
- Core.lean で定義されていた rad 関数を `DkMath.ABC.Rad.rad` に１本化
  - これに伴い、Core.lean での `rad` 定義を廃止
  - 参照先である MassBridge.lean で、インポートを追加
    - `import DkMath.ABC.Rad`
- Core.lean に残っていた radical-kernel 補題群を `DkMath.ABC.Rad` に集約
  - 移設した補題
    - `mem_support_factorization_iff`
    - `support_prod_log_eq_sum_log`
    - `support_prod_log_ge_sum_log`
    - `rad_prod`
    - `rad_log_eq_sum_prime_logs`
    - `rad_log_ge_sum_prime_logs`
    - `disjoint_support_of_coprime`
    - `support_mul_coprime`
    - `rad_mul_coprime`
    - `rad_le`
  - Core.lean 側の重複定義は削除し、
    radical kernel の owner を `DkMath.ABC.Rad` に固定
- `Square.lean` に残っていた pure-rad 補題群を `DkMath.ABC.Rad` に追加集約
  - 移設した補題
    - `rad_eq_self_of_squarefree`
    - `rad_eq_self_of_squarefree'`
    - `factorization_prod_primes`
    - `squarefree_of_rad_eq_self`
    - `rad_pow_eq_rad`
    - `rad_mul_general`
    - `rad_mul_coprime'`
    - `abc_one_le_rad`
    - `rad_pos`
  - `Square.lean` 側には squarefree / squarefull と近接積の応用補題だけを残した
- `Triple.lean` の import を `DkMath.ABC.Core` から `DkMath.ABC.Rad` へ変更
  - `Triple` 自身は radical kernel だけで足りることを確認
- `RatioBound.lean` に `import DkMath.ABC.Basic` を追加
  - `Nat.ceil_spec` / `div_lt_iff` を `Triple -> Core` の隠れ依存で拾っていたため、
    import を明示化
- `succ_sub_self` / `dvd_one_iff` / `gcd_succ` / `coprime_succ` の owner を `DkMath.Basic.Nat` に固定
  - `ABC.Core` の重複定義は削除
  - `ABC.Core` では
    `export DkMath.Basic.Nat (succ_sub_self dvd_one_iff gcd_succ coprime_succ)`
    により既存の `DkMath.ABC.*` 呼び口だけを維持
  - hidden import の実例として `ABC001.lean` に `import DkMath.Basic.Nat` を追加
- `padicValNat_split` の owner を `DkMath.ABC.PadicValNat` に固定
  - `ABC.Core` の重複定義は削除
  - `ABC.Core` には `import DkMath.ABC.PadicValNat` を追加し、
    既存の `DkMath.ABC.*` 呼び口は import 経由で維持
  - valuation 系の基本補題は `Core` ではなく `PadicValNat` が持つ方針を明示
- `ABC020.lean` に残っていた `padic_val_two_of_odd` の重複断片を削除
  - owner は `DkMath.ABC.PadicValNat` に固定
  - `ABC020` ではローカル定義を持たず、
    valuation/counting の基本補題は owner module を参照する形に整理
- `ABC025.lean` に残っていた `padicValNat_le_self` / `padicValNat_le_log` の重複断片を削除
  - `import DkMath.ABC.PadicValNat` を追加
  - telescoping 本体はそのままにして、
    valuation の basic bounds は owner module を参照する形へ整理
- live chain の `ABC0**.lean` について、
  `DkMath.ABC.PadicValNat` の lemma 名との重複を機械探索
  - この時点では追加の重複は検出されなかった
  - `ABCSolvedProofSamples.lean` / `ABCWorking.lean` は scratch/archive 系として別管理に切り分け
- `DkMath.ABC.Demo` を新設し、以下のファイルを移設
  - `lean/dk_math/DkMath/ABC/Demo/ABCSolvedProofSamples.lean` へ移設。
  - `lean/dk_math/DkMath/ABC/Demo/ABCWorking.lean` へ移設。
  - これらはリファクタリングの作業対象外。
- `squarefree` / `squarefull` と mirror alias 群の owner を `DkMath.ABC.Square` に固定
  - `Square.lean` の import を `DkMath.ABC.Core` から `DkMath.ABC.Rad` へ変更
  - `Square.lean` に
    `squarefull'`, `squarefree_prop`, `squarefree`, `squarefull`
    の定義を集約
  - `ABC.Core` から上記定義の重複を削除し、
    `import DkMath.ABC.Square` を追加
  - `Core` は squarefree / squarefull の owner ではなく、
    import 経由で公開する境界に整理
- `DkMath.ABC.Main` に `import DkMath.ABC.Square` を追加
  - squarefree / squarefull surface を transitively ではなく direct import で公開
- `Main` build で露出した hidden import を explicit owner import に修正
  - `ABC001.lean` では `coprime_succ` を `DkMath.Basic.Nat.coprime_succ` に明示
  - `ABC002.lean`, `ABC003.lean`, `ABC014.lean`, `ABC015.lean`, `ABC016.lean`, `ABC031.lean`
    に `import DkMath.Basic.Nat` と `open DkMath.Basic.Nat` を追加
  - `ABC009.lean` に `import DkMath.ABC.Core` を追加し、
    `RpowExtras.rpow_mul_nat` の owner 依存を明示
  - これにより `Main` 側の hidden import 探索を継続可能な状態に進めた
- `chain-cut-patterns-001.md` を追加
  - `ABC連番.lean` の切断パターンを
    `owner import 露出型`, `shared utility 横刺し型`, `thin base + thematic band 型`
    として整理
  - 次の具体候補として
    `RpowExtras` 専用 module 化,
    `ABC024`-`ABC028` utility-first 化,
    `ABC001`-`ABC003` base seam 固定
    をメモ化
- `RpowExtras` を `DkMath.ABC.RpowExtras` に切り出し
  - `rpow_mul_nat`, `one_lt_rpow_two`, `denom_pos` を `Core` から移設
  - `ABC.Core` には `import DkMath.ABC.RpowExtras` を追加し、
    ローカル namespace は削除
  - `ABC009.lean` は `import DkMath.ABC.Core` ではなく
    `import DkMath.ABC.RpowExtras` を使う形に変更
  - これにより `ABC009 -> Core` 依存を 1 本切断
- `ABC024.lean` の serial predecessor import を utility owner import へ置換
  - `import DkMath.ABC.ABC023` を削除
  - 代わりに
    `import DkMath.ABC.ABC022`,
    `import DkMath.ABC.RatioBound`,
    `import DkMath.ABC.CountPowersDividing2n1`
    を明示
  - `ABC023.lean` は実質 empty relay なので、
    `ABC024`
    は layer-cake / ceil / counting の owner を直接引く形へ整理
  - build は
    `ABC024`,
    `ABC025`,
    `ABC028`
    まで通り、
    `ABC024`-`ABC028`
    帯で
    utility-first cut
    が実際に成立することを確認
- `ABC025.lean` から不要な serial predecessor import を削除
  - `import DkMath.ABC.ABC024` は未使用だったため削除
  - `ABC025` は
    `ABC025_bound2`, `CountPowersDividing2n1`, `PadicValNat`
    だけで build できることを確認
  - これにより
    `ABC024 -> ABC025`
    の serial edge を 1 本切断
- `ABC028.lean` に `import DkMath.ABC.ABC019` を追加
  - `markov_card_bound` の hidden import が
    `Main` build で露出したため owner import を明示
  - `ABC025 -> ABC028`
    cut 後でも
    `ABC028`
    は
    `ABC019`
    を direct import すれば通ることを確認
- `ABC033.lean` に `import DkMath.ABC.ABC022` と `import DkMath.ABC.Core` を追加
  - `three_pow_ge_linear` の owner は `Core`
  - `rpow_layer_cake` の owner は `ABC022`
  - `Main` build の hidden import 停止点を explicit owner import 化して解消
- `ABC033.lean` から `import DkMath.ABC.ABC032` を削除
  - 代わりに
    `import DkMath.ABC.ABC025`
    を追加
  - `ABC033`
    が実際に使っていたのは
    `ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3`
    であり、
    owner は
    `ABC025`
    だった
  - これにより
    `ABC032 -> ABC033`
    の serial edge を切断し、
    `ABC033`
    は
    `ABC022` + `ABC025` + `Core`
    の owner import で閉じる形になった
- `ABC090.lean` の empty relay import を整理
  - `import DkMath.ABC.ABC040` を削除
  - 代わりに最小環境として
    `import DkMath.ABC.Basic`
    を追加
  - `ABC090`
    自体は空 shell なので、
    `ABC040`
    を経由する必要はなかった
  - これにより
    `ABC090 -> ABC040`
    の serial edge を切断
- `ABC038.lean` の serial predecessor import を整理
  - `import DkMath.ABC.ABC037` を削除
  - 代わりに
    `import DkMath.ABC.ABC036`
    を追加
  - `ABC038`
    が必要としていたのは
    `Bad_ε`
    など
    `ABC036`
    owner の記号であり、
    `ABC037`
    の density 補題自体は未使用だった
  - これにより
    `ABC037 -> ABC038`
    の serial edge を切断
- `ABC039.lean` に `import DkMath.ABC.ABC037` を追加
  - `ABC038`
    を薄くした結果、
    `bad_set_density_bound_quality`
    の owner が
    `ABC037`
    として露出したため、
    direct import へ置き換えた
  - `ABC039`
    は
    `ABC038`
    の quality 側 API と
    `ABC037`
    の density 側 API の両方を使うことが明確になった
- `ABC036.lean` の serial predecessor import を整理
  - `import DkMath.ABC.ABC035`
    を削除
  - 代わりに
    `import DkMath.ABC.ABC034`
    を追加
  - `ABC036`
    が実際に使っていたのは
    `chernoff_single_prime_uniform_rpow`
    を中心とする
    single-prime Chernoff kernel
    であり、
    `ABC035`
    の union-bound API は未使用だった
  - これにより
    `ABC035 -> ABC036`
    の serial edge を切断
- single-prime Chernoff kernel を `DkMath.ABC.ChernoffSinglePrime` に切り出し
  - 旧
    `ABC033.lean`
    が持っていた
    `Vp`, `Excess`, `pge3`, `const_C`, `const_X`, `primesUpTo`,
    `mgf_padic_excess_bound_uniform`, `card_filter_le_exp_markov`,
    `t_bound_log2_div_log3`
    などの Chernoff kernel 群を
    新 utility module
    `ChernoffSinglePrime.lean`
    に移設
  - `ABC033.lean`
    自体は
    `import DkMath.ABC.ChernoffSinglePrime`
    だけを持つ compatibility relay に縮小
  - `ABC034.lean`
    は
    `import DkMath.ABC.ABC033`
    ではなく
    `import DkMath.ABC.ChernoffSinglePrime`
    を direct import する形へ変更
  - これにより
    `ABC033 -> ABC034`
    の serial edge を切断し、
    `ABC034`
    帯を
    番号 file
    ではなく
    thematic utility
    に接続した
- `ChernoffSinglePrime.lean` を `ChernoffBasic` + `ChernoffSinglePrime` の二層に再分割
  - 新設:
    `DkMath.ABC.ChernoffBasic`
  - `ChernoffBasic.lean`
    に移したもの
    - notation / arithmetic helper:
      `n2a1`, `Vp`, `Excess`
    - threshold / constant / index helper:
      `pge3`, `const_C`, `const_X`, `primesUpTo`,
      `prime_mem_primesUpTo_of_dvd_odd`
    - analytic helper:
      `card_filter_le_exp_markov`,
      `t_bound_log2_div_log3`,
      `absorb_constant_4_to_5`
  - `ChernoffSinglePrime.lean`
    側には
    `mgf_padic_excess_bound_uniform`,
    `mgf_padic_excess_bound_explicit`,
    `mgf_padic_excess_bound`,
    `chernoff_engine`
    だけを残した
  - これにより
    `ChernoffSinglePrime`
    は
    MGF / engine owner、
    `ChernoffBasic`
    は
    notation/constants/Markov owner
    という役割に整理された
  - `DkMath.ABC.Main` build を再実行し成功
  - `ABC025` / `ABC028` / `ABC033`
    の owner import 明示化後、
    public entry まで clean に通ることを確認
- `ABC034.lean` の single-prime convenience theorem を
  `DkMath.ABC.ChernoffSinglePrime`
  へ移設
  - moved:
    `chernoff_single_prime_uniform`
  - moved:
    `chernoff_single_prime_uniform_rpow`
  - 吸収定数
    `4 -> 5`
    の局所証明は
    `absorb_constant_4_to_5`
    を使う形へ整理し、
    convenience layer 側の重複も減らした
  - `ABC034.lean`
    自体は
    `import DkMath.ABC.ChernoffSinglePrime`
    だけを持つ compatibility relay に縮小
  - これにより
    `ABC034`
    は owner file ではなく relay file となり、
    single-prime branch の convenience 層は
    `ChernoffSinglePrime`
    が一括して持つ構成になった
- `DkMath.ABC.Main` build を再実行し成功
  - `ABC034` の owner 降格後も
    `ABC035` / `ABC036` / `ABC038Bridge`
    を含む public chain が通ることを確認
- union-bound convenience 層を
  `DkMath.ABC.ChernoffUnionBound`
  として切り出し
  - 新設:
    `ChernoffUnionBound.lean`
  - moved:
    `chernoff_single_prime_explicit'`
  - moved:
    `chernoff_single_prime_explicit`
  - moved:
    `union_bound_chernoff`
  - moved:
    `union_bound_chernoff'`
  - moved:
    `union_bound_chernoff_pow`
  - moved:
    `union_bound_chernoff_pow'`
  - `ChernoffUnionBound`
    は
    `ChernoffSinglePrime`
    を import して、
    explicit specialization と union-bound 層の owner を持つ構成にした
  - `ABC035.lean`
    自体は
    `import DkMath.ABC.ChernoffUnionBound`
    だけを持つ compatibility relay に縮小
  - これにより
    `ABC035`
    も owner file ではなく relay file となり、
    Chernoff 帯の union-bound branch は
    非連番 utility module
    に乗った
- `DkMath.ABC.Main` build を再実行し成功
  - `ABC035` の owner 降格後も
    public chain が通ることを確認
- density 層を
  `DkMath.ABC.ChernoffDensity`
  として切り出し
  - 新設:
    `ChernoffDensity.lean`
  - moved:
    `Bad_ε`
  - moved:
    `bad_iff_exists_excess`
  - moved:
    `exp_one_gt_one`
  - moved:
    `decidable_Bad_ε`
  - moved:
    `p_lt_X_to_p_lt_X_succ`
  - moved:
    `bad_set_density_bound_param`
  - moved:
    `bad_set_density_bound'`
  - `ChernoffDensity`
    は
    `ChernoffUnionBound`
    を import して、
    bad-set / density 層の owner を持つ構成にした
  - `ABC036.lean`
    自体は
    `import DkMath.ABC.ChernoffDensity`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ABC037.lean`
    と
    `ABC038.lean`
    を
    `ABC036`
    relay 経由ではなく
    `ChernoffDensity`
    の direct import に変更した
  - これにより
    `ABC036`
    も owner file ではなく relay file となり、
    density branch が
    非連番 utility module
    に昇格した
- `DkMath.ABC.Main` build を再実行し成功
  - `ChernoffDensity`
    を含む public chain が通ることを確認
- quality-specific density 層を
  `DkMath.ABC.ChernoffQualityDensity`
  として切り出し
  - 新設:
    `ChernoffQualityDensity.lean`
  - moved:
    `construct_HΛ_for_quality`
  - moved:
    `bad_set_density_bound_quality`
  - `ChernoffQualityDensity`
    は
    `ChernoffDensity`
    を import して、
    quality 用 Λ 構成と density specialization の owner を持つ構成にした
  - `ABC037.lean`
    自体は
    `import DkMath.ABC.ChernoffQualityDensity`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ABC039.lean`
    を
    `ABC037`
    relay 経由ではなく
    `ChernoffQualityDensity`
    の direct import に変更した
  - relay 追跡用の
    `check-relay-lean.md`
    にも
    `ABC034` / `ABC035` / `ABC036` / `ABC037`
    の移設先を追記した
- `DkMath.ABC.Main` build を再実行し成功
  - `ChernoffQualityDensity`
    を含む public chain が通ることを確認
- quality / bridge 層を
  `DkMath.ABC.ChernoffQualityBridge`
  として切り出し
  - 新設:
    `ChernoffQualityBridge.lean`
  - moved:
    `abc_c_pos`
  - moved:
    `not_isCoprime_zero_nonzero`
  - moved:
    `not_isCoprime_nonzero_zero`
  - moved:
    `prime_of_mem_factorization_support`
  - moved:
    `Excess_ABC`
  - moved:
    `Bad_ε_ABC`
  - moved:
    `not_bad_abc_implies_vp_bound`
  - moved:
    `twoTail_log_bound_of_not_bad_abc`
  - moved:
    `quality_le_of_not_bad`
  - moved:
    `quality_le_of_not_bad_abc`
  - moved:
    `quality_le_of_not_bad_with_tail`
  - moved:
    `tailbound_of_log_bound`
  - moved:
    `quality_le_of_not_bad_with_log`
  - `ABC038.lean`
    自体は
    `import DkMath.ABC.ChernoffQualityBridge`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ABC039.lean`
    と
    `ABC038Bridge.lean`
    を
    `ABC038`
    relay 経由ではなく
    `ChernoffQualityBridge`
    の direct import に変更した
- final quality theorem 層を
  `DkMath.ABC.ChernoffQualityFinal`
  として切り出し
  - 新設:
    `ChernoffQualityFinal.lean`
  - moved:
    `twoTail_log_bound_of_not_bad_eps`
  - moved:
    `twoTail_log_bound_of_not_bad_eps_budget`
  - moved:
    `abc_quality_pointwise`
  - moved:
    `abc_quality_density`
  - moved:
    `abc_quality_hybrid`
  - `ABC039.lean`
    自体は
    `import DkMath.ABC.ChernoffQualityFinal`
    だけを持つ compatibility relay に縮小
  - `ABC040.lean`
    は
    `ABC039`
    経由ではなく
    `ChernoffQualityFinal`
    を direct import する shell に整理
- `abc_main` 最終定理層を
  `DkMath.ABC.ABCMainTheorem`
  として切り出し
  - 新設:
    `ABCMainTheorem.lean`
  - moved:
    `K_eps`
  - moved:
    `abc_main_axiom`
  - moved:
    `abc_main`
  - `ABC032.lean`
    自体は
    `import DkMath.ABC.ABCMainTheorem`
    だけを持つ compatibility relay に縮小
  - `DkMath.ABC.Main`
    には
    `import DkMath.ABC.ABCMainTheorem`
    を追加し、
    public entry から
    `abc_main`
    系へ直接届く導線を作った
- adjacent-quality 層を
  `DkMath.ABC.AdjacentQuality`
  として切り出し
  - 新設:
    `AdjacentQuality.lean`
  - moved:
    `adjacent_quality_le_density_one`
  - moved:
    `adjacent_quality_le_ae_alt`
  - `ABC031.lean`
    自体は
    `import DkMath.ABC.AdjacentQuality`
    だけを持つ compatibility relay に縮小
  - `ABCMainTheorem.lean`
    の import は
    `ABC031`
    ではなく
    `Rad`
    に薄くし、
    final theorem 層の serial predecessor 依存を除去
- adjacent tail / Chernoff budget 層を
  `DkMath.ABC.AdjacentTailDensity`
  として切り出し
  - 新設:
    `AdjacentTailDensity.lean`
  - moved:
    `union_bound_chernoff_log_rad`
  - moved:
    `chernoff_single_prime_uniform`
  - moved:
    `chernoff_single_prime_uniform_easy`
  - moved:
    `EventuallyChernoffBudgetAdjacentHypothesis`
  - moved:
    `twoTail_log_bound_adjacent_density_one`
  - `ABC030.lean`
    自体は
    `import DkMath.ABC.AdjacentTailDensity`
    だけを持つ compatibility relay に縮小
  - downstream では
    `AdjacentQuality.lean`
    を
    `ABC030`
    relay 経由ではなく
    `AdjacentTailDensity`
    の direct import に変更した
- dyadic / analytic Chernoff helper 層を
  `DkMath.ABC.ChernoffDyadic`
  として切り出し
  - 新設:
    `ChernoffDyadic.lean`
  - moved:
    `chernoff_single_prime_constants`
  - moved:
    `chernoff_constants_for_finset`
  - moved:
    `chernoff_sum_crude_bound`
  - moved:
    `nat_card_le_of_real_le`
  - moved:
    `chernoff_light_primes_sum_bound`
  - moved:
    `dyadic_block`
  - moved:
    `mem_dyadic_block_iff`
  - moved:
    `dyadic_block_subset_range`
  - moved:
    `dyadic_block_prime_subset`
  - moved:
    `dyadic_block_card_le_primes_upto`
  - moved:
    `dyadic_partition_skeleton`
  - moved:
    `finite_abel_partial_summation`
  - moved:
    `block_sum_le_Cmax_mul_sum`
  - moved:
    `block_sum_le_Cmax_chernoff`
  - moved:
    `dyadic_block_card_le_pow_two`
  - moved:
    `dyadic_block_sum_crude`
  - `ABC029.lean`
    自体は
    `import DkMath.ABC.ChernoffDyadic`
    だけを持つ compatibility relay に縮小
  - downstream では
    `AdjacentTailDensity.lean`
    を
    `ABC029`
    relay 経由ではなく
    `ChernoffDyadic`
    の direct import に変更した
- MGF / single-prime Chernoff core 層を
  `DkMath.ABC.ChernoffMgf`
  として切り出し
  - 新設:
    `ChernoffMgf.lean`
  - moved:
    `mgf_padic_excess_bound_pbase`
  - moved:
    `mgf_padic_excess_bound_two`
  - moved:
    `mgf_padic_excess_bound_le_C`
  - moved:
    `chernoff_single_prime`
  - `ABC028.lean`
    自体は
    `import DkMath.ABC.ChernoffMgf`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ChernoffDyadic.lean`
    を
    `ABC028`
    relay 経由ではなく
    `ChernoffMgf`
    の direct import に変更した
  - あわせて
    `ChernoffMgf.lean`
    に
    `import DkMath.ABC.ABC025`
    を追加し、
    `ABC.Telescoping.sum_pow_padicValNat_le_geom_half`
    の owner 依存を explicit import 化した
- heavy-prime budget / ceiling helper 層を
  `DkMath.ABC.HeavyPrimeBudget`
  として切り出し
  - 新設:
    `HeavyPrimeBudget.lean`
  - moved:
    `ceil_div_le_one_of_p3_gt_X`
  - moved:
    `term_le_four_of_p3_gt_X`
  - moved:
    `four_le_two_ceil_quarter_add_two`
  - moved:
    `B_mul_ceil_div_le_ceil_of_large`
  - moved:
    `eventually_pow_ge_twenty`
  - `ABC027.lean`
    自体は
    `import DkMath.ABC.HeavyPrimeBudget`
    だけを持つ compatibility relay に縮小
  - downstream では
    `AdjacentTailDensity.lean`
    を
    `ABC027`
    relay 経由ではなく
    `HeavyPrimeBudget`
    の direct import に変更した
- heavy-prime selection / witness 層を
  `DkMath.ABC.HeavyPrimeSelection`
  として切り出し
  - 新設:
    `HeavyPrimeSelection.lean`
  - moved:
    `K_of`
  - moved:
    `S_heavy_def`
  - moved:
    `mem_S_heavy_of_pow_le`
  - moved:
    `S_heavy_subset_range`
  - moved:
    `S_heavy_basic`
  - moved:
    `witness_n_for_S_heavy`
  - `ABC026.lean`
    自体は
    `import DkMath.ABC.HeavyPrimeSelection`
    だけを持つ compatibility relay に縮小
  - downstream では
    `AdjacentTailDensity.lean`
    を
    `ABC026`
    relay 経由ではなく
    `HeavyPrimeSelection`
    の direct import に変更した
  - `HeavyPrimeBudget.lean`
    からは不要になった
    `ABC026`
    依存を削除した
- telescoping / p-adic sum-bound 層を
  `DkMath.ABC.PadicTelescoping`
  として切り出し
  - 新設:
    `PadicTelescoping.lean`
  - moved:
    `ABC025.lean`
    全体
    (`namespace DkMath.ABC.Telescoping`)
  - `ABC025.lean`
    自体は
    `import DkMath.ABC.PadicTelescoping`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ChernoffMgf.lean`,
    `ChernoffSinglePrime.lean`,
    `ABC025_allX.lean`
    を
    `ABC025`
    relay 経由ではなく
    `PadicTelescoping`
    の direct import に変更した
  - `HeavyPrimeBudget.lean`,
    `HeavyPrimeSelection.lean`
    は
    `ABC025`
    ではなく
    `DkMath.ABC.Basic`
    を import する形へ薄くした
- layer-cake MGF の代替証明層を
  `DkMath.ABC.ChernoffMgfLayercake`
  として切り出し
  - 新設:
    `ChernoffMgfLayercake.lean`
  - moved:
    `ABC024.lean`
    全体
    (`mgf_padic_excess_bound_pbase_layercake`)
  - `ABC024.lean`
    自体は
    `import DkMath.ABC.ChernoffMgfLayercake`
    だけを持つ compatibility relay に縮小
  - 今回は code consumer 側の import 変更は無く、
    relay / owner 境界の確定と
    追跡可能化が主眼
- layer-cake helper / primitive 層を
  `DkMath.ABC.LayerCakeBasic`
  として切り出し
  - 新設:
    `LayerCakeBasic.lean`
  - moved:
    `ABC022.lean`
    全体
    (`rpow_layer_cake`, `div_le_iff`, `ceil_spec`,
    `natCeil_le_add_one_real'`, `sum_Icc_telescope'`, `exp_layer_cake'`)
  - `ABC022.lean`
    自体は
    `import DkMath.ABC.LayerCakeBasic`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ABC023.lean`,
    `ChernoffMgfLayercake.lean`,
    `ChernoffSinglePrime.lean`
    を
    `ABC022`
    relay 経由ではなく
    `LayerCakeBasic`
    の direct import に変更した
- tail / analytic helper 層を
  `DkMath.ABC.TailAnalyticBasic`
  として切り出し
  - 新設:
    `TailAnalyticBasic.lean`
  - moved:
    `ABC019.lean`
    全体
    (`TailBound`, `sqPart`, `quality_le_of_pi_tail_general`,
    `log_twoTail_le_excess_sum`, `markov_card_bound`,
    `sum_Icc_telescope`, `exp_layer_cake`)
  - `ABC019.lean`
    自体は
    `import DkMath.ABC.TailAnalyticBasic`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ChernoffMgf.lean`
    と
    `ABC020.lean`
    を
    `ABC019`
    relay 経由ではなく
    `TailAnalyticBasic`
    の direct import に変更した
- mixed basic band
  `TailAnalyticBasic`
  を二分割し、
  `TailSquareBridge`
  と
  `FiniteChernoffBasic`
  へ再配置
  - 新設:
    `TailSquareBridge.lean`
  - moved:
    `TailBound`, `sqPart`, `sqPart_eq_evenPart_pow2`,
    `oddPart_le_rad`, `sqTail_le_sqPart`,
    `c_le_sqPart_mul_rad`,
    `quality_le_of_pi_tail_general`,
    `log_twoTail_le_excess_sum`
  - 新設:
    `FiniteChernoffBasic.lean`
  - moved:
    `markov_card_bound`, `sum_Icc_telescope`, `exp_layer_cake`
  - `TailAnalyticBasic.lean`
    自体は
    `import DkMath.ABC.TailSquareBridge`
    と
    `import DkMath.ABC.FiniteChernoffBasic`
    を持つ compatibility relay / aggregator に縮小
  - downstream では
    `ChernoffMgf.lean`
    を
    `FiniteChernoffBasic`
    の direct import に、
    `ABC020.lean`
    を
    `TailSquareBridge`
    の direct import に変更した
  - 分割直後に
    `LayerCakeBasic.lean`
    の hidden import が露出したため、
    `FiniteChernoffBasic`
    を direct import する修正も併せて入れた
- Janson roadmap / expectation helper 層を
  `DkMath.ABC.JansonRoadmap`
  として昇格
  - 新設:
    `JansonRoadmap.lean`
  - moved:
    `ABC021.lean`
    全体
    (`PMF.expect_mono`, `markov_inequality`,
    `chebyshev_inequality`, `Janson.mgf`,
    `exp_sum_eq_prod_exp`,
    `expect_prod_eq_prod_expect`,
    `mgf_sum_indep`,
    `second_moment_zero_prob`,
    `variance_indicator_sum`,
    `janson_core_inequality`,
    `bound_v2_from_janson`)
  - `ABC021.lean`
    自体は
    `import DkMath.ABC.JansonRoadmap`
    だけを持つ compatibility relay に縮小
  - `LayerCakeBasic.lean`
    からは
    `ABC021`
    import を削除した
    （live chain では未使用だったため）
  - この結果
    `ChernoffQualityBridge.lean`
    の
    `TailSquareBridge`
    hidden import が露出したため、
    `import DkMath.ABC.TailSquareBridge`
    を direct 化して復旧した
- Janson branch の import spine を 1 本薄くした
  - `JansonRoadmap.lean`
    の import を
    `ABC020`
    relay 経由から
    `ABC008`
    への direct import に変更した
  - これにより
    `ABC020`
    は
    `TailSquareBridge`
    への relay としてのみ残る状態が、
    import 実態と追跡表の両方で一致した
- Janson basic / PMF infrastructure 層を
  `DkMath.ABC.JansonBasic`
  に昇格
  - 新設:
    `JansonBasic.lean`
  - moved:
    `ABC008.lean`
    全体
    (`JansonModel`, `JansonSetup`, `mu`, `dbar`,
    `bernoulli_pmf`, `product_pmf`,
    `expect_indicator_prod` など)
  - `ABC008.lean`
    自体は
    `import DkMath.ABC.JansonBasic`
    だけを持つ compatibility relay に縮小
  - downstream では
    `ABC009.lean`
    と
    `JansonRoadmap.lean`
    を
    `ABC008`
    relay 経由ではなく
    `JansonBasic`
    の direct import に変更した
- Janson branch の relay 追跡をさらに明確化
  - `ABC008.lean`
    は
    `JansonBasic`
    への relay、
    `ABC021.lean`
    は
    `JansonRoadmap`
    への relay、
    `ABC020.lean`
    は
    `TailSquareBridge`
    への relay、
    という 3 本の役割分担が成立した
