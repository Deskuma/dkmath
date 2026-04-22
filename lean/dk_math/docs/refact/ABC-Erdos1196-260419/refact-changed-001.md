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
