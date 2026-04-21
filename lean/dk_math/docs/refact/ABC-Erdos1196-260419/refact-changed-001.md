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
