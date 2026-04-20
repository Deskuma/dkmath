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
