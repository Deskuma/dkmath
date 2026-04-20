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
