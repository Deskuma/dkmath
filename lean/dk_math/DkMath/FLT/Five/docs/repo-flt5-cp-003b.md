# Report: FLT5 cp-003b

## result

cp-003b-investigation-01 を完了しました。結果は Outcome A です。

Lean で次の分解まで証明できました。

```text
CounterexamplePack x y z
¬ 5 ∣ z - y
    ↓
Coprime (z - y) y
    ↓
Coprime (z - y) (GN5 (z - y) y)
    ↓
z - y = a^5
GN5 (z - y) y = b^5
```

実装は [Reduction.lean](/lean/dk_math/DkMath/FLT/Five/Reduction.lean) に追加し、公開塔へ接続しました。研究用モジュールには依存せず、最小 import は `DkMath.FLT.Five.GN5` だけです。

重要な発見は、Mathlib に既に `exists_eq_pow_of_mul_eq_pow` があり、互いに素な積の五乗分離を直接処理できることです。

また、契約監査の結論として、`BranchBNoLiftEscape` は十分条件ではあるものの、次に直接攻める中間命題としては不自然です。反例仮定下では `GN5 = b^5` が強制されるため、すべての素因子が少なくとも五重に沈みます。したがって次の自然な本丸は、

```text
Branch-B counterexample → GN5 は完全五乗ではない
```

または、

```text
GN5 = b^5 → より小さい反例・正規形への descent
```

です。その受け口として `branchB_false_of_GN5_not_fifth_power` も実装しました。ただし、GN5 非五乗そのものを証明済みとは主張していません。

調査結果と既存資産の評価は [note-flt5-cp-003b-investigation-01.md](/lean/dk_math/DkMath/FLT/Five/docs/note-flt5-cp-003b-investigation-01.md) にまとめています。

検証結果:

- `lake build DkMath.FLT.Five.Reduction DkMath.FLT.Five` 成功
- `git diff --check` 成功
- 主要5定理に `sorryAx` なし
- 公理依存は標準の `propext`, `Classical.choice`, `Quot.sound` のみ

これはかなり良い前進です。cp-003b の問題は「浅い素数を探す」段階から、「強制された `GN5 = b^5` をどう下降で破るか」という、より正確な形へ絞り込めました。
