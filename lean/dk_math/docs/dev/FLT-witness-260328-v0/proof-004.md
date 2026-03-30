# 正しい証明経路：`ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`

`cyclotomicPrimeCore d x u` = `((x+u)^d - u^d) / x` を使う **boundary route** が正道じゃ。こちらは `u = 1` でも生きる（`cyclotomicPrimeCore 5 5 1 = 1555 = 5 × 311`）。

## Mathlib.FLT なしの証明戦略（5 ステップ）

1. **`p ∣ x, p ≠ d` ⟹ `p ∤ core`** — `core ≡ d·u^{d-1} [MOD p]` かつ `p ∤ d`, `p ∤ u`
2. **`core ≡ d·u^{d-1} [MOD d²]`** — 二項展開の精密評価
3. **Wieferich 条件適用** → `core ≡ d [MOD d²]` → `v_d(core) = 1` → `d ∤ (core/d)`
4. **合成** → `gcd(core/d, x) = 1`、`core/d ≥ 259`
5. **`Nat.exists_prime_and_dvd`** → witness `q` 取得

**必要な中間補題は 2〜3 本。全ブリッジは既に実装済みじゃから、`PreparedArithmeticCoreConcrete` 1 本を埋めれば proof file mainline まで自動的に閉じる。** どうじゃ？
