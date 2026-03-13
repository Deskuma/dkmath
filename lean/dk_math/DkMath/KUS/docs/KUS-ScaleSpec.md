# KUS Scale Specification (phase-05)

この文書は、`Scale.lean` で導入した最小の unit transport 仕様を要約する。

## 目的

- KUS の `coeff`（可視係数）を保持したまま、`US` / `KUS` の unit と blueprint を安全に移送する。
- 依存型として

$$
Blueprint\;u \to Blueprint'\;(mapUnit\;u)
$$

を明示し、`S_U` の unit 従属性を壊さない。

## Lean API

- `ScaleSpec U Blueprint V Blueprint'`
  - `mapUnit : U -> V`
  - `mapBlueprint : Blueprint u -> Blueprint' (mapUnit u)`
- `ScaleSpec.scaleUS`
- `ScaleSpec.scaleKUS`
- `ScaleSpec.idScale`
- `ScaleSpec.comp`

## 保証（phase-03 で固定）

- `toNat (scaleKUS σ x) = toNat x`
- `extract (scaleKUS σ x) = scaleUS σ (extract x)`
- `scaleKUS idScale x = x`
- `scaleKUS (comp τ σ) x = scaleKUS τ (scaleKUS σ x)`

## 追加保証（phase-05）

- `scaleKUS σ (Fiber.toKUS support n) = Fiber.toKUS (scaleUS σ support) n`
- `extract (scaleKUS σ (Fiber.toKUS support n)) = scaleUS σ support`
- `toNat` レベルでは、fixed fiber の加法と scale が整合する
  - `toNat (scaleKUS σ (Fiber.toKUS support (n + m)))`
  - `= toNat (scaleKUS σ (Fiber.toKUS support n)) + toNat (scaleKUS σ (Fiber.toKUS support m))`

これにより、「観測側の係数保持」と「構造保持側の transport」を分離したまま扱える。

## 範囲外

- 逆変換の存在（同型性）は仮定しない
- scale と演算（Monoid）を統合した高階法則はまだ導入しない
- 幾何モデルや具体 unit 系の transport は `Examples.lean` 側へ後送

## 次作業の候補

1. `Examples.lean` へ phase-05 補題の具体利用例を 1 つ追加
2. transport 後 fiber の型設計（Nat 別名のままにするか）を見直す
