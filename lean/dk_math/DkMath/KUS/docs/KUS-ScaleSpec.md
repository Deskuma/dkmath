# KUS Scale Specification (phase-03)

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

これにより、「観測側の係数保持」と「構造保持側の transport」を分離したまま扱える。

## 範囲外

- 逆変換の存在（同型性）は仮定しない
- scale と演算（Monoid）を統合した高階法則はまだ導入しない
- 幾何モデルや具体 unit 系の transport は `Examples.lean` 側へ後送

## 次作業の候補

1. `Examples.lean` で toy blueprint の scale 例を追加
2. `Monoid` と `Scale` の相互作用（例: scale が加法を保存）を最小補題として追加
