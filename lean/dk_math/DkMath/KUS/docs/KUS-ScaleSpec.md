# KUS Scale Specification (phase-10)

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

## 使用例（phase-07）

- `Examples.lean` に、phase-05 補題の具体利用を追加した
  - `toyScale_toKUS_comm`
  - `toyScale_extract_toKUS_comm`
  - `toyScale_toNat_add_comm`

これにより、`Scale` と `Monoid` の整合補題が「定義」だけでなく「実利用」でも確認できる状態になった。

## API 整理（phase-08）

- 既存名を壊さずに、整合補題の短い alias を追加した
  - `scale_toKUS`
  - `extract_scale_toKUS`
  - `toNat_scale_toKUS_add`

方針は「命名の薄い整理のみ」であり、既存定理名・既存利用はそのまま有効である。

## 適用判断（phase-09）

- `Examples.lean` の 3 箇所を alias 補題呼び出しへ置換した。
  - `ScaleSpec.scaleKUS_toKUS` -> `scale_toKUS`
  - `ScaleSpec.extract_scaleKUS_toKUS` -> `extract_scale_toKUS`
  - `ScaleSpec.toNat_scaleKUS_toKUS_add` -> `toNat_scale_toKUS_add`

この結果、長い修飾名を減らしつつ、理論内容は変えずに可読性だけ改善できることを確認した。

## 運用方針（phase-10）

- alias の標準適用範囲は `Examples.lean` までとする。
- コア理論層は既存の `ScaleSpec.*` 名を正準参照として維持する。
- 詳細は `KUS-AliasPolicy.md` に分離した。

これにより、「観測側の係数保持」と「構造保持側の transport」を分離したまま扱える。

## 範囲外

- 逆変換の存在（同型性）は仮定しない
- scale と演算（Monoid）を統合した高階法則はまだ導入しない
- 幾何モデルや具体 unit 系の transport は `Examples.lean` 側へ後送

## 次作業の候補

1. alias 命名規則の簡易ガイドを追加する
2. subtype fiber を再導入する場合の移行手順を docs へ切り出す
