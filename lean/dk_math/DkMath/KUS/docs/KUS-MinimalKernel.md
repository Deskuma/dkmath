# KUS Minimal Kernel

この文書は、README の理論方針を phase-01 の Lean 実装へ対応付けるための短い設計メモである。

## 今回実装した対応

- `US`
  - `(U, S_U)` を保持する構造。
  - Lean では `DkMath.KUS.US` として実装。
- `KUS`
  - `(K, U, S_U)` を保持する構造。
  - Lean では `DkMath.KUS.KUS` として実装。
- `zeroState`
  - `(0, U, S_U)` を表す。
  - `support : US` を受けて構造保持零を返す。
- `toNat`
  - 観測的零の側、すなわち可視係数 `K` への forget。
- `extract`
  - 通常除法ではなく、構造保持側 `(U, S_U)` を取り出す特異操作。

## 今回固定した最小定理

- `toNat (ofNat support n) = n`
- `extract (ofNat support n) = support`
- `ofNat (extract x) (toNat x) = x`

これにより、README の

$$
\mathbb{N} \to \mathrm{KUS} \to \mathbb{N}
$$

という往復と、`extract` による構造回収が、Lean 上で最小核として明示された。

## 実装後の状況（phase-02）

- 固定 support fiber 上の加法可換モノイド構造を `DkMath/KUS/Monoid.lean` に追加した
  - `Fiber support := Nat`（phase-02 の最小実装）
  - `Fiber.toKUS`, `Fiber.toNat`
  - `Fiber` 上の `AddCommMonoid` instance

## まだ実装していないもの

- unit 変更に伴う transport / scale
- 一般 carrier への拡張
- 無限状態の扱い

## 次作業の候補

1. `Scale.lean` の前段として、unit transport の仕様だけを docs に固定する
2. `Examples.lean` 用に最小の toy blueprint を一つ作る
3. `Monoid` の API を必要最小限で命名整理する
