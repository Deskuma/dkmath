# LPS: Lander, Parkin, and Selfridge conjecture

Samples related to the Lander, Parkin, and Selfridge conjecture.

## 関連資料

- **設計書**: [LPS-FLT-design.md](../../FLT/docs/LPS-FLT-design.md) — Big 族分解と Gap 反転構造の理論設計
- **実装メモ**: [LPS_Memo.md](./LPS_Memo.md) — Lean 実装の骨格案とアプローチ
- **研究ノート**: [ObservedMinProfile-ResearchNote.md](./docs/ObservedMinProfile-ResearchNote.md) — observed minimum profile 分岐の実験記録

## Lean コード構成

### [BigFamily.lean](./BigFamily.lean)

Big-family 分解の基本定義と定理。

- `big d x u` : 完成全体 = `(x + u)^d`
- `gap d x u` : 単位核 = `u^d`
- `body d x u` : 本体 = `big - gap`
- `core d x u` : 主核 = `x^d`
- `beam d x u` : 残差 = `body - core`

主な定理:

- `big = body + gap`
- `body = core + beam`
- `big = core + beam + gap`

### [BigFamilyInt.lean](./BigFamilyInt.lean)

Big-family 分解の `ℤ` 版。

- `big / gap / body / core / beam / residual` を整数で定義
- `ℤ` の減算構造を使った等式復元を確認

### [BigFamilyExamples.lean](./BigFamilyExamples.lean)

Big-family と Fillability を接続する観測標本集。

- `ObservedMinOne / ObservedMinTwo`（局所定義）
- same Big で observed minimum profile が分岐する標本
- `d = 3` の 3 標本を束ねる総括定理

### [PowerSwap.lean](./PowerSwap.lean)

反転指数交点 `a^b = b^a` の定義と性質。

- `PowerSwap a b` : `a^b = b^a` という述語
- `powerSwap_two_four` : `2^4 = 4^2 = 16` の古典例

### [GapFillRank.lean](./GapFillRank.lean)

Gap 充填可能性と FillRank の定義・基本例。

- `FillableByPowSumExact d n r` : `n = ∑ (f i)^d` (r 個の d 乗和)
- `FillableByPowSumLE d n r` : `n` が最大 r 個で埋まるか
- `ResidualFillableExact` : Big と Body の残差が埋まるか

## 設計の中核

Big を固定しながら内部構造を観測する:

\[
\mathrm{Big} = \mathrm{Core} + \mathrm{Beam} + \mathrm{Gap}
\]

反転指数交点 (`a^b = b^a`) が成り立つ時、
**Big は不変のまま、内部役割が反転し、FillRank が変動しうる**
というのが本研究の中心仮説です。
