# LPS: Lander, Parkin, and Selfridge conjecture

Samples related to the Lander, Parkin, and Selfridge conjecture.

## 関連資料

- **設計書**: [LPS-FLT-design.md](../../FLT/docs/LPS-FLT-design.md) — Big 族分解と Gap 反転構造の理論設計
- **実装メモ**: [LPS_Memo.md](./LPS_Memo.md) — Lean 実装の骨格案とアプローチ

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
