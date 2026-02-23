# No Square on S0 Work Notes

status: 作業中 - phase-02: x=c-b, u=b を代入して `Gx 3 x u = S0_nat c b` へ落とす橋補題を作る

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md) - `hS0_not_sq` を `NoSqOnS0` に置換可能な構造にした。

## 状況

1. [ ] `CosmicFormulaBinom`（代数核）

   - まず `G` を明示定義して固定：
   - `((x+u)^d - u^d) = x * Gx d x u`
   - `((x+u)^d - x^d) = u * Gu d x u`
   - `q ∣ ((x+u)^d - u^d) ∧ ¬ q ∣ x -> q ∣ Gx d x u` を補題化

2. [ ] `PetalDetect`（d=3への射影）

   - `x=c-b, u=b` を代入し `Gx 3 x u = S0_nat c b` へ落とす橋補題を作る
   - ここで `NoSqOnS0` / `hS0_not_sq` に接続

3. [ ] `Core`（FLT本線）

   - 上の橋補題を使って `padicValNat` の上界補題へ流す

---

`CellDim` を経由するべきか？  

- **必須ではない**です（まずは不要）。  
- 幾何・単位構造（√2/√3、交差点、周期）を厳密化する段階で `CellDim` 層を追加するのがよいです。

> ※次のフェーズにする。

---

注意点（重要）

- `Gap := u^d` を「ノルム」と呼ぶのは概念としては良いですが、Leanでは先に**定義**が必要。
- 「succ が互いに異なる => 互いに素」「周期 = gcd」も、現状は直観なのでそのままは使えません。  
  先に `PetalCoreUnit` と `HarmonicPoint`（周期交差点）を述語で定義してから補題化するのが筋です。

必要なら次に、上の 1 → 2 の橋補題スケルトンを実際にファイルへ作成します。

## 2026-02-23 作業ログ（現時点まとめ）
