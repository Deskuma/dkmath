# No Square on S0 Work Notes

status: 作業中 - phase-02: x=c-b, u=b を代入して `Gx 3 x u = S0_nat c b` へ落とす橋補題を作る

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md) - `hS0_not_sq` を `NoSqOnS0` に置換可能な構造にした。

## 状況

1. [x] `CosmicFormulaBinom`（代数核）

   - まず `G` を明示定義して固定：
   - `((x+u)^d - u^d) = x * Gx d x u`
   - `((x+u)^d - x^d) = u * Gu d x u`
   - `q ∣ ((x+u)^d - u^d) ∧ ¬ q ∣ x -> q ∣ Gx d x u` を補題化

2. [x] `PetalDetect`（d=3への射影）

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

## 2026-02-23 追記（phase-02: Binom -> Petal の橋補題実装）

### 実施内容

- 新規: `lean/dk_math/DkMath/FLT/CosmicPetalBridge.lean`
  - `sub_eq_mul_GN`:
    - `(x+u)^d - u^d = x * GN d x u`（CosmicFormulaBinom の無減算形から導出）
  - `prime_dvd_GN_of_dvd_sub_not_dvd_left`:
    - `q ∣ ((x+u)^d - u^d)` かつ `¬ q ∣ x` から `q ∣ GN d x u`
  - `GN_three_sub_eq_S0_nat`:
    - `x=c-b, u=b` の d=3 射影 `GN 3 (c-b) b = S0_nat c b`
  - `prime_dvd_S0_via_cosmic_bridge`:
    - `q ∣ c^3-b^3` かつ `¬ q ∣ c-b` から `q ∣ S0_nat c b`

- 更新: `lean/dk_math/DkMath/FLT/PhaseLift.lean`
  - `import DkMath.FLT.CosmicPetalBridge` を追加
  - `hS0_not_sq_of_NoSqOnS0` 内の `q ∣ S0` 導出を
    `prime_dvd_S0_via_cosmic_bridge` に切り替え

### 検証

- `lake build DkMath.FLT.CosmicPetalBridge` 成功
- `lake build DkMath.FLT.Main` 成功（先に確認済み）

### 状態更新

- [x] 1. `CosmicFormulaBinom`（代数核）
- [x] 2. `PetalDetect`（d=3への射影）
- [ ] 3. `Core`（FLT本線での上界補題への本格統合）
