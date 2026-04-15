# Proof of the Uniqueness of Factorization - Main Chain Proof Note (Draft)

cid: 69becbd2-3f3c-83ab-97af-666a8f8f4fb3

## 1. 目的

本ノートは、`GN` 構造アプローチで実装した
「素因数分解の一意性」証明の主鎖を、
証明論文に近い形で記述するための草稿である。

---

## 2. 主張の形

最終目標は、自然数 `m n` に対して

- prime-power 除法判定が全素数で一致すれば `m = n`

を示すことである。

Lean 実装では、最終的に

- `unique_factorization_nat_via_prime_powers`

を核として利用する。

---

## 3. 主鎖（高レベル）

### 3.1 核定理

1. `factorization_eq_of_prime_pow_dvd_iff`
2. `unique_factorization_nat_via_prime_powers`

により、

- `∀ p k, p^k ∣ m ↔ p^k ∣ n`

から `m = n` を得る。

### 3.2 層分離

素数を `d` に関して分割する。

- 例外層: `q ∣ d`
- 非例外層: `q ∤ d`

この 2 層の比較を束ねると

- `unique_factorization_nat_via_split_prime_layers`

に接続できる。

---

## 4. GN 構造からの供給

`boundaryProd` / `kernelRight` を介して、
層ごとの比較入力を供給する。

### 4.1 例外層（`q ∣ d`）

- `hExcM` / `hExcK` / `hExcBK` を比較入力とする
- valuation 等式や不等式から prime-power 比較へ持ち上げる

### 4.2 非例外層（`q ∤ d`）

- `hNonExcM` / `hNonExcK` / `hNonExcBK` を比較入力とする
- non-overlap（境界と kernel の非競合）を主軸にする

---

## 5. valuation から prime-power への橋

基礎橋は

- `padicValNat_dvd_iff_le`

である。これにより

- valuation 等式/不等式

を

- prime-power 除法同値/片方向

へ変換する。

ここで GN 固有の寄与は、
valuation 法則を生むこと自体ではなく、

- どの対象対（boundary vs kernel）に法則を適用するか
- どの層条件（例外/非例外）で適用するか

を構造的に固定できる点にある。

---

## 6. facade 統一の意味

実装後半では、入力形の違いを facade で統一した。

- `NonExceptionalBridgeEntrance`
- `NonExceptionalBoundaryEntrance`

これにより

- Val/BK の違い
- boundaryProd/sides の違い

を公開 API から分離できる。

最終推奨入口:

- `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`

---

## 7. 主鎖の形式的まとめ

概念的には次の連鎖である。

1. GN 構造から層別比較入力を得る
2. valuation ↔ prime-power の橋で比較を正規化
3. 例外層/非例外層を合成
4. prime-power 全一致へ到達
5. 核定理で `m = n`

---

## 8. 既知の境界と注意点

- `compat/thin` ラッパーは互換維持のため残置
- 新規実装は推奨入口に集約
- 現状は Mathlib 依存のプロトタイプ実装だが、
  facade 設計により段階置換の余地を確保している

---

## 9. 論文化に向けた次項目

- 定理名対応表（Lean 名 ↔ 論文記法）
- 仮定最小化（どの仮定が本質か）
- 例外層/非例外層の独立節化
- 主要補題の依存 DAG 図

---

## 10. Lean 定理名 ↔ 論文記法（主鎖視点）

| Lean 名 | 論文記法（提案） | 主鎖での役割 |
|---|---|---|
| `factorization_eq_of_prime_pow_dvd_iff` | \(\mathbf{FacEq}_{\mathrm{pow}}\) | `∀ p,k` の prime-power 同値から `factorization` 一致を導く |
| `unique_factorization_nat_via_prime_powers` | \(\mathbf{UF}_{\mathrm{pow}}\) | `∀ p,k` 同値から `m=n` を導く核定理 |
| `factorization_eq_of_prime_pow_dvd_iff_split_layers` | \(\mathbf{FacEq}_{\mathrm{split}}\) | 例外層/非例外層を合成して `factorization` 一致へ接続 |
| `unique_factorization_nat_via_split_prime_layers` | \(\mathbf{UF}_{\mathrm{split}}\) | 層別比較（Exc/NonExc）を合成して `m=n` |
| `exceptionalPowComparison_of_padicValNat_eq` | \(\mathbf{PowCmp}_{\mathrm{Exc}}^{v}\) | 例外層で `v_q` 等式を prime-power 同値へ変換 |
| `nonExceptionalPowComparison_of_padicValNat_eq` | \(\mathbf{PowCmp}_{\neg\mathrm{Exc}}^{v}\) | 非例外層で `v_q` 等式を prime-power 同値へ変換 |
| `exceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight` | \(\mathbf{BK}_{\mathrm{Exc}}^{v}\) | 例外層の `boundaryProd ↔ kernelRight` prime-power 比較 |
| `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight` | \(\mathbf{BK}_{\neg\mathrm{Exc}}^{v}\) | 非例外層の `boundaryProd ↔ kernelRight` prime-power 比較 |
| `exceptionalM_of_padicValNat_eq_m_boundaryProd` | \(\mathbf{M}_{\mathrm{Exc}}^{v}\) | 例外層 `m ↔ boundaryProd` 供給 |
| `exceptionalK_of_padicValNat_eq_n_kernelRight` | \(\mathbf{K}_{\mathrm{Exc}}^{v}\) | 例外層 `n ↔ kernelRight` 供給 |
| `nonExceptionalM_of_padicValNat_eq_m_boundaryProd` | \(\mathbf{M}_{\neg\mathrm{Exc}}^{v}\) | 非例外層 `m ↔ boundaryProd` 供給 |
| `nonExceptionalK_of_padicValNat_eq_n_kernelRight` | \(\mathbf{K}_{\neg\mathrm{Exc}}^{v}\) | 非例外層 `n ↔ kernelRight` 供給 |
| `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK` | \(\mathbf{UF}_{\mathrm{GN}}^{\mathrm{final}}\) | 主鎖最終入口（facade 統合） |

---

## 11. 記号定義の一貫性チェック（`Exc` / `NonExc`）

主鎖記述で `Exc` / `NonExc` の意味が揺れないことを確認する。

### 11.1 チェック規約

1. 例外層は `Exc` で統一し、条件は常に `q ∣ d`。
2. 非例外層は `NonExc` または `\neg\mathrm{Exc}` で統一し、条件は常に `q ∤ d`。
3. 例外層比較補題は `...Exceptional...` / `_{Exc}`、
   非例外層比較補題は `...nonExceptional...` / `_{\neg Exc}` に対応させる。
4. split 合成（`UF_split`）では、`Exc` / `NonExc` の両層が同時に必要であることを明示する。

### 11.2 主鎖での整合結果

| 対象 | 判定 | 確認内容 |
|---|---|---|
| `PowCmp_Exc^v` / `PowCmp_{¬Exc}^v` | OK | 条件がそれぞれ `q ∣ d` / `q ∤ d` で固定 |
| `BK_Exc^v` / `BK_{¬Exc}^v` | OK | boundary-kernel 比較が層別に分離 |
| `M_Exc^v, K_Exc^v` と `M_{¬Exc}^v, K_{¬Exc}^v` | OK | `m/n` 側供給が層別記法と一致 |
| `UF_split` | OK | 例外層と非例外層の合成として記述 |
| `UF_GN^final` | OK | facade 入口で層意味が混線しない |
