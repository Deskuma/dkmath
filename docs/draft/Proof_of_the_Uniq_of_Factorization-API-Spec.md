# Proof of the Uniqueness of Factorization - API Specification (Draft)

cid: 69becbd2-3f3c-83ab-97af-666a8f8f4fb3

## 1. 目的

本仕様書は、`DkMath.NumberTheory.UniqueFactorizationGN` の公開 API を、
呼び出し側視点で固定するためのドラフトである。

- 最終推奨入口を明確化する
- facade 入口の意味と使い分けを明確化する
- 互換 wrapper（`compat/thin`）と推奨 API を分離する

---

## 2. スコープ

対象モジュール:

- `DkMath.NumberTheory.UniqueFactorizationGN`
- `DkMath.Samples.UniqueFactorizationGNFacade`（呼び出し例）

---

## 3. 用語と facade 型

### 3.1 `NonExceptionalBridgeEntrance d x u`

非例外層（`q ∤ d`）で、次のどちらかを受ける facade。

- valuation 等式入力（`hNonExcVal`）
- prime-power 同値入力（`hNonExcBK`）

constructor:

- `nonExceptionalBridgeEntrance_of_nonExcVal`
- `nonExceptionalBridgeEntrance_of_nonExcBK`

### 3.2 `NonExceptionalBoundaryEntrance d x u`

非例外層境界で、次のどちらかを受ける facade。

- `boundaryProd` の非除法入力
- `boundaryRight/Left` の非除法入力

constructor:

- `nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd`
- `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides`

---

## 4. 推奨入口（優先順）

### 4.1 最終推奨入口（A/B/C 完全版）

`unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`

用途:

- 例外層・非例外層ともに `m/n` 側比較を valuation 入力で与える場合
- 非例外 bridge は facade（Val/BK どちらでも可）で与える
- 非例外 boundary も facade で与える

出力:

- `m = n`

### 4.2 準推奨入口（例外層のみ auto）

`unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcMK`

用途:

- `hExcM/hExcK` は valuation から自動生成したい
- 非例外 `hNonExcM/hNonExcK` は既に手元にある

### 4.3 下位推奨入口（prime-power 比較入力直結）

`unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcFacade_boundaryFacade`

用途:

- 例外/非例外ともに `h*M/h*K`（prime-power 比較）を直接持つ

---

## 5. `compat/thin` 層

branch-specific な旧公開名は互換維持で残すが、
docstring で `compat/thin` を明示し、内部は推奨入口へ委譲する。

代表例:

- `...nonExcVal_boundaryFacade...`
- `...nonExcBK_boundaryFacade...`
- `...nonExcVal_boundarySides`
- `...nonExcBK_boundaryProd`
- `...nonExcVal_boundaryProd`

方針:

- 既存呼び出しは壊さない
- 新規呼び出しは推奨入口へ寄せる

---

## 6. 呼び出し導線（最小）

参照サンプル:

- `DkMath.Samples.UniqueFactorizationGNFacade`

最短導線:

1. `hNonExcVal` か `hNonExcBK` から `NonExceptionalBridgeEntrance` を作る
2. `hNonExcNotDvdBoundaryProd` または sides 入力から `NonExceptionalBoundaryEntrance` を作る
3. 4.1 の最終推奨入口を呼ぶ

---

## 7. 依存境界（将来独立化の観点）

現状は Mathlib 依存を含むプロトタイプ実装である。
ただし、依存の多くは wrapper/bridge で局所化済み。

独立化（`DkMathlib`）に向けた原則:

- 呼び出し面は facade API を維持
- 内部実装（Mathlib 依存補題）を段階置換
- `compat/thin` 層は移行期間の緩衝材として維持

---

## 8. 今後の更新ルール（草案）

- 新しい公開入口を追加した場合:
  - 本仕様書の「4. 推奨入口」に追記
  - 旧入口が互換層化された場合は「5. `compat/thin` 層」に追記
- `Samples` の導線変更時:
  - 「6. 呼び出し導線（最小）」を更新

---

## 9. Lean 定理名 ↔ 論文記法（API 視点）

| Lean 名 | 論文記法（提案） | 意味/用途 |
|---|---|---|
| `NonExceptionalBridgeEntrance d x u` | \(\mathsf{Bridge}_{\neg\mathrm{Exc}}(d;x,u)\) | 非例外層 bridge 入力の facade（Val/BK の和） |
| `NonExceptionalBoundaryEntrance d x u` | \(\mathsf{Boundary}_{\neg\mathrm{Exc}}(d;x,u)\) | 非例外層 boundary 入力の facade（Prod/Sides の和） |
| `nonExceptionalBridgeEntrance_of_nonExcVal` | \(\mathsf{Bridge}^{\mathrm{Val}}_{\neg\mathrm{Exc}}\) | `hNonExcVal` から bridge facade を構成 |
| `nonExceptionalBridgeEntrance_of_nonExcBK` | \(\mathsf{Bridge}^{\mathrm{BK}}_{\neg\mathrm{Exc}}\) | `hNonExcBK` から bridge facade を構成 |
| `nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd` | \(\mathsf{Boundary}^{\mathrm{Prod}}_{\neg\mathrm{Exc}}\) | `boundaryProd` 非除法から boundary facade を構成 |
| `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides` | \(\mathsf{Boundary}^{\mathrm{Sides}}_{\neg\mathrm{Exc}}\) | `boundaryRight/Left` 非除法から boundary facade を構成 |
| `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK` | \(\mathbf{UF}_{\mathrm{GN}}^{\mathrm{final}}\) | 最終推奨入口（A/B/C 統合） |
| `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcMK` | \(\mathbf{UF}_{\mathrm{GN}}^{\mathrm{autoExc}}\) | 例外層 `M/K` 自動供給付きの準推奨入口 |
| `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcFacade_boundaryFacade` | \(\mathbf{UF}_{\mathrm{GN}}^{\mathrm{primePow}}\) | prime-power 比較入力を直接受ける下位入口 |
