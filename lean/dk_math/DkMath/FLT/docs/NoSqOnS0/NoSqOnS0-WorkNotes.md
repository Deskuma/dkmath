# No Square on S0 Work Notes

status: 作業中 - phase-07: ドキュメント branch: `dev/flt-refactoring-phase7-260224-v0`

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)

## 課題

- [x] なし

## 状況タスク

phase-07（ドキュメント）
[README.md](../../README.md) のドキュメントを最新コードベースに合わせて更新（刷新）する。

- [x] 1. Mermaid 図の再生成
  - 現行コードベースに合わせて補題チェーン図を更新
- [x] 2. README.md のドキュメント刷新
  - Mermaid 図を最新に差し替え
  - 定理や補題の説明文を現行コードに合わせて更新
  - 全体の構成や流れも必要に応じて見直し

## 作業ログ 2026/02/24  5:16 より

- phase-07 実装ステップ（README の刷新）
  - `DkMath/FLT/README.md` を現行コードベースに合わせて再編。
  - 内容を以下へ更新:
    - モジュール責務（`Main` / `PhaseLift` / `CounterexamplePattern`）
    - 推奨導線（`NoSqOnS0` / classify）
    - phase-06 入口（`Phase6NoSqInput`）
    - メンテ方針

- phase-07 実装ステップ（Mermaid 図の再生成）
  - README に「補題チェーン（Mermaid）」を追加。
  - 主要導線:
    - `CosmicFormulaBinom -> PhaseLift`
    - `PhaseLift -> Main`
    - `CounterexamplePattern -> Main`

- build（再確認）
  - ドキュメント更新のみ（ビルド対象の Lean ファイル変更なし）

## 補題チェーン（Mermaid）

README と同一内容を記録（更新時は両方を同期）。

```mermaid
graph LR
  A["CosmicFormulaBinom.two_gap_xy_factor*"] --> B["PhaseLift.two_gap_xy_dvd_cube_bridge"]
  C["CosmicPetalBridge.prime_dvd_S0_via_cosmic_bridge"] --> D["PhaseLift.prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff"]
  E["PhaseLift.cube_sub_eq_mul_sub_S0"] --> D
  F["PhaseLift.exists_prime_factor_cube_diff_of_three_dvd_sub"] --> G["PhaseLift.exists_prime_factor_cube_diff"]
  H["PhaseLift.exists_prime_factor_cube_diff_of_not_three_dvd_sub"] --> G
  I["PhaseLift.padicValNat_lower_bound_of_dvd_d3"] --> J["Main.FLT_d3_by_padicValNat"]
  K["PhaseLift.padicValNat_upper_bound_d3"] --> J
  G --> J
  L["PhaseLift.hS0_not_sq_of_NoSqOnS0"] --> M["Main.FLT_d3_by_padicValNat_of_NoSqOnS0"]
  J --> M
  N["PhaseLift.Phase6NoSqInput"] --> O["Main.FLT_d3_by_padicValNat_of_phase6NoSqInput"]
  M --> O
  P["CounterexamplePattern.classifyLift_impossible_family_of_harmonicEnvelope_NoSq"] --> Q["Main.FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport"]
  M --> Q
```
