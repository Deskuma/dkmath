# No Square on S0 Work Notes

status: 作業中 - phase-08:

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)

## 課題

- [x] なし

## 状況タスク

phase-08（A+B 合流）

## 実装方針（A+B 合流）

1. `¬ NoSqOnS0` の正規形を作る（`PhaseLift`）

   - `not_NoSqOnS0_iff_exists_sq_factor`
   - 形: `¬ NoSqOnS0 c b ↔ ∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q^2 ∣ S0_nat c b`

2. `q=3 / q≠3` 分岐補題を作る（`PhaseLift`）

   - `exists_sq_factor_split_three`
   - 形: 上の存在を `q=3` と `q≠3` に分解

3. `q≠3` 側を既存資産で潰す

   - `S0PrimeSupportExceptThree` + `AllNonLiftableOnS0` 系へ接続
   - 必要なら `phase6_s0PrimeSupportExceptThree` を再利用して矛盾化

4. `q=3` 側専用判定器（新規）

   - `v3` か `mod 9` で `3^2 ∣ S0_nat c b` の成立条件を明示
   - 補題名例: `three_square_factor_obstruction`（`mod 9` 分岐）

5. 合流定理を `Main` に追加

   - `by_cases hNoSq : NoSqOnS0 c b`
     - `hNoSq` 側: 既存 `...of_NoSqOnS0`
     - `¬hNoSq` 側: 新規 B 判定器

## まず着手すべき1本

最初はこれ。

- `not_NoSqOnS0_iff_exists_sq_factor`

これができると、B 判定器の入口が完全に安定します。  

## 作業ログ 2026/02/25  1:49 より

- phase-08 実装ステップ（補集合正規形の導入）
  - `PhaseLift.lean` に追加:
    - `not_NoSqOnS0_iff_exists_sq_factor`
      - `¬ NoSqOnS0 c b ↔ ∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b`
  - 位置づけ:
    - B ルート（`¬ NoSqOnS0` 側）の入口を存在形で固定。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  1:56 より

- phase-08 実装ステップ（`q=3 / q≠3` 分解）
  - `PhaseLift.lean` に追加:
    - `exists_sq_factor_split_three`
      - 入力:
        - `∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b`
      - 出力:
        - `(3 ^ 2 ∣ S0_nat c b) ∨ ∃ q, Nat.Prime q ∧ q ≠ 3 ∧ q ∣ S0_nat c b ∧ q ^ 2 ∣ S0_nat c b`
  - 実装内容:
    - 証人 `q` を取り、`by_cases hq3 : q = 3` で左右へ分岐するだけの正規分解を定義。

- build（今回）
  - `lake build DkMath.FLT.PhaseLift` : OK

## 作業ログ 2026/02/25  2:04 より

- phase-08 実装ステップ（Main 接続）
  - `Main.lean` に追加:
    - `FLT_d3_by_padicValNat_of_support_nonLiftable_mod3_separated`
      - 入力:
        - `hSuppEx3 : S0PrimeSupportExceptThree c b`
        - `hNonLift : ∀ q, NonLiftableS0 c b q`
        - `mod3` 分離 (`hc_nz`, `hb_nz`, `hsep`)
      - 流れ:
        - `NoSqOnS0_of_support_nonLiftable_mod3_separated` で `NoSqOnS0` を回復
        - 既存 `FLT_d3_by_padicValNat_of_NoSqOnS0` へ接続

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:28 より

- API 命名整理（`phase6` 用語の除去）
  - `PhaseLift.lean`
    - `structure Phase6NoSqInput` → `structure NoSqInput`
    - `phase6_s0PrimeSupportExceptThree` → `s0PrimeSupportExceptThree_of_NoSqInput`
  - `Main.lean`
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_phase6NoSqInput`
      → `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqInput`
    - `FLT_d3_by_padicValNat_of_phase6NoSqInput`
      → `FLT_d3_by_padicValNat_of_NoSqInput`
  - 互換マーク・非推奨注記は追加せず、そのまま新名称へ移行。

- ドキュメント更新
  - `FLT/README.md` の公開入口名・Mermaid ノード名を新名称へ更新
  - README タイトルから phase 表記を削除

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:17 より

- phase-08 リファクタ（互換ラッパー化）
  - `Main.lean` を整理:
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_phase6NoSqInput` を実装本体として維持
    - `FLT_d3_by_padicValNat_of_phase6NoSqInput` は互換シグネチャを保った薄い委譲に変更
      - `_hNoExcAll` は互換性維持のため受け取るが使用しない
  - 目的:
    - `phase6` 入口の実装経路を A+B 合流ルートへ一本化し、重複ロジックを除去。

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:13 より

- phase-08 リファクタ（旧入口の新合流ルート寄せ）
  - `Main.lean` の既存定理を更新:
    - `FLT_d3_by_padicValNat_of_phase6NoSqInput`
      - 旧: `...of_harmonicEnvelope_NoSq_coprimeSupport` へ接続
      - 新: `phase6_s0PrimeSupportExceptThree` / `nonLiftableS0_all_of_NoSqOnS0` で材料を作り、
        `FLT_d3_by_padicValNat_by_cases_NoSq` へ接続
      - 互換シグネチャ維持のため `hNoExcAll` は残す（実装上は未使用）
  - 効果:
    - phase6 系の入口も A+B 合流ルートへ統一。

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:10 より

- phase-08 実装ステップ（API 一本化ラッパー）
  - `Main.lean` に追加:
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_phase6NoSqInput`
      - `Phase6NoSqInput` から `phase6_s0PrimeSupportExceptThree` で `hSuppEx3` を生成
      - `nonLiftableS0_all_of_NoSqOnS0 hP6.hNoSq` で `hNonLift` を生成
      - `FLT_d3_by_padicValNat_by_cases_NoSq` へ直結
  - 位置づけ:
    - phase-06 入力束から A+B 合流ルートへ、`hNoExcAll` 非依存で接続。

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:06 より

- phase-08 実装ステップ（A+B 合流定理）
  - `Main.lean` に追加:
    - `FLT_d3_by_padicValNat_by_cases_NoSq`
      - `by_cases hNoSq : NoSqOnS0 c b` で分岐
      - A 側: `FLT_d3_by_padicValNat_of_NoSqOnS0`
      - B 側: `FLT_d3_by_padicValNat_of_support_nonLiftable_mod3_separated`
  - 位置づけ:
    - `NoSqOnS0` を中心にした入口合流を、定理として明示化。

- build（今回）
  - `lake build DkMath.FLT.Main` : OK

## 作業ログ 2026/02/25  2:03 より

- phase-08 実装ステップ（`q=3` 側 obstruction）
  - `PhaseLift.lean` に追加:
    - `three_sq_not_dvd_of_mod3_separated`
      - `c,b` が `mod 3` で非零かつ分離なら `¬ (3^2 ∣ S0_nat c b)` を示す。
    - `NoSqOnS0_of_support_nonLiftable_mod3_separated`
      - `hSuppEx3 + hNonLift + mod3 分離` から `NoSqOnS0 c b` を直接回復。
      - 証明は `¬ NoSq` を仮定して `three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable` で `3^2 ∣ S0` を得て矛盾。
  - 位置づけ:
    - B ルートの残差（`3` 側）を `mod3` 条件で閉じる橋を追加。

- build（今回）
  - `lake build DkMath.FLT.PhaseLift` : OK

## 作業ログ 2026/02/25  2:01 より

- phase-08 実装ステップ（`q≠3` 側の既存資産接続）
  - `PhaseLift.lean` に追加:
    - `not_exists_sq_factor_ne_three_of_support_nonLiftable`
      - `S0PrimeSupportExceptThree c b` と `∀ q, NonLiftableS0 c b q` があれば、
        `q ≠ 3` で `q^2 ∣ S0_nat c b` となる証人は存在しないことを示す。
    - `three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable`
      - `¬ NoSqOnS0 c b` を `exists_sq_factor_split_three` で分解し、
        `q≠3` 分岐を上補題で排除して `3^2 ∣ S0_nat c b` を抽出。
  - 位置づけ:
    - B ルートで「補集合は実質 `3` 側だけ残る」を Lean 上で明示化。

- build（今回）
  - `lake build DkMath.FLT.PhaseLift` : OK
