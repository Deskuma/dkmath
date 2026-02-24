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

phase-07（ドキュメント）

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
