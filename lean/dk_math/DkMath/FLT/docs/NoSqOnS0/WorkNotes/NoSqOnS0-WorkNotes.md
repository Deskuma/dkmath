# No Square on S0 Work Notes

status: 作業中 - phase-15: 完全証明への道 (CosmicPetalBridgeGNNoWieferich: triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core)

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)
[NoSqOnS0: phase-08](NoSqOnS0-WorkNotes-phase-08.md)
[NoSqOnS0: phase-09](NoSqOnS0-WorkNotes-phase-09.md)
[NoSqOnS0: phase-10](NoSqOnS0-WorkNotes-phase-10.md)
[NoSqOnS0: phase-11](NoSqOnS0-WorkNotes-phase-11.md)
[NoSqOnS0: phase-12](NoSqOnS0-WorkNotes-phase-12.md)
[NoSqOnS0: phase-13](NoSqOnS0-WorkNotes-phase-13.md)
[NoSqOnS0: phase-14](NoSqOnS0-WorkNotes-phase-14.md)

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [x] ただし、`GEisensteinBridge` の `descent` インターフェースは実装済み。

## 状況タスク

- 完了条件（DoD）:
  - [ ] 1. `TriominoFLT.lean` に `sorry` がない。
  - [ ] 2. `FLT_highExponent_core_pending` が実装済み（または不要化）。
  - [ ] 3. `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT` が成功。
  - [ ] 4. 暫定依存の残有無をコメントとログに明示。
- 受け入れ条件:
  - [ ] 1. Bridge から `Main` の triomino 接続口へ実際に到達すること。
  - [ ] 2. `Main` 側既存 API（line 772 / 788）を変更せず接続できること。

## 計画

## 作業ログ

### 2026-03-04 phase-15 準備（NoWieferich 核を別ファイルへ移設）

- 対象:
  - 新規: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
- 変更:
  - 残る唯一の `sorry` である
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    を、新規ファイル `CosmicPetalBridgeGNNoWieferich.lean` へ移設
  - `CosmicPetalBridgeGNDescentB.lean` は新規ファイルを import し、
    Branch B の glue / bridge 側に専念する形へ整理
- 内容:
  1. `CosmicPetalBridgeGNDescentB.lean` は phase-14 の配線整理を保持したまま、研究対象の深い核だけを phase-15 用の別室へ分離した
  2. これにより、今後の新補題追加や試行錯誤は
     `CosmicPetalBridgeGNNoWieferich.lean`
     に局所化できる
