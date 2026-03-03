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

- [ ] phase-15 の深い数学核
  - [ ] `CosmicPetalBridgeGNNoWieferich.lean` の
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    を実装する
  - [ ] 具体的には、`TriominoNoWieferichBridge` を
    Branch B 文脈で供給する
- [x] phase-14 の配線整理
  - [x] `CosmicPetalBridgeGNDescentB.lean` は glue / bridge 側へ整理済み
  - [x] 残る `sorry` は phase-15 用の別ファイルへ隔離済み

## 状況タスク

- 完了条件（DoD）:
  - [ ] 1. `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
    に `sorry` がない
  - [ ] 2. `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
    が warning なしで成功
  - [ ] 3. `CosmicPetalBridgeGNDescentB.lean` は phase-15 でも no-`sorry` の配線側として維持される
  - [ ] 4. phase-15 の研究核と、その依存方針をログに明示
- 受け入れ条件:
  - [ ] 1. Branch B descent ルートが `TriominoNoWieferichBridge` の供給だけで閉じること
  - [ ] 2. `CosmicPetalBridgeGN.lean` / `TriominoCosmicGapInvariant.lean` の公開配線を変更せずに接続できること
  - [ ] 3. 新補題・試行錯誤は `CosmicPetalBridgeGNNoWieferich.lean` に局所化されること

## 計画

- 直近の主戦場:
  - `CosmicPetalBridgeGNNoWieferich.lean`
- 現在の唯一の未解決点:
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
- 直近の探索候補:
  - primitive prime + valuation (`padicValNat = 1`)
  - non-liftable / no-Wieferich bridge の既存 spine への接続
  - 必要なら上の存在命題をさらに Prop-level の補題へ分解
- 非目標（当面）:
  - `CosmicPetalBridgeGNDescentB.lean` の外壁 refactor 継続
  - explicit な `z'` 構成の再導入

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
