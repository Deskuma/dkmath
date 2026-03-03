# No Square on S0 Work Notes

status: 作業中 - phase-15: valuation spine の statement repair (ZsigmondyCyclotomicResearch: squarefree_implies_padic_val_le_one は現状強すぎる)

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

- [ ] phase-15 の深い数学核（research spine）
  - [ ] `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` の
    `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
    の statement を修正する（現状の一般形は反例があり強すぎる）
  - [ ] その結果として
    `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
    を正しい statement へ差し替え、valuation spine を no-`sorry` 化する
- [x] phase-15 の local bridge 接続
  - [x] `CosmicPetalBridgeGNNoWieferich.lean` は local `sorry` を持たず、
    valuation spine への委譲だけで閉じる
  - [x] `CosmicPetalBridgeGNDescentB.lean` / `CosmicPetalBridgeGN.lean` /
    `TriominoCosmicGapInvariant.lean` の公開配線は維持済み

## 状況タスク

- 完了条件（DoD）:
  - [x] 1. `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
    に local `sorry` がない
  - [ ] 2. `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
    の `squarefree_implies_padic_val_le_one`
    を削除または正しい statement に置き換え、その結果 `sorry` がない
  - [ ] 3. `cd lean/dk_math && lake build DkMath.NumberTheory.ZsigmondyCyclotomicResearch DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
    が warning なしで成功
  - [x] 4. `CosmicPetalBridgeGNDescentB.lean` は phase-15 でも no-`sorry` の配線側として維持される
  - [x] 5. phase-15 の研究核と、その依存方針をログに明示
- 受け入れ条件:
  - [x] 1. Branch B descent ルートが `TriominoNoWieferichBridge` の供給だけで閉じること
  - [x] 2. `CosmicPetalBridgeGN.lean` / `TriominoCosmicGapInvariant.lean` の公開配線を変更せずに接続できること
  - [ ] 3. 新補題・試行錯誤は実質的に
    `ZsigmondyCyclotomicResearch.lean` の valuation spine
    （必要ならその薄い wrapper として `CosmicPetalBridgeGNNoWieferich.lean`）
    に局所化されること

## 計画

- 直近の主戦場:
  - `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
- 現在の唯一の未解決点:
  - `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
    （現状の命題は反例があり、証明ではなく statement repair が必要）
- 直近の探索候補:
  - primitive prime divisor の valuation を 1 に抑える、より狭い正しい statement への置換
  - `padicValNat_dvd_iff_le` を介した `¬ q^2 ∣ ...` との往復を補助補題化
  - `ZsigmondyCyclotomic.lean` / `DiffPow.lean` 側の squarefree・primitive prime 補題の再利用
- 非目標（当面）:
  - `CosmicPetalBridgeGNDescentB.lean` の外壁 refactor 継続
  - `CosmicPetalBridgeGNNoWieferich.lean` に新しい深い数学核を戻すこと
  - explicit な `z'` 構成の再導入
  - 反例がある現行 statement をそのまま証明しようとすること

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

### 2026-03-04 phase-15 継続（NoWieferich は合成だけで閉じる）

- 対象:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
- 変更:
  - `CosmicPetalBridgeGNNoWieferich.lean` では、`TriominoNoWieferichBridge` を
    直接 `sorry` で置くのをやめた
  - 代わりに
    `triominoNoWieferichBridge_of_descent (hDesc : WieferichDescentB)`
    を定義し、
    Core にある no-`sorry` 合成
    (`counterexampleHasWieferichLiftB_impl`,
    `wieferichLiftExclusion_of_liftExists_and_descent`,
    `triominoNoWieferichBridge_of_wieferichLiftExclusion`)
    だけで閉じる形に変更
  - `CosmicPetalBridgeGNDescentB.lean` 側には、
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    を thin wrapper として戻し、
    `triominoNoWieferichBridge_of_descent triominoWieferichDescent_impl`
    に委譲
- 内容:
  1. phase-15 の「深い数学核」と見ていた `NoWieferich` は、現時点の依存関係では
     追加研究なしの最終合成で閉じることが判明した
  2. これにより、`NoWieferich.lean` / `DescentB.lean` から `sorry` は消える見込みになった

### 2026-03-04 phase-15 継続（定義順制約を確認し、NoWieferich stub は維持）

- 対象:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
- 確認:
  - `triominoNoWieferichBridge_of_descent (hDesc : WieferichDescentB)` は
    Core の no-`sorry` 合成だけで実装できる
  - ただし `DescentB` 内の no-arg 利用箇所はファイル前半にあり、
    `triominoWieferichDescent_impl`（ファイル末尾）を使う no-arg 定理を
    その位置で供給することは、現行の定義順ではできない
- 対応:
  1. `CosmicPetalBridgeGNNoWieferich.lean` に
     `triominoNoWieferichBridge_of_descent`
     を追加（no-`sorry`）
  2. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
     は phase-15 の stub として維持
  3. `DescentB` 側は local な no-arg 再定義を置かず、
     import した stub をそのまま使う形に戻した
  4. あわせて
     `triominoWieferichDescent_impl`
     は
     `triominoWieferichDescent_impl_of_core triominoWieferichDescentCoreB_impl`
     と明示適用へ修正

## 2026-03-04 phase-15 継続（NoWieferich stub を valuation 上界へ分解）

- 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `triominoNoWieferichBridge_of_padicValNat_le_one`
    - `padicValNat q (z^p - y^p) ≤ 1` から `TriominoNoWieferichBridge` を作る no-`sorry` glue を追加
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core`
    - phase-15 の最小研究核として追加
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    - 直接 `sorry` を持つ形をやめ、上の valuation 上界補題へ委譲する薄い殻に変更

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - いずれも成功

- 現在の唯一の `sorry`:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core`

- 意味:
  - phase-15 の研究核は、`TriominoNoWieferichBridge` 全体ではなく
    「primitive prime divisor 文脈で `padicValNat q (z^p - y^p) ≤ 1` をどう供給するか」
    というより小さい Prop-level の上界補題に圧縮された。

## 2026-03-04 phase-15 継続（valuation 研究核を diff から GN に押し込む）

- 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `open DkMath.CosmicFormulaBinom`
    - `GN` をこのファイル内で正しく参照できるように修正
  - `triominoWieferichShrink_padicValNat_diff_eq_GN_core`
    - Branch B の primitive prime 文脈で
      `padicValNat q (z^p - y^p) = padicValNat q (GN p (z - y) y)`
      を no-`sorry` で追加
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core`
    - 新しい最小研究核として追加
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_le_one_core`
    - 直接 `sorry` を持つ形をやめ、上の `GN` 側上界補題へ委譲する no-`sorry` wrapper に変更

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - いずれも成功

- 現在の唯一の `sorry`:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core`

- 意味:
  - phase-15 の研究核は、もはや `z^p - y^p` の valuation 上界そのものではなく、
    `GN p (z - y) y` に対する primitive prime の 2 段 lift をどう禁止するか、
    という `NonLiftableGN` そのものの形へ揃った。

## 2026-03-04 phase-15 継続（primitive-prime valuation の型へ合わせて再圧縮）

- 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core`
    - 新規追加
    - phase-15 の最小研究核を、既存の primitive-prime valuation 補題と同型の
      `padicValNat q (z^p - y^p) ≤ 1`
      形へ明示的に切り出した
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core`
    - 直接 `sorry` を持つ形をやめ、
      diff 版上界 + `triominoWieferichShrink_padicValNat_diff_eq_GN_core`
      から従う no-`sorry` wrapper に変更
  - `triominoNoWieferichBridge_of_padicValNat_le_one`
    - 未使用だった `hpow_pos` を除去

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - いずれも成功

- 現在の唯一の `sorry`:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core`

- 意味:
  - 残る研究核は、既存の `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
    と同型の statement に揃った。
  - したがって phase-15 では、
    「既存 valuation spine をここへどう接続するか」
    だけに集中できる。

## 2026-03-04 phase-15 継続（local no-`sorry` 化、残核は research spine へ移動）

- 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `import DkMath.NumberTheory.ZsigmondyCyclotomicResearch`
    を追加
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core`
    を、local `sorry` ではなく
    `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
    への委譲に変更

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - いずれも成功

- 現在の warning:
  - `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:14`
  - `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
  - `declaration uses sorry` 1件のみ

- 意味:
  - `CosmicPetalBridgeGNNoWieferich.lean` は local `sorry` を持たない、純粋な bridge / wrapper になった
  - phase-15 の未解決数学は、`NoWieferich` 側の局所 stub ではなく、
    valuation spine の根である
    `squarefree_implies_padic_val_le_one`
    に移った
  - 以後の研究対象は、実質
    `ZsigmondyCyclotomicResearch.lean`
    の squarefree / valuation コアである

## 2026-03-04 phase-15 継続（research theorem は証明待ちではなく statement repair 待ち）

- 更新:
  - `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`

- 事実認定:
  - `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
    は現状の一般形では強すぎ、反例があることが判明した
  - したがって、ここでやるべきことは `sorry` をそのまま埋めることではなく、
    statement を必要な仮定付きの正しい形へ修正することである

- 反映:
  - research file の theorem comment を、証明待ちではなく
    「statement repair が必要な placeholder」である旨に修正
  - `CosmicPetalBridgeGNNoWieferich.lean` 側にも、
    local bridge は正しいが上流の valuation spine は placeholder 依存であることを明記

- 意味:
  - phase-15 の残核は「ある theorem を証明する」ではなく、
    「false な一般命題を、primitive-prime 文脈に十分な正しい命題へ置き換える」
    という research task に変わった
  - 以後の作業は、`ZsigmondyCyclotomicResearch.lean` で
    squarefree / primitive-prime / valuation のどの条件が最小で必要かを詰める
