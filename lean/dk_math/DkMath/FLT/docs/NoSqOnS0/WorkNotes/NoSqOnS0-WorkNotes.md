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

- [ ] phase-15 の供給者実装（PrimeProvider 層）
  - [ ] `DkMath.FLT.TriominoSquarefreeGNBridge` を PrimeProvider 層でどこが供給するか確定する
  - [ ] その供給から
    `DkMath.FLT.triominoNoWieferichBridge_of_squarefree_GN`
    を使って `TriominoNoWieferichBridge` を本流で閉じる
- [ ] 研究補題の整理（本流ではない）
  - [ ] `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean` の
    false placeholder
    `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one`
    は statement repair / 移設対象として管理する
  - [ ] `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
    は将来、適切な常設モジュールへ統合される正しい theorem に差し替える
- [x] phase-15 の local bridge 接続
  - [x] `CosmicPetalBridgeGNNoWieferich.lean` は local `sorry` を持たず、
    bridge 仕様の受け口だけを持つ
  - [x] `CosmicPetalBridgeGNDescentB.lean` / `CosmicPetalBridgeGN.lean` /
    `TriominoCosmicGapInvariant.lean` の公開配線は維持済み

## 状況タスク

- 完了条件（DoD）:
  - [x] 1. `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
    に local `sorry` がない
  - [ ] 2. `DkMath.FLT.TriominoSquarefreeGNBridge` の供給者が PrimeProvider 層で確定し、
    `TriominoNoWieferichBridge` が false placeholder を経由せずに閉じる
  - [ ] 3. `cd lean/dk_math && lake build DkMath.NumberTheory.ZsigmondyCyclotomicResearch DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
    が warning なしで成功
  - [x] 4. `CosmicPetalBridgeGNDescentB.lean` は phase-15 でも no-`sorry` の配線側として維持される
  - [x] 5. phase-15 の bridge 仕様と、Research が本流ではないことをログに明示
- 受け入れ条件:
  - [x] 1. Branch B descent ルートが `TriominoNoWieferichBridge` の供給だけで閉じること
  - [x] 2. `CosmicPetalBridgeGN.lean` / `TriominoCosmicGapInvariant.lean` の公開配線を変更せずに接続できること
  - [ ] 3. 新補題・試行錯誤は
    PrimeProvider 層の bridge 供給者に局所化され、
    `ZsigmondyCyclotomicResearch.lean` は一時的な proving ground としてのみ参照されること

## 計画

- 直近の主戦場:
  - PrimeProvider 層で `DkMath.FLT.TriominoSquarefreeGNBridge` の供給者をどう置くか
- 現在の設計上の不足点:
  - 本流が必要とする honest 条件は
    `Squarefree (GN p (z - y) y)`
    であり、これは
    `DkMath.FLT.TriominoSquarefreeGNBridge`
    として型に切り出し済み
- 直近の探索候補:
  - `TriominoSquarefreeGNBridge` を PrimeProvider 層の新しい bridge 仮定として受けるか、
    既存の PrimeProvider 理論から導くかの確定
  - `padicValNat_primitive_prime_factor_le_one_of_squarefree_G` への接続を本流へ昇格させる薄い補題の整備
  - `ZsigmondyCyclotomicResearch.lean` 上の true stronger theorem を、解決後にどの常設モジュールへ統合するかの見取り図を保つ
- 非目標（当面）:
  - `CosmicPetalBridgeGNDescentB.lean` の外壁 refactor 継続
  - `CosmicPetalBridgeGNNoWieferich.lean` に新しい深い数学核を戻すこと
  - explicit な `z'` 構成の再導入
  - 反例がある現行 statement をそのまま証明しようとすること
  - Research ファイルを本流の恒久的な供給者とみなすこと

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

## 2026-03-04 phase-15 継続（true な stronger theorem を Research に追加）

- 更新:
  - `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`

- 追加:
  - `DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree`
  - `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G`

- 内容:
  - 偽である一般 placeholder
    `squarefree_implies_padic_val_le_one`
    はそのまま残しつつ、
    実際に真である stronger theorem を別名で追加した
  - `padicValNat_le_one_of_squarefree` は
    `Squarefree n` と `n ≠ 0` から
    `padicValNat q n ≤ 1`
    を返す純算術の橋
  - `padicValNat_primitive_prime_factor_le_one_of_squarefree_G` は
    primitive-prime 文脈に
    `Squarefree (GN d (a - b) b)`
    を足すことで、`padicValNat q (a ^ d - b ^ d) ≤ 1` を返す

- 意味:
  - phase-15 の research は、もう「偽な一般定理を埋める」ことではない
  - これからは
    「どの追加仮定を downstream が受け入れるか」
    を決めて、
    local bridge をこの true な stronger theorem へ繋ぎ替える設計判断に移った

### 2026-03-04 phase-15 補助（BinomTail を CosmicFormulaBinom へ接続）
- `DkMath/Algebra/BinomTail.lean` の mixed-term positivity 補題を `DkMath/CosmicFormula/CosmicFormulaBinom.lean` に接続。
- 追加:
  - `add_pow_ne_sum_pows_nat_of_two_le_binom`
  - `add_pow_gt_sum_pows_nat_of_two_le_binom`
- 内容:
  - `2 ≤ d`, `x,u > 0` のとき `(x + u)^d` は `x^d + u^d` に一致せず、しかも真に大きいことを、`CosmicFormulaBinom` の語彙で直接参照できるようにした。
- これは phase-15 の主核ではないが、`G / GN` のような中間層が必要であることをコード上で言い表す補助道具として整備した。
- 確認: `cd lean/dk_math && lake env lean DkMath/CosmicFormula/CosmicFormulaBinom.lean` 成功。

## 2026-03-04 phase-15 継続（NoWieferich に squarefree-GN の正直な入口を追加）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`

- 追加:
  - `DkMath.FLT.triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core`
  - `DkMath.FLT.triominoNoWieferichBridge_of_squarefree_GN`

- 内容:
  - `Squarefree (GN p (z - y) y)` を仮定すれば、research 側の true な stronger theorem
    `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
    を直接使って
    `padicValNat q (z ^ p - y ^ p) ≤ 1`
    が得られる入口を追加した。
  - これにより、phase-15 の不足仮定はコード上で明示的になった。
    いま欠けているのは一般定理の証明ではなく、
    `Squarefree (GN ...)` をどこで供給するか、という設計上の次段だけである。

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich`
  - どちらも成功。残る warning は `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:69` の false placeholder 1 件のみ。

## 2026-03-04 phase-15 継続（Squarefree(GN) を bridge 仕様として型へ切り出し）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`

- 追加:
  - `DkMath.FLT.TriominoSquarefreeGNBridge`

- 内容:
  - `Squarefree (GN p (z - y) y)` を、ad hoc な追加仮定ではなく
    phase-15 の honest bridge 仕様として `Prop` に切り出した。
  - `triominoNoWieferichBridge_of_squarefree_GN` は、この新しい bridge 仕様を受ければ
    false な一般 placeholder を経由せずに no-`sorry` で閉じる。
  - これで phase-15 の不足仮定は「どの条件が要るか」が型で固定された。

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - 成功。

## 2026-03-04 phase-15 継続（PrimeProvider が供給者、Research は proving ground と明記）

- 方針更新:
  - `DkMath.FLT.TriominoSquarefreeGNBridge` の供給者は PrimeProvider 層に置く。
  - `ZsigmondyCyclotomicResearch.lean` は、false placeholder の洗い替えと true stronger theorem の試作を行う proving ground であり、本流の恒久的な供給者とはみなさない。

- 意味:
  - phase-15 の設計は「Research を直接下流へ繋ぎ続ける」ことではなく、
    PrimeProvider 層で honest bridge を受ける / 供給する形へ収束させる。
  - Research 側の補題は、sorry 解決後に適切な常設モジュールへ統合する前提で扱う。

## 2026-03-04 phase-15 継続（PrimeProvider 層に Squarefree-GN 供給者の器を追加）

- 新規:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProvider.lean`

- 追加:
  - `DkMath.FLT.TriominoSquarefreeGNBridgeProvider`
  - `DkMath.FLT.triominoNoWieferichBridge_of_provider`

- 内容:
  - `TriominoSquarefreeGNBridge` を PrimeProvider 層の契約として受けるための最小 provider 構造体を新設した。
  - これにより、「供給者は PrimeProvider 層に置く」という役割分担がコード上でも明示された。
  - `CosmicPetalBridgeGNNoWieferich.lean` は受け口、`TriominoSquarefreeGNBridgeProvider.lean` は供給者の器、という分離になった。

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProvider.lean`
  - 成功。

## 2026-03-04 phase-15 継続（PrimeProvider 供給者の実装室を追加）

- 新規:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`

- 追加:
  - `DkMath.FLT.TriominoSquarefreeGNBridgeProviderImplTarget`
  - `DkMath.FLT.triominoNoWieferichBridge_of_provider_impl`

- 内容:
  - PrimeProvider 層の契約 (`TriominoSquarefreeGNBridgeProvider`) に対する phase-15 の実装室を追加した。
  - 現時点では実装室は `Prop` target を受ける薄い wrapper に留め、本流には差し込まない。
  - これにより、供給者の「器」と「実装の試行錯誤の場」が分離された。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl`
  - 成功（既知の warning は `ZsigmondyCyclotomicResearch.lean` の false placeholder のみ）。

## 2026-03-04 phase-15 継続（`¬ q^2 ∣ GN` をより弱い honest bridge として追加）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProvider.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`

- 追加:
  - `DkMath.FLT.TriominoNoLiftGNBridge`
  - `DkMath.FLT.triominoNoWieferichBridge_of_not_sq_GN`
  - `DkMath.FLT.TriominoNoLiftGNBridgeProvider`
  - `DkMath.FLT.triominoNoWieferichBridge_of_noLift_provider`
  - `DkMath.FLT.TriominoNoLiftGNBridgeProviderImplTarget`
  - `DkMath.FLT.triominoNoWieferichBridge_of_noLift_provider_impl`

- 内容:
  - `Squarefree (GN ...)` より弱い、phase-15 が本質的に欲しい最小条件
    `¬ q ^ 2 ∣ GN p (z - y) y`
    を direct bridge として型に切り出した。
  - `triominoNoWieferichBridge_of_squarefree_GN` は、この direct bridge を経由して閉じるように整理した。
  - PrimeProvider 層でも、squarefree 版に加えて no-lift 版 provider を追加し、
    供給者の器と実装室の両方で受けられるようにした。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl`
  - 成功（既知の warning は `ZsigmondyCyclotomicResearch.lean` の false placeholder のみ）。
