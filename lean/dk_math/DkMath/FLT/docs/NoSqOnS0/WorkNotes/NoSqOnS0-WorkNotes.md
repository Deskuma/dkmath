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

## 2026-03-04 phase-15 継続（NoLift provider 実装室に研究 stub を追加）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`

- 追加:
  - `DkMath.FLT.triominoNoLiftGNBridgeProvider_impl`

- 内容:
  - phase-15 の実際の研究対象を、PrimeProvider 層の実装室ファイルに明示的な stub として追加した。
  - 型は `TriominoNoLiftGNBridgeProvider` で、
    primitive-prime 文脈から `¬ q^2 ∣ GN p (z - y) y` を直接供給する provider をここで育てる。
  - これにより、研究核の場所は `CosmicPetalBridgeGNNoWieferich.lean` の bridge 仕様ではなく、
    `TriominoSquarefreeGNBridgeProviderImpl.lean` の provider 実装 stub へ明確に移った。

- 注意:
  - この stub は `by sorry` を含むため、phase-15 の新しい warning の所在になる。
  - 既存の false placeholder (`ZsigmondyCyclotomicResearch.lean`) とは別に、
    Provider 実装室の未解決点を明示する意図で追加した。

## 2026-03-04 phase-15 継続（NoLift provider 実装室を正規入口に揃えた）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`

- 追加:
  - `DkMath.FLT.triominoNoWieferichBridge_impl`

- 内容:
  - 実装室では `¬ q^2 ∣ GN ...` を直接供給する `triominoNoLiftGNBridgeProvider_impl` を本命とし、
    そこから本流の `TriominoNoWieferichBridge` へ直接注入する
    `triominoNoWieferichBridge_impl` を追加した。
  - これにより、phase-15 の研究対象は
    `triominoNoLiftGNBridgeProvider_impl`
    ただ一箇所であることが、実装室ファイル内でも明確になった。

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl`
  - 成功。warning は
    - `TriominoSquarefreeGNBridgeProviderImpl.lean` の研究 stub
    - `ZsigmondyCyclotomicResearch.lean` の既知 false placeholder
    のみ。

## 2026-03-04 phase-15 継続（squarefree から no-lift への薄い橋を追加）

- 更新:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`

- 追加:
  - `DkMath.FLT.NoLift`
  - `DkMath.FLT.noLift_of_squarefree`
  - `DkMath.FLT.triominoNoLiftGNBridge_of_squarefree_GN`

- 内容:
  - `NoLift (q, X) := ¬ q^2 ∣ X` を phase-15 の最小 no-lift 語彙として追加した。
  - squarefree な非零自然数から直ちに `NoLift` が従う一般補題 `noLift_of_squarefree` を追加した。
  - これを使って、強い仮定 `TriominoSquarefreeGNBridge` から弱い本命仮定
    `TriominoNoLiftGNBridge` を直接得る薄い橋
    `triominoNoLiftGNBridge_of_squarefree_GN` を追加した。
  - `triominoNoWieferichBridge_of_squarefree_GN` は、内部でこの薄い橋を経由して
    `triominoNoWieferichBridge_of_not_sq_GN` に流すだけの形へ整理した。

- 確認:
  - `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich`
  - 成功（既知の warning は `ZsigmondyCyclotomicResearch.lean` の false placeholder のみ）。

## 2026-03-04 phase-15 継続（NoLift spine を常設化し provider stub を解消）

- 更新:
  - 新規: `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicNoLift.lean`
  - 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`

- 追加:
  - `DkMath.NumberTheory.GcdNext.noLift_GN_of_primitive_prime_factor`

- 内容:
  - primitive-prime branch の標準仮定から
    `¬ q ^ 2 ∣ GN d (a - b) b`
    を直接返す常設 spine を `NumberTheory` 側へ新設した。
  - 証明は
    `padicValNat_primitive_prime_factor_le_one`
    と
    `padicValNat_factorization`
    を使って `padicValNat q (GN ...) ≤ 1` に落とし、
    そこから `q^2 ∤ GN` を引く形に固定した。
  - `triominoNoLiftGNBridgeProvider_impl` は local `sorry` をやめ、
    反例 pack から必要な `Nat.Coprime z y` だけを組み立てて、
    新しい `NumberTheory` spine を呼ぶ薄い provider に変更した。

- 失敗例 / 設計差分:
  - 当初は「Branch B pack から `NoWieferichCondition` を抽出し、
    `NoWieferich => NoLift` をそのまま provider に差し込む」形を試した。
  - しかし現行の
    `PrimeGe5CounterexamplePack`
    と
    `triominoNoLiftGNBridgeProvider_impl`
    の引数には、その種の `NoWieferich` 条件を取り出せる field が存在しない。
  - そのため、入力シグネチャを壊さずに済む現実的な落とし所として、
    「primitive-prime 仮定そのものから直接 `NoLift` を返す」常設 spine に切り替えた。

- 確認:
  - `cd lean/dk_math && lake build DkMath.NumberTheory.ZsigmondyCyclotomicNoLift DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 成功。
  - 残る warning は既知の
    `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
    の
    `squarefree_implies_padic_val_le_one`
    （`declaration uses sorry`）
    のみ。

## 2026-03-05 phase-15 継続（偽 NoLift spine を降格し、squarefree ルートへ切り戻し）

- 更新:
  - 新規: `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicSquarefree.lean`
  - 更新: `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
  - 更新: `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicNoLift.lean`
  - 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean`
  - 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean`
  - 新規: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean`
  - 更新: `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 真である squarefree 系補題
    `padicValNat_le_one_of_squarefree`
    と
    `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
    を、新規常設ファイル
    `ZsigmondyCyclotomicSquarefree.lean`
    へ切り出した。
  - `ZsigmondyCyclotomicResearch.lean` には偽 placeholder
    `squarefree_implies_padic_val_le_one`
    と、その research wrapper だけを残し、true な squarefree 補題は持たせない形へ整理した。
  - `ZsigmondyCyclotomicNoLift.lean` は、もはや常設 spine ではなく、
    「primitive-prime 仮定だけでは `¬ q^2 ∣ GN` は言えない」
    ことを示す反例墓標
    `noLift_GN_of_primitive_prime_factor_is_false`
    へ差し替えた。
  - `TriominoSquarefreeGNBridgeProviderImpl.lean` では、concrete な
    `triominoNoLiftGNBridgeProvider_impl`
    を廃止し、
    `TriominoSquarefreeGNBridgeProvider` から
    `TriominoNoLiftGNBridge`
    / `TriominoNoWieferichBridge`
    を派生させる薄い定理だけを残した。
  - `CosmicPetalBridgeGNNoWieferich.lean` から research import を外し、
    true な glue と squarefree ルートだけを permanent 側に残した。
  - false wrapper に依存する kernel
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_*`
    は、新規
    `CosmicPetalBridgeGNNoWieferichResearch.lean`
    へ移動した。
  - `CosmicPetalBridgeGNDescentB.lean` は、その research-side kernel を明示 import する形へ変更し、
    permanent glue と research kernel の境界を import graph 上でも見えるようにした。

- 失敗例 / 制約:
  - 反例
    `(d, a, b, q) = (3, 5, 3, 7)`
    で
    `a^3 - b^3 = 98`,
    `q ∤ (a - b) = 2`,
    かつ
    `GN 3 (a - b) b = GN 3 2 3 = 49`
    なので
    `7^2 ∣ GN 3 2 3`
    が成り立つ。
  - したがって、
    「primitive-prime 仮定だけで `¬ q^2 ∣ GN`」
    という常設命題は偽であり、
    ここを `sorry` で埋める方向は破綻している。
  - 今回の切り戻しで permanent な `CosmicPetalBridgeGNNoWieferich.lean`
    自体の Research 依存は外れたが、
    `CosmicPetalBridgeGNDescentB.lean`
    は新しい
    `CosmicPetalBridgeGNNoWieferichResearch.lean`
    を経由して、なお Research に依存する。
  - つまり「true glue の常設化」は完了したが、
    「本流の descent ルートから Research を完全に切る」には、
    concrete な squarefree provider を供給するか、
    もしくは descent 入口そのものをパラメータ化する追加設計がまだ必要。

- 確認:
  - `cd lean/dk_math && lake build DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree DkMath.NumberTheory.ZsigmondyCyclotomicResearch DkMath.NumberTheory.ZsigmondyCyclotomicNoLift`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - すべて成功。
  - warning は
    `lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean`
    の
    `squarefree_implies_padic_val_le_one`
    に由来する `declaration uses sorry`
    が research 側に 1 件残るのみ。

## ~~2026-03-05 phase-15 継続（Basic.lean の d=3 private 補題から Research 参照を除去）~~

- 更新:
  - `Basic.lean`

- 内容:
  - `GN3_cube_not_cube_of_gt_one` が
    `padicValNat_primitive_prime_factor_le_one`
    を経由していたため、`ZsigmondyCyclotomicResearch.lean` への import を引いていた。
  - この private 補題は `d = 3` 固定であり、しかも同ファイル内に
    `GN3_cube_not_cube_of_gt_one_use_FLT3`
    という安全な比較用補題が既にあるため、
    実装をその補題への委譲へ差し替えた。
  - これにより `Basic.lean` から
    `ZsigmondyCyclotomicResearch.lean`
    の import を除去した。

- 判断:
  - `ZsigmondyCyclotomic.lean` にある `d = 3` 専用の
    `padicValNat_le_one_of_prime_divisor_case_three`
    は、現状では「差の付値 = 二次式の付値」までしか返さず、
    そのままでは `≤ 1` の上界にはならない。
  - よって今回の用途では、無理に valuation ルートを維持するより、
    既に存在する FLT(3) 比較補題へ戻す方が安全で、依存切断の目的にも一致する。

- ※ これは、ロールバックを行った（ユーザー）

## 2026-03-05 phase-15 継続（DescentB の kernel 注入を試行し、上位 interface の整理だけ先行）

- 更新:
  - `CosmicPetalBridgeGN.lean`
  - `CosmicPetalBridgeGNDescentB.lean`
  - `TriominoCosmicGapInvariant.lean`

- 内容:
  - `CosmicPetalBridgeGNDescentB.lean` について、
    `TriominoNoLiftGNBridge` を section 変数として広域に注入し、
    Branch B の descent kernel を research import から切り離す案を実装試行した。
  - しかしこの方法だと、中腹の `Candidate` 系補題
    （特に `triominoWieferichShrinkNumsInvCandidate_of_pack`
    / `triominoWieferichShrinkNumsInvCandidateB_kernel` 周辺）
    まで仮定が連鎖し、以後の多数の theorem/def の型が一斉に変化して崩れた。
  - したがって、今回の時点では `CosmicPetalBridgeGNDescentB.lean` の完全注入化は見送り、
    research kernel import を使う従来形へ戻した。
  - その代わり、`CosmicPetalBridgeGN.lean` では
    `TriominoWieferichBranchBridge` を `hNoLift` 1 本だけの最小 interface に縮めた。
  - 現状の `triominoWieferichLiftKernel_impl` / `triominoWieferichLiftExclusion_impl`
    は Branch B descent の no-arg 実装を使うので、
    lift 側はまだ `hNoLift` からは組み上がっていない。
  - `triominoNoWieferichBridge_impl` は引き続き `hNoLift` から構成する。
  - `TriominoCosmicGapInvariant.lean` 側は既に `hNoLift` 側しか使っていないため、
    上位 signature の変更だけで整合した。

- 判断:
  - `DescentB` の本体を truly parameterized にするには、
    単に theorem 1 本へ引数を足すだけでは足りず、
    少なくとも `CandidateB_kernel` 以降の長い suffix を
    明示的に引数 threading する再設計が必要。
  - つまり「kernel を引数化して research import を断つ」は正しい方向だが、
    現ファイル構造では 1 回の薄い patch では閉じない。
  - 先に interface を最小化し、descent 側は別途まとまった refactor として切るのが安全。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 成功。
  - 追加 warning は解消済み。
  - 依然として research warning は `ZsigmondyCyclotomicResearch.lean` の既知 1 件のみ。

## 2026-03-05 phase-15 継続（Main.lean の入口整理と section 分割）

- 更新:
  - `Main.lean`

- 内容:
  - `Main.lean` に section を導入し、公開定理群を以下の責務で分割した。
    - `CoreRoute`
    - `NoSqRecoveryAdapters`
    - `DescentAdapters`
    - `ProviderCompatibility`
    - `DescentBridgeAdapters`
    - `CompatibilityInputs`
    - `DefinitionalEqualities`
  - 併せて、次の 4 点を canonical entry としてコメントで明示した。
    - `DescentBaseInput`
    - `FLT_d3_by_padicValNat_of_NoSqOnS0`
    - `FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport`
    - `FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport`
    - `FLT_d3_by_padicValNat_of_DescentBaseInput`
  - これにより、「いま何を証明しているか」を
    `DescentBaseInput.hDescentClass` をどこから供給するか、
    という一点に追いやすくした。

- 判断:
  - いまの `Main.lean` は theorem 自体は多いが、多くは最終的に
    `FLT_d3_by_padicValNat_of_NoSqOnS0`
    へ流し込む薄い adapter である。
  - 先に区画整理しておくことで、
    本筋の証明対象（descent 系の canonical input をどう満たすか）が追いやすくなる。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。

## 2026-03-06 phase-15 継続（DescentB に局所 NoLift 束を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - Branch B の固定 `q` 用最小データ束を追加:
    - `structure BranchBLocalNoLift (p y z q : ℕ) : Prop`
    - fields:
      - `hq_prime : Nat.Prime q`
      - `hq_dvd_diff : q ∣ z ^ p - y ^ p`
      - `hq_not_dvd_gap : ¬ q ∣ (z - y)`
      - `hNoLift : ¬ q ^ 2 ∣ GN p (z - y) y`
  - `branchBLocalNoLift_of_noWieferich` を追加し、
    `TriominoNoWieferichBridge` から
    `∃ r, BranchBLocalNoLift p y z r` を返すようにした。
  - kernel 直結ラッパーとして
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_localNoLift_core`
    を追加。
    - 入力: existing kernel コンテキスト
    - 出力: `∃ r, BranchBLocalNoLift p y z r`
  - 既存の
    `..._existsPrime_dvd_GN_not_sq_of_noWieferich`
    と
    `..._existsPrime_dvd_GN_not_sq_core`
    は、この新しい local bundle 経由の実装に差し替えた。

- 判断:
  - `Basic` 側を不変に保ったまま、
    descent 側で「固定した `q` の局所 NoLift」を返す供給点を先に実装。
  - これで方針B移行時の接続先が明示された。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - 成功。
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。
  - 既存 warning のみ:
    - `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:81:6: declaration uses sorry`
    - `DkMath/FLT/GEisensteinBridge.lean:1464:2: Try this: intro ...`

## 2026-03-06 phase-15 継続（差し替え点固定: `NoLift -> padicValNat ≤ 1` 補助の導入）

- 更新:
  - `Basic.lean`

- 内容:
  - private 補助
    `padicValNat_le_one_of_noLift` を追加。
    - 入力: `Nat.Prime q`, `N ≠ 0`, `¬ q^2 ∣ N`
    - 出力: `padicValNat q N ≤ 1`
  - `GN3_cube_not_cube_of_gt_one_of_squarefree` では、
    上界構築を次の2段へ分離した。
    - 現在の供給源（squarefree）から `hNoLift_N : ¬ q^2 ∣ N` を作る
    - 上界化は `padicValNat_le_one_of_noLift hq_prime hN_ne hNoLift_N`
  - これで将来の方針B移行時は、
    差し替え点が「`hNoLift_N` の供給」1箇所に固定される形になった。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - 成功。
  - 残る既存 warning:
    - `DkMath/FLT/Basic.lean:685:8: declaration uses sorry`

## 2026-03-06 phase-15 継続（valuation spine 整形: `hN_pos` 統一と下界を `hq_dvd_N` 直結）

- 更新:
  - `Basic.lean`

- 内容:
  - `GN3_cube_not_cube_of_gt_one_of_squarefree` 内で、
    `hq_dvd_GN` を `hq_dvd_N : q ∣ N` として保持し、
    `hval_N_ge` を
    `DkMath.ABC.padicValNat_one_le_of_prime_dvd hq_prime hN_ne hq_dvd_N`
    で直接構成する形に整理。
  - `hN_ne` は `hN_pos` から一元的に作る形へ統一。
    `hN_pos` は `hGN_pos` から
    `simpa [N, A, B, Nat.add_sub_cancel]` で導出。
  - 併せて `unnecessarySimpa` 指摘箇所（`hb_ne0` 内）を
    `simpa` から `simp` へ変更して warning を解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - 成功。
  - `Basic.lean` の `unnecessarySimpa` warning は解消。
  - 残る既存 warning:
    - `DkMath/FLT/Basic.lean:669:8: declaration uses sorry`

## 2026-03-06 phase-15 継続（方針B: NoLift 依存を配線から外し、最小反例+下降へ切替）

- 更新:
  - `CosmicPetalBridgeGN.lean`

- 内容:
  - `TriominoWieferichBranchBridge` の入力契約を
    `hNoLift : TriominoNoLiftGNBridge`
    から
    `hDescent : TriominoWieferichLiftBridge`（= `WieferichDescentB`）
    に変更。
  - `triominoWieferichLiftKernel_impl` は
    `counterexampleHasWieferichLiftB_impl` と `hBranch.hDescent` を合成する形に変更。
  - `triominoWieferichLiftExclusion_impl` は branch 引数を受け取り、
    `wieferichLiftExclusion_of_liftExists_and_descent` へ接続。
  - `triominoNoWieferichBridge_impl` は
    `triominoNoWieferichBridge_of_not_sq_GN hBranch.hNoLift`
    から、
    `triominoNoWieferichBridge_of_wieferichLiftExclusion (triominoWieferichLiftExclusion_impl hBranch)`
    に切替。
  - コメントも方針B（最小反例 + 下降）に合わせて更新。

- 結果:
  - 本丸配線で `NoLift` の global 供給を要求しない形に移行。
  - `NoWieferich` は「lift exists + descent + minimal selection」経路で閉じる構成へ統一。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 成功。
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。
  - 既存 warning のみ:
    - `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:81:6: declaration uses sorry`
    - `DkMath/FLT/GEisensteinBridge.lean:1464:2: Try this: intro ...`

## 2026-03-05 phase-15 継続（`FLT3` fallback の明示隔離）

- 更新:
  - `Basic.lean`

- 内容:
  - fallback の責務を名前で明示するため、
    旧互換入口を
    `GN3_cube_not_cube_of_gt_one_fallback_use_FLT3`
    に改名した。
  - 呼び出し側（`u_eq_one_of_coprime_gcd` 内）も同名へ接続し、
    squarefree 非供給パスが「FLT3 fallback である」ことを
    コード上で判読可能にした。
  - あわせて `GN3_cube_not_cube_of_gt_one_use_FLT3` のコメントを更新し、
    本線が `GN3_cube_not_cube_of_gt_one_of_squarefree` であることを明示した。

- 結果:
  - fallback 経路が private 名称と呼び出し点の両方で露出し、
    非依存本線（squarefree 版）との混線を避けやすくなった。
  - 証明内容そのもの（論理）は不変で、責務分離のみを実施。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - 成功。
  - 既存 warning:
    - `DkMath/FLT/Basic.lean:635:8: declaration uses sorry`

## 2026-03-05 phase-15 継続（GEisensteinBaseInput provider interface を GEisensteinBridge 側へ移設）

- 更新:
  - `GEisensteinBridge.lean`
  - `Main.lean`

- 内容:
  - 先に `Main.lean` に置いていた
    - `GEisensteinBaseInput`
    - `GEisensteinBaseInputProvider`
    - `geisensteinBaseInputProvider_of_coreFamily`
    を `GEisensteinBridge.lean` へ移設した。
  - `GEisensteinBridge` 側では `GEisensteinDescentCore` 直後に定義し、
    bridge 層の provider 群と同じ責務領域に揃えた。
  - `Main.lean` では重複定義を削除し、import 経由でそのまま利用する形に変更した。
  - これで `GEisensteinBaseInput` 系の interface は `Main` ではなく
    `GEisensteinBridge` が唯一の定義元になった。

- 判断:
  - provider interface の責務（kernel family の供給仕様）は bridge 層に置く方が依存方向が素直。
  - `Main` は「受けるだけ」の公開入口モジュールとして薄く保てる。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 成功（既存の `GEisensteinBridge.lean` style 提案 warning のみ）。

## 2026-03-05 phase-15 継続（GEisensteinBaseInput を返す provider interface を追加）

- 更新:
  - `Main.lean`

- 内容:
  - `GEisensteinBaseInputProvider` を追加した。
  - 仕様は
    `∀ {c b}, b < c → Nat.Coprime c b → GEisensteinBaseInput c b`
    を返す最小 provider。
  - あわせて
    `geisensteinBaseInputProvider_of_coreFamily`
    を追加し、
    `GEisensteinDescentCore` family からこの provider を組み立てられるようにした。
  - 公開側の thin wrapper として
    `FLT_d3_by_padicValNat_of_GEisensteinBaseInputProvider`
    も追加し、
    `provider -> GEisensteinBaseInput -> FLT`
    の一本道を作った。

- 判断:
  - これで `Main` の公開入口は
    - 値レベル: `GEisensteinBaseInput`
    - family レベル: `GEisensteinBaseInputProvider`
    の 2 段で受けられる。
  - 今後 provider 実装室を作るなら、まず `GEisensteinDescentCore` family を供給し、
    そこから `geisensteinBaseInputProvider_of_coreFamily`
    を通して `Main` に刺すのが標準ルートになる。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。

## 2026-03-05 phase-15 継続（PrimitiveSquareDescentEngine から GEisensteinDescentCore への正規 constructor を明示）

- 更新:
  - `GEisensteinBridge.lean`
  - `Main.lean`

- 内容:
  - `GEisensteinBridge.lean` に、次の constructor を追加した。
    - `GEisensteinDescentCore_of_harmonicEnvelope_descentStep`
    - `GEisensteinDescentCore_of_harmonicEnvelope_descentEngine`
  - どちらも最終的には
    `GEisensteinDescentCore_of_descentClassify_primitiveSized`
    へ流し込み、
    `primitiveSized` frame つきの nonempty core を作る。
  - これにより、`PrimitiveSquareDescentStep` / `PrimitiveSquareDescentEngine`
    は「前段の生成器」、`GEisensteinDescentCore`
    は「最終 kernel」という役割分担が明確になった。
  - `Main.lean` の
    `FLT_d3_by_padicValNat_of_harmonicEnvelope_descentStep_coprimeSupport`
    と
    `FLT_d3_by_padicValNat_of_harmonicEnvelope_descentEngine_coprimeSupport`
    も、この new core constructor を使って
    `DescentBaseInput.ofGEisensteinCore`
    を組み立てる形へ変更した。

- 判断:
  - `hDescentClass` の供給路を「step/engine から直接 classify を作る」形のままにしておくより、
    いったん `GEisensteinDescentCore` に昇格させてから
    `DescentBaseInput` を構成する方が、今後の kernel 注入・provider 化と整合する。
  - 特に `primitiveSized` frame を持つ core を標準にしたことで、
    `classifyImpossible` だけの薄い殻ではなく、
    停止到達 API を含む kernel として使える。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.GEisensteinBridge DkMath.FLT.Main`
  - 成功（既存の `GEisensteinBridge.lean` style 提案 warning のみ）。

## 2026-03-05 phase-15 継続（GEisensteinBaseInput を新設し、Main の公開入口を移す）

- 更新:
  - `Main.lean`

- 内容:
  - 新しく `GEisensteinBaseInput` を追加した。
    - `hbc : b < c`
    - `hcb_coprime : Nat.Coprime c b`
    - `hCore : GEisensteinDescentCore c b`
  - これにより、`Main` の公開側で受け取るべき bundle を
    「`descentClassify` だけの最小束」ではなく
    「`GEisenstein` kernel そのものを含む束」に引き上げた。
  - `DescentBaseInput` は残すが、役割を内部 compatibility layer に下げた。
  - 変換 `GEisensteinBaseInput.toDescentBaseInput` を追加し、
    下流の `descentClassify` ベース定理へはこの内部変換で接続する。
  - 公開 canonical entry として
    `FLT_d3_by_padicValNat_of_GEisensteinBaseInput`
    を追加した。
  - 既存の
    `FLT_d3_by_padicValNat_of_DescentBaseInput`
    は内部 compatibility entry というコメントに変更した。
  - step/engine 入口や `GEisensteinCore` 入口のローカル bundle も、
    `DescentBaseInput` ではなく `GEisensteinBaseInput` を先に作る形へ寄せた。

- 判断:
  - これで `Main` の「公開入口として何を供給すべきか」が
    `GEisensteinDescentCore` を含む bundle に固定された。
  - 以後は `hDescentClass` 単体ではなく、
    `GEisensteinBaseInput` をどの provider / kernel から組み立てるか、
    という設計で前へ進める。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。
  - 新規 warning はなし（既存の `GEisensteinBridge.lean` の style 提案のみ）。

## 2026-03-05 phase-15 継続（DescentBaseInput.hDescentClass の canonical source を確定）

- 更新:
  - `Main.lean`

- 内容:
  - `DescentBaseInput.hDescentClass` の正規供給源を
    `GEisensteinDescentCore c b`
    に確定した。
  - その判断をコードへ落とすため、
    `DescentBaseInput.ofGEisensteinCore`
    を追加した。
  - この constructor は
    `descentClassifyImpossibleOnPrimitive_of_GEisensteinCore`
    を用いて、
    `GEisenstein` 側の descent kernel から
    `DescentBaseInput` を組み立てる。
  - `FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport`
    もこの constructor を経由する形へ整理し、
    `GEisensteinCore -> DescentBaseInput -> descentClassify`
    という正規ルートをコード上で明示した。

- 判断:
  - `PrimitiveSquareDescentStep` / `PrimitiveSquareDescentEngine` は
    `hDescentClass` を生む前段の生成器としては有用だが、
    停止到達や frame 情報まで持つ「kernel」としては
    `GEisensteinDescentCore` の方が豊富で安定している。
  - したがって、`DescentBaseInput` に何かを注入する最終点は
    `GEisensteinDescentCore`
    とみなすのが自然。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - 成功。

## 2026-03-05 phase-15 継続（`Basic` の偽命題リンク置換の可否調査）

- 更新:
  - `Basic.lean`
  - `ZsigmondyCyclotomicSquarefree.lean`
  - `ZsigmondyCyclotomicResearch.lean`

- 調査対象:
  - `Basic.lean` の `GN3_cube_not_cube_of_gt_one` 内で使っている
    `padicValNat_primitive_prime_factor_le_one`
    （`ZsigmondyCyclotomicResearch.lean` 側定義）を
    `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
    に置換できるか。

- 結果:
  - **現状の `Basic` 単体文脈では置換不能**。
  - 置換先補題は追加仮定
    `Squarefree (GN 3 (A - B) B)` を要求するが、
    `GN3_cube_not_cube_of_gt_one` の入力
    (`a ≥ 2`, `y ≥ 1`, `Nat.Coprime a y`, `¬ 3 ∣ a`) から
    この squarefree を供給する既存補題がワークスペース内に見当たらない。
  - `Squarefree (GN ...)` を直接生成する既存ルートは
    PrimeProvider/Bridge 層（`CosmicPetalBridgeGNNoWieferich.lean` まわり）であり、
    `Basic.lean` のこの private lemma 呼び出し経路には接続されていない。

- 失敗例（探索時の反例メモ）:
  - `A=a^3+y`, `B=y` 形でも、primitive 条件 `q ∣ A^3-B^3`, `q ∤ A-B` だけでは
    `v_q(A^3-B^3) ≤ 1` は成り立たない実例が多数出る。
  - 例:
    - `(a,y,q) = (2,29,7)` で `v_7((a^3+y)^3-y^3)=2`
    - `(a,y,q) = (10,33,31)` で `v_31((a^3+y)^3-y^3)=3`
  - したがって「偽命題の単純置換」は不可で、
    `Squarefree` 供給を設計に追加しない限り、
    `Basic` の当該ブロックだけを安全に差し替えることはできない。

- 方針メモ:
  - `Basic` を non-FLT3 ルートのまま維持するなら、
    次段で必要なのは「`GN3_cube_not_cube_of_gt_one` に対する `Squarefree` 供給路の新設」。
  - 供給路を置かない場合、当該 private lemma は引き続き
    research 補題依存のまま残る。

## 2026-03-05 phase-15 継続（`Basic` 偽命題リンクの仮定付き切り離し実装）

- 更新:
  - `Basic.lean`

- 内容:
  - `GN3_cube_not_cube_of_gt_one` の non-FLT3 ルートを、
    `Squarefree` 仮定つきの新補題
    `GN3_cube_not_cube_of_gt_one_of_squarefree`
    として分離した。
  - 新補題では `hval_le` を偽命題
    `padicValNat_primitive_prime_factor_le_one`
    ではなく、
    `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
    で構成するように変更。
  - `hSq : Squarefree (GN 3 (a ^ 3) y)` から
    `Squarefree (GN 3 (A - B) B)` への変換を
    `simpa [A, B]` で供給して適用。
  - `Basic.lean` の import から
    `ZsigmondyCyclotomicResearch.lean` を削除し、
    `ZsigmondyCyclotomicSquarefree.lean` を直接 import。
  - 既存シグネチャ互換のため、旧名
    `GN3_cube_not_cube_of_gt_one`
    は暫定 wrapper として残し、
    現時点では `GN3_cube_not_cube_of_gt_one_use_FLT3` に接続。

- 結果:
  - `Basic.lean` から
    - `ZsigmondyCyclotomicResearch.lean`
    - `padicValNat_primitive_prime_factor_le_one`
    への参照は消滅。
  - ただし、旧シグネチャ側は squarefree 供給が未接続のため、
    互換 wrapper で FLT3 経由を維持（設計上の未完点として残置）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - 成功。
  - 既存 warning:
    - `DkMath/FLT/Basic.lean:635:8: declaration uses sorry`
    - （今回差分による新規 warning ではない）

## 2026-03-06 phase-15 継続（`q` 一本固定スニペットの導入）

- 更新:
  - `Basic.lean`

- 内容:
  - `pick_primitive_q_data_GN3` を private 補助補題として追加。
  - 返り値は次の4点をまとめて返す形にした。
    - `hq_prime : Nat.Prime q`
    - `hq_div : q ∣ A^3 - B^3`
    - `hq_ndiv : ¬ q ∣ A - B`
    - `hq_dvd_GN : q ∣ GN 3 (A - B) B`
  - `hq_dvd_mul` の導出は
    `rw [← hfactor]; exact hq_div`
    の堅い形で実装。
  - `GN3_cube_not_cube_of_gt_one_of_squarefree` 内の
    primitive prime 抽出部分をこの補助補題経由へ差し替えた。
  - さらに整理として、
    `hN_pos : 0 < N` を `hGN_pos` から
    `simpa [N, A, B, Nat.add_sub_cancel]` で導出し、
    `hN_ne : N ≠ 0` は `Nat.ne_of_gt hN_pos` で取得する形に統一。
  - `hq_dvd_GN` は `hq_dvd_N : q ∣ N` に受け渡し、
    `hval_N_ge : 1 ≤ padicValNat q N` の導出に実使用
    （`DkMath.ABC.padicValNat_one_le_of_prime_dvd`）。

- 備考:
  - 共有スニペット案にあった
    `exists_primitive_prime_factor_prime` 呼び出しの余分な `(by norm_num)` 1 個は、
    現行シグネチャに合わせて削除して反映。
  - 失敗例:
    - `hN_ne` を `Nat.pos_of_dvd_of_pos hq_dvd_N hq_prime.pos` で出そうとしたが、
      方向が合わず（`q ∣ N` からは直接 `0 < N` を出せない）型不一致で失敗。
    - `hN_ne` は一旦元の `hb : GN ... = b^3` 経由へ戻し、
      `hq_dvd_GN` は `hq_dvd_N` として保持する形に修正。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - 成功。
  - 既存 warning:
    - `DkMath/FLT/Basic.lean:663:8: declaration uses sorry`

## 2026-03-06 phase-15 継続（DescentB の局所 NoLift 供給口を GN3 形へ pullback）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `BranchBLocalNoLift` から `Basic` 側の `N := GN 3 (a^3) y` に直接刺せるよう、
    次の pullback 補題を追加:
    - `branchBLocalNoLift_pullback_GN3`
      - 入力: `BranchBLocalNoLift 3 y (a ^ 3 + y) q`
      - 出力: `¬ q ^ 2 ∣ GN 3 (a ^ 3) y`
      - 実装: `simpa [Nat.add_sub_cancel]` で gap 形を吸収
  - あわせて、`a^3` 形の入力から Branch B 局所束を返す薄い供給定理を追加:
    - `branchBLocalNoLift_GN3_of_noWieferich`
      - `h3_not_dvd_a3 : ¬ 3 ∣ a^3`
      - `hq_not_dvd_a3 : ¬ q ∣ a^3`
      - `hqpow_dvd_GN_a3 : q^3 ∣ GN 3 (a^3) y`
      を受け、内部で gap 形へ `simpa [Nat.add_sub_cancel]` 変換して
      `branchBLocalNoLift_of_noWieferich` に接続。

- 失敗例:
  - 初回実装で `branchBLocalNoLift_GN3_of_noWieferich` を
    `branchBLocalNoLift_of_noWieferich` より前に置いたため、
    `Unknown identifier branchBLocalNoLift_of_noWieferich` でビルド失敗。
  - 対処として定理定義順を後ろへ移動し、再ビルドで解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（GapGNPowDataB を FLT3 ラッパーへ直結）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定理を追加:
    - `FLT3_from_pack_gapGNPowData_and_noWieferich3`
      - 入力:
        - `hpack : PrimeCounterexamplePack 3 x y z`
        - `d : TriominoWieferichShrinkGapGNPowDataB 3 x y z q`
        - `ha : 2 ≤ d.u`
        - `h3_not_dvd_u3 : ¬ 3 ∣ d.u ^ 3`
      - 処理:
        - `d.hgap` / `d.hGNq` をそのまま
          `FLT3_from_pack_gapCube_and_noWieferich3_of_mulCube`
          へ渡して矛盾化
      - 目的:
        - 853–936 行帯の `GapGNPowDataB` 系データから、
          追加整形なしで FLT3 実パス入口へ流し込める接続点を固定。

- 失敗例:
  - なし（型合わせのみで通過）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（FLT3 実分岐に刺しやすい `PrimeCounterexamplePack 3` 直受け入口を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `FLT3_from_pack_gapCube_and_noWieferich3` を追加。
    - 入力: `hpack : PrimeCounterexamplePack 3 x y z`, `hy`, `hgap`, `hGN_cube` など
    - 目的: 実分岐がすでに `PrimeCounterexamplePack 3 ...` を持つ場合に、
      transport 補題 `primeCounterexamplePack3_of_eq` を経由した GN3 provider kernel 呼び出しを
      そのまま適用できるようにする。
  - 内部では `hpack.hyz_lt` と `hy` から `hpos` を組み立て、
    既存の `FLT3_from_gapCube_and_noWieferich3` へ委譲。

- 失敗例:
  - 初回実装で `by_contra hx0` の `hx0` をそのまま `simpa [hx0]` に使って失敗。
    - `hx0` の型は `¬ 0 < x` であり `x = 0` ではないため。
  - `hx_eq0 : x = 0 := Nat.eq_zero_of_not_pos hx0` を挟んで解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-06 phase-15 継続（GN3 経路を `PrimeCounterexamplePack 3` 実パスへ接続）

- 更新:
  - `CosmicPetalBridgeGNCore.lean`
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `Core` に `TriominoNoWieferichBridge3` を追加。
    - `PrimeGe5CounterexamplePack` とは分離し、`PrimeCounterexamplePack 3` 専用の
      NoWieferich 契約として定義。
  - `Core` に `triominoCosmicNonLiftableGN3Bridge_of_noWieferich3` を追加。
    - `p=3` 固定で `z^3 - y^3 = (z-y) * GN 3 (z-y) y` を使い、
      差側 no-lift から GN 側 no-lift を引き戻す橋を常設化。
  - `DescentB` の GN3 専用定理群の入力を非空文脈へ修正:
    - `branchBLocalNoLift_GN3_of_noWieferich`
    - `gn3NoLiftProvider_of_noWieferich`
    - `kernel_route_gn3_not_cube_of_noWieferich`
    - いずれも `PrimeGe5CounterexamplePack 3 ...` から
      `PrimeCounterexamplePack 3 ...` へ置換し、
      `TriominoNoWieferichBridge3` を受け取る形へ変更。
  - これにより、GN3 provider 経路は「型だけ通る到達不能枝」ではなく、
    `p=3` を許す実文脈で適用可能な契約に整列した。

- 失敗例:
  - `branchBLocalNoLift_GN3_of_noWieferich` で旧実装のまま
    `branchBLocalNoLift_of_noWieferich` を再利用しようとすると、
    必要入力が `PrimeGe5CounterexamplePack` のため型が合わず失敗。
  - 対処として GN3 専用に直接
    `hq_dvd_diff`（因数分解から）と `hNoLift`（`...noWieferich3` から）を構成し、
    `r := q` で束を返す形へ変更。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - すべて成功。

## 2026-03-07 phase-15 継続（FLT3 実パス入口: `z = a^3 + y` transport helper を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `primeCounterexamplePack3_of_eq` を追加。
    - 入力: `hpos`, `h_coprime`, `h_body : z^3 = x^3 + y^3`, `hz : z = a^3 + y`
    - 出力: `PrimeCounterexamplePack 3 x y (a^3 + y)`
    - 目的: GN3 kernel が要求する pack への transport を 1 本化。
  - `FLT3_from_gapCube_and_noWieferich3` を追加。
    - 入力: `hNW3`, `hgap : z - y = a^3`, `hGN_cube : ∃ b, GN 3 (a^3) y = b^3` など
    - 処理:
      1. `hgap` + `hzy` から `hz : z = a^3 + y` を再構成
      2. `primeCounterexamplePack3_of_eq` で `hpack3` を構成
      3. `hpack3.gap_coprime_right` と `Nat.coprime_pow_left_iff` から `Nat.Coprime a y` を回収
      4. `kernel_route_gn3_not_cube_of_noWieferich` へ注入して `hGN_cube` を矛盾化
  - これで「`gap cube witness` を持つ FLT3 分岐 -> GN3 provider kernel」への
    実パス入口が 1 本できた。

- 失敗例:
  - 初回実装で `Nat.pow_pos hpos.left 3` と書いたが、この環境の型では
    `Nat.pow_pos` は指数引数を取らずエラー。
  - `Nat.pow_pos hpos.left` へ修正して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-06 phase-15 継続（candidateZ の矛盾生成点へ GN3 provider 経路を差し込み）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_from_gap_GN_powers_core`
    の矛盾生成を再整理。
    - `PrimeGe5CounterexamplePack` 文脈では `p = 3` 分岐は到達不能であることを確認。
    - `by_cases hp3 : p = 3` を削除し、常に
      `...noPowGN_core -> hNoPowGN ⟨q*d.v1, d.hGNq⟩`
      で矛盾を作る形に修正。
  - 到達不能分岐へ GN3 provider 経路を差し込んでいた誤りを除去し、
    候補点 `candidateZ` は `p ≥ 5` 専用核として意味どおりに戻した。

- 失敗例:
  - `p = 3` 分岐で `hpack3.hp5 : 5 ≤ 3` から `False` を作って
    `ha` / `hcop` を `False.elim` 供給する実装は、型は通るが到達不能分岐であり
    「実パスで GN3 provider を使う」目的を満たさないと判明。
  - 同見出し節が重複していたため、今回一本化。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-06 phase-15 継続（GN3 NoLift 最小インターフェイスを導入して Basic 差し替え点を固定）

- 更新:
  - `Core.lean`
  - `Basic.lean`
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `Core.lean` に `DkMath.FLT.GN3NoLiftProvider (a y)` を追加。
    - `q ∣ GN 3 (a^3) y` と `¬ q ∣ a^3` から `¬ q^2 ∣ GN 3 (a^3) y` を供給する最小契約。
  - `Basic.lean` の
    `GN3_cube_not_cube_of_gt_one_of_squarefree` 内で
    `hNoLift_N` 生成を provider 呼び出しへ差し替え。
    - 既存の squarefree 証明は、局所 provider `hProvSq` を作ってそこへ閉じ込めた。
    - valuation spine の下流 (`padicValNat_le_one_of_noLift`) は無変更。
  - `CosmicPetalBridgeGNDescentB.lean` に
    `gn3NoLiftProvider_of_noWieferich` を追加。
    - `PrimeGe5CounterexamplePack 3 x y (a^3+y)` と NoWieferich bridge から
      `GN3NoLiftProvider a y` を構成できる形にした。

- 失敗例:
  - `Core.lean` の新 interface で `GN` を短名のまま書いたところ、
    `namespace DkMath.FLT` では `Unknown identifier GN` でビルド失敗。
  - `DkMath.CosmicFormulaBinom.GN` へ完全修飾して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Core`
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - すべて成功。

## 2026-03-06 phase-15 継続（Basic の GN3 補題を provider 本線 + squarefree wrapper に二層化）

- 更新:
  - `Basic.lean`

- 内容:
  - `GN3_cube_not_cube_of_gt_one_of_provider_core` を private core として確立。
    - valuation spine 本体はこの core に集約。
    - `hNoLift_N` は `GN3NoLiftProvider` から供給する形に固定。
  - `GN3_cube_not_cube_of_gt_one_of_squarefree` は
    squarefree から `GN3NoLiftProvider` を作る薄い wrapper へ変更。
  - `GN3_cube_not_cube_of_gt_one_of_provider` を public 入口として追加。
    - これで PrimeProvider / kernel 側が provider を注入して本線を呼べる口ができた。
  - FLT3 fallback 補題は比較用として維持（本線は provider 入口）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.Basic`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-06 phase-15 継続（kernel 側で provider 経路を 1 本貫通）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `import Basic.lean` を追加し、PrimeProvider 側から
    `GN3_cube_not_cube_of_gt_one_of_provider` を直接呼べるようにした。
  - 新規定理を追加:
    - `kernel_route_gn3_not_cube_of_noWieferich`
      - 入力: `hNW`, `hpack : PrimeGe5CounterexamplePack 3 x y (a^3+y)`,
        `ha`, `hy`, `hcop`, `h3_not_dvd_a3`
      - 処理:
        1. `gn3NoLiftProvider_of_noWieferich` で `GN3NoLiftProvider a y` を生成
        2. `Basic` の public 入口 `GN3_cube_not_cube_of_gt_one_of_provider` へ注入
      - 結果: `¬ ∃ b, GN 3 (a^3) y = b^3`
  - これで「squarefree fallback なし」の provider 注入経路が
    kernel 側に 1 本成立した。

- 失敗例:
  - `h3a` 生成で `dvd_pow h3 3` を使ったところ型不一致
    （`numerals are data ... expected proposition`）で失敗。
  - `dvd_pow_self` を使う形に修正して解消:
    `h3_dvd_a3 : 3 ∣ a^3 := dvd_trans h3 (dvd_pow_self a (by decide : 3 ≠ 0))`

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（FLT3 実分岐への差し込み準備: `hGN_cube` 変換ラッパー）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定理を追加:
    - `FLT3_from_pack_gapCube_and_noWieferich3_of_mulCube`
      - 入力:
        - `hpack : PrimeCounterexamplePack 3 x y z`
        - `hgap : z - y = a^3`
        - `hGNq : GN 3 (z - y) y = (q * v1)^3`
      - 処理:
        - `hGNq` と `hgap` から `hGN_cube : ∃ b, GN 3 (a^3) y = b^3` を構成
        - 既存の `FLT3_from_pack_gapCube_and_noWieferich3` に注入
      - 目的:
        - 呼び出し側で毎回 `∃ b` 包装を書く必要をなくし、
          `GN = (q * v1)^3` 形の枝から 1 行で矛盾化できるようにする。

- 調査結果（実パス探索）:
  - `PrimeCounterexamplePack 3` を直接使う箇所は現時点で
    `CosmicPetalBridgeGNCore.lean` / `CosmicPetalBridgeGNDescentB.lean` に限定。
  - `hgap : z - y = a^3` と `GN 3 ... = _^3` を同時に持つ既存呼び出し点は未接続。
  - したがって次の実作業は、
    FLT3 側でこの 2 つが揃う枝（またはそこへ transport できる枝）へ
    `FLT3_from_pack_gapCube_and_noWieferich3_of_mulCube` を差し込む配線。

- 失敗例:
  - 最初のビルドでプロジェクト root を 1 階層誤り
    (`/home/deskuma/develop/lean/dkmath` で `lakefile` 不在)。
  - `workdir` を `lean/dk_math` へ修正して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`GapGNPowDataB` から candidateZ core へ FLT3 専用差し替え口を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定義を追加:
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_from_gap_GN_powers_of_noWieferich3`
      - 入力:
        - `hpack : PrimeCounterexamplePack 3 x y z`
        - `d : TriominoWieferichShrinkGapGNPowDataB 3 x y z q`
        - `hy : 1 ≤ y`
        - `ha : 2 ≤ d.u`
        - `h3_not_dvd_u3 : ¬ 3 ∣ d.u ^ 3`
      - 処理:
        - `FLT3_from_pack_gapGNPowData_and_noWieferich3` で即矛盾化
        - `False.elim` で `TriominoWieferichShrinkKernelCandidateZDataB 3 x y z q` を返す
      - 目的:
        - 既存の一般 `PrimeGe5` 本丸（`noPowGN_core`）はそのまま保持しつつ、
          `p=3` 実分岐側だけを新 GN3 spine へ差し替えるための入口を明示する。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（FLT3 用 `candidateZ_data/candidateZ` ラッパーを追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定義を追加:
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_data_of_noWieferich3`
      - `GapGNPowDataB 3` と `hNW3` から `candidateZ_data` を返す薄い包装。
      - 内部で
        `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_from_gap_GN_powers_of_noWieferich3`
        を直接呼ぶ。
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_of_noWieferich3`
      - 上記 data を `toSubtype` して、既存 `candidateZ` 形
        `{ z' // z' < z ∧ ¬ 3 ∣ (z' - y) ∧ (x / q)^3 + y^3 = z'^3 }`
        を返す。
  - 目的:
    - 「`p=3` 実分岐で実際に呼ぶ位置」を
      `candidateZ_data / candidateZ` と同型の入口で固定する。
    - 一般 `PrimeGe5` 本丸は未変更のまま温存。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`hpB` から `¬ 3 ∣ d.u^3` を自動回収する FLT3 ラッパーを追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定義を追加:
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_data_of_noWieferich3_hpB`
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_of_noWieferich3_hpB`
  - どちらも `hpB : ¬ 3 ∣ (z - y)` と `d.hgap : z - y = d.u^3` から
    `¬ 3 ∣ d.u^3` を内部で回収して既存ラッパーへ委譲。
  - 目的:
    - 呼び出し側で `h3_not_dvd_u3` を明示生成する手間を減らし、
      既存の Branch B 形（`hpB` 保持）から FLT3 入口へ差し込みやすくする。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（実置換: `_hpB` ラッパーを旧経由から新 core 直呼びへ）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_data_of_noWieferich3_hpB`
    の本体を置換。
    - 旧: `...candidateZ_data_of_noWieferich3`（旧経由）へ委譲
    - 新: `...candidateZ_from_gap_GN_powers_of_noWieferich3`（新 core）を直接呼ぶ
  - これにより、`hpB` 版ラッパーは中間層に依存せず、
    FLT3 no-Wieferich spine へ直接接続される。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（攻め案: `p=3` 即矛盾定理を追加し `_hpB` 末尾を差し替え）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規定理を追加:
    - `triominoWieferichShrinkKernelEqSeedTracePack3_contradiction_of_noWieferich3_hpB`
      - 入力:
        - `hNW3, hpack, hy, hpB, d, ha`
      - 出力:
        - `False`
      - 役割:
        - `hpB` と `d.hgap` から `¬ 3 ∣ d.u^3` を内部回収し、
          `FLT3_from_pack_gapGNPowData_and_noWieferich3` へ直結する
          `p=3` 専用の即矛盾入口を固定。
  - 置換:
    - `triominoWieferichShrinkKernelEqSeedTracePack3_candidateZ_data_of_noWieferich3_hpB`
      の末尾を、
      旧ルート（`h3_not_dvd_u3` を作って core 呼び出し）から
      新しい即矛盾定理呼び出し + `False.elim` へ置換。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（一般化閉路: `p=3 / p≥5` dispatcher と pack 昇格補題を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 新規補題:
    - `primeGe5CounterexamplePack_of_pack`
      - `PrimeCounterexamplePack p x y z` + `hy : 1 ≤ y` + `hp5 : 5 ≤ p`
        から `PrimeGe5CounterexamplePack p x y z` を構成。
      - `hx0` は `x=0` を仮定して `y^p = z^p` を導き、
        `Nat.pow_left_injective` と `hyz_lt` で矛盾化。
  - 新規 dispatcher:
    - `triominoWieferichShrinkKernelEqSeedTracePack_contradiction_of_noWieferich`
      - 入力:
        - `hNW3 : TriominoNoWieferichBridge3`
        - `hNW5 : TriominoNoWieferichBridge`
        - `hpack : PrimeCounterexamplePack p x y z`
        - `hy, hp2, hpB, hqP, hq_not_dvd_gap, hqpow_dvd_GN, d, ha`
      - 分岐:
        - `p = 3` は GN3 spine (`...contradiction_of_noWieferich3_hpB`) へ
        - `p ≠ 3` は `hp2` と prime 性から `5 ≤ p` を導いて Ge5 spine へ

- 失敗例:
  - `primeGe5CounterexamplePack_of_pack` 初版で
    `Nat.zero_pow` の条件型を `p ≠ 0` と誤って渡し失敗。
    - 修正: `0 ^ p + ...` を一段受け、`Nat.zero_pow hpack.hp.pos` で整理。
  - dispatcher 初版を参照先より前に置いてしまい、前方参照で失敗。
    - 修正: 宣言順を後ろへ移動し解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（本線置換: `candidateZ_from_gap_GN_powers_core` を dispatcher 呼び出しへ差し替え）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 追加:
    - `triominoWieferichShrinkKernelEqSeedTracePack_contradiction_of_noWieferich_gate3`
      - `p=3` 分岐で必要な `hNW3`/`ha` を gate (`p = 3 -> ...`) で受ける dispatcher。
      - `p≠3` 分岐は Ge5 spine をそのまま実行。
  - 置換:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_from_gap_GN_powers_core`
      の旧末尾
      - `hNoPowGN` を作って `hNoPowGN ⟨q * d.v1, d.hGNq⟩`
      を廃止し、
      - `...contradiction_of_noWieferich_gate3` 呼び出し + `False.elim`
      へ差し替え。
    - `PrimeGe5` 文脈なので `p=3` gate は
      `hpack.hp5` と `p=3` の矛盾から `False.elim` で供給。
  - 整理:
    - 既存 `triominoWieferichShrinkKernelEqSeedTracePack_contradiction_of_noWieferich`
      は新 gate dispatcher を呼ぶ薄い wrapper に更新。

- 失敗例:
  - `hpack.hp.ne_two` を使って `hp2 : p ≠ 2` を作ろうとして型不一致で失敗。
    - 修正: `hpack.hp5` から `2 < p` を導き `Nat.ne_of_gt` で `hp2` を構成。
  - `omega` だけで `hp2` を出す試行が失敗。
    - 修正: 上記の明示的な不等式導出へ変更。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（閉路固定: 残存確認 + axioms 点検 + `GapGNPowDataB` 不可能定理を追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - 残存確認:
    - `rg -n "hNoPowGN|noPowGN_core|q \\* d\\.v1|d\\.hGNq" DkMath/FLT/PrimeProvider`
    - 旧 `hNoPowGN ⟨q * d.v1, d.hGNq⟩` 形は
      `...contradiction_of_noWieferich_gate3` 内（Ge5 分岐の内部ローカル）にのみ残存。
      `candidateZ_from_gap_GN_powers_core` 末尾は dispatcher 呼び出しに置換済み。
  - axioms 点検:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePack_contradiction_of_noWieferich`
      - `propext, Classical.choice, Quot.sound`
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_from_gap_GN_powers_core`
      - `propext, sorryAx, Classical.choice, Quot.sound`
    - `#print axioms kernel_route_gn3_not_cube_of_noWieferich`
      - `propext, Classical.choice, Quot.sound`
    - `#print axioms GN3_cube_not_cube_of_gt_one_of_provider`
      - `propext, Classical.choice, Quot.sound`
  - 追加:
    - `triominoWieferichShrinkGapGNPowData_impossible_of_noWieferich`
      - `GapGNPowDataB` と dispatcher 前提から直接 `False` を返す最終定理。
      - 本体は
        `triominoWieferichShrinkKernelEqSeedTracePack_contradiction_of_noWieferich`
        への薄い委譲のみ。

- 失敗例:
  - なし（追加分）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`candidateZ_from_gap_GN_powers_core` の `sorryAx` 污染源を局所化し切り離し）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `#print axioms` 追跡で汚染源を特定:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
      が `sorryAx` を保持。
    - `...contradiction_of_noWieferich_gate3` は clean。
  - 対処:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_from_gap_GN_powers_core`
      を `hNW5 : TriominoNoWieferichBridge` 引数化。
    - 本体内部で固定 core を直参照せず、受け取った `hNW5` を dispatcher へ渡す形に変更。
    - 既存配線 (`...candidateZ_data`) では従来どおり
      `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
      を注入して挙動を維持。
  - 結果:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_from_gap_GN_powers_core`
      から `sorryAx` が消滅（clean 化）。
    - 一方 `...candidateZ_data` は固定注入を行うため `sorryAx` が残存（汚染位置の局所化が完了）。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`candidateZ_data` / `candidateZ` を clean 本体 + 固定注入 wrapper に分離）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `candidateZ_data` を clean 化:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data`
      に `(hNW5 : TriominoNoWieferichBridge)` 引数を追加。
    - 固定注入版を
      `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data_of_noWieferich_core`
      として分離。
  - `candidateZ` を clean 化:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ`
      に `(hNW5 : TriominoNoWieferichBridge)` 引数を追加。
    - 固定注入版を
      `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_of_noWieferich_core`
      として分離。
  - 外側配線:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core`
      は fixed 注入 wrapper
      `...candidateZ_of_noWieferich_core`
      を呼ぶ形へ更新（既存挙動を維持）。

- axioms 点検:
  - clean:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data`
      - `propext, Classical.choice, Quot.sound`
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ`
      - `propext, Classical.choice, Quot.sound`
  - 汚染隔離先:
    - `#print axioms ...candidateZ_data_of_noWieferich_core`
      - `sorryAx` あり
    - `#print axioms ...candidateZ_of_noWieferich_core`
      - `sorryAx` あり

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`z_core` を clean 本体 + 固定注入 wrapper に分離）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `z_core` clean 化:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core`
      に `(hNW5 : TriominoNoWieferichBridge)` を追加。
    - 本体は `...candidateZ` clean 版を呼ぶだけに整理。
  - 固定注入 wrapper:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core_of_noWieferich_core`
      を追加し、research 側 no-Wieferich core の注入を隔離。
  - 外側配線:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
      は `..._z_core_of_noWieferich_core` を呼ぶ形に更新（既存挙動維持）。

- axioms 点検:
  - clean:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core`
      - `propext, Classical.choice, Quot.sound`
  - 汚染隔離先:
    - `#print axioms ...kernel_z_core_of_noWieferich_core`
      - `sorryAx` あり
  - 伝播確認:
    - `#print axioms ...kernel`
      - `sorryAx` あり
    - `#print axioms triominoWieferichDescent_impl`
      - `sorryAx` あり

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（`kernel` と `descent_impl` を clean 本体 + 固定注入 wrapper に分離）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `kernel` clean 化:
    - 追加: `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_clean`
      - `(hNW5 : TriominoNoWieferichBridge)` を受ける clean 本体。
    - 追加: `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_of_noWieferich_core`
      - fixed injection wrapper。
    - 更新: 公開名 `...kernel`
      - wrapper 呼び出しへ整理。
  - `descent_impl` clean 化:
    - 追加: `triominoWieferichDescent_impl_clean`
      - `hStep : TriominoWieferichDescentStepB` を受ける clean 本体。
    - 追加: `triominoWieferichDescent_impl_of_noWieferich_core`
      - fixed injection wrapper（`triominoWieferichDescentStepB_impl` を注入）。
    - 更新: 公開名 `triominoWieferichDescent_impl`
      - wrapper 呼び出しへ整理。

- axioms 点検:
  - clean:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel_clean`
      - `propext, Classical.choice, Quot.sound`
    - `#print axioms triominoWieferichDescent_impl_clean`
      - `propext, Classical.choice, Quot.sound`
  - 汚染隔離先:
    - `#print axioms triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
      - `sorryAx` あり
    - `#print axioms triominoWieferichDescent_impl`
      - `sorryAx` あり

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.Main`
  - どちらも成功。

## 2026-03-07 phase-15 継続（fixed injection wrapper の一部を quarantine ファイルへ移設）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`
  - `CosmicPetalBridgeGNDescentBQuarantine.lean`

- 内容:
  - `CosmicPetalBridgeGNDescentB.lean` から、以下の fixed injection wrapper を削除:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data_of_noWieferich_core`
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_of_noWieferich_core`
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core_of_noWieferich_core`
    - `triominoWieferichDescent_impl_of_noWieferich_core`
    - `triominoWieferichDescent_impl`
  - 新規 `CosmicPetalBridgeGNDescentBQuarantine.lean` を追加し、上記 wrapper を移設。
  - clean 側 (`CosmicPetalBridgeGNDescentB.lean`) には
    - `...candidateZ_data`
    - `...candidateZ`
    - `...kernel_z_core`
    - `...kernel_clean`
    - `triominoWieferichDescent_impl_clean`
    を残し、quarantine 側は fixed injection 名義のみ保持する形に変更。

- 失敗例:
  - `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine` 初回実行で失敗。
    - エラー: `Unknown identifier GN`
    - 原因: 新規 quarantine ファイルに `open DkMath.CosmicFormulaBinom` が無かった。
    - 対処: `CosmicPetalBridgeGNDescentBQuarantine.lean` に `open DkMath.CosmicFormulaBinom` を追加して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（`kernel` 直下 consumer の追加 clean 化）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `triominoWieferichShrinkKernelInv_of_nums_of_pack` を 2 層化:
    - clean 本体:
      - `triominoWieferichShrinkKernelInv_of_nums_of_pack_clean (hNW5 : TriominoNoWieferichBridge)`
    - 固定注入 wrapper:
      - `triominoWieferichShrinkKernelInv_of_nums_of_pack`
        （`triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core` を注入）
  - clean 本体は `...kernel_clean` / `...Nums_of_pack_clean` 経由に変更し、
    `kernel` 直下 consumer を 1 本だけ外側へ押し出した。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - どちらも成功。

## 2026-03-07 phase-15 継続（projection fan をまとめて clean 化）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `kernel` 直下の projection fan を `hNW5` 引数で一括 2 層化:
    - `triominoWieferichShrinkKernel_hxmul_of_pack_clean` / wrapper
    - `triominoWieferichShrinkKernel_hy_eq_of_pack_clean` / wrapper
    - `triominoWieferichShrinkNumsInvRecipe_of_pack_clean` / wrapper
    - `triominoWieferichShrinkNumsInvCandidate_of_pack_clean` / wrapper
    - `triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack_clean` / wrapper
    - `triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack_clean` / wrapper
    - `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack_clean` / wrapper
  - 既存 no-arg 名は fixed injection wrapper として維持し、呼び出し互換は保持。

- 失敗例:
  - 初回ビルドで `implicit lambda` 由来の型不一致が発生。
    - 発生箇所: `@triominoWieferichShrinkNumsInvCandidate_of_pack_clean ...` 呼び出し
    - 症状: `p : ℕ` が bridge 引数位置に解釈される型崩れ
  - 対処:
    - `@` 呼び出しをやめ、`(hNW5 := hNW5)` を含む named argument 形式へ統一して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（LinkSpec/Shadow/CandidateEq 帯の clean API 追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `hxdiv` を clean/wrapper 2 層化:
    - `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack`（fixed injection wrapper）
  - `div_eq_shadow` 帯を clean/wrapper 2 層化:
    - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_clean`
    - `..._div_eq_shadow`（wrapper）
    - `..._div_eq_shadow_clean_x/y/z` を追加（wrapper 版 `x/y/z` は維持）
  - `LinkSpec` 消費帯へ clean API を追加:
    - `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq_clean`
    - `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidateB_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidateEq_of_pack_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hEq_of_pack_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hyz_of_pack_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hyzLt_of_pack_clean`
  - 既存 no-arg 名は互換維持（wrapper/既存定理のまま）。

- 失敗例:
  - なし（今回の変更範囲では build 失敗なし）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（CandidateEqCore 帯の clean 化）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `CandidateEqCore` 帯に clean 版を追加:
    - `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hEq_core_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hyz_core_clean`
    - `triominoWieferichShrinkNumsInvCandidate_hyzLt_core_clean`
  - これらは既に追加済みの clean 群（`...of_pack_clean`, `...LinkSpec_of_kernel_clean`,
    `...of_pack_shadow_fields_of_kernel_clean`, `...KernelNums_of_pack_clean`）から直接構成。
  - 既存 no-arg 名（non-clean 定理）は互換維持のためそのまま残置。

- 失敗例:
  - なし。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（`kernel` 層の追放試行と切り戻し）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`
  - `CosmicPetalBridgeGNDescentBQuarantine.lean`

- 内容:
  - quarantine 側へ追加:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_of_noWieferich_core`
      （fixed injection wrapper）
  - clean 側（`DescentB.lean`）で
    - `CosmicPetalBridgeGNNoWieferichResearch` import を外し、
      `hNW5_default` 引数化で本線 clean 化を試行。

- 失敗例:
  - `hNW5_default` の暗黙伝播が `kernel` 下流に広く伝播し、
    `Type mismatch` が多数発生（`kernel` 投影群と下流 glue 群で連鎖）。
  - 試行時点では build 失敗。

- 対処:
  - 破綻を避けるため、`DescentB.lean` は直前の安定形へ切り戻し。
    - `Research` import は復帰。
    - `kernel` 下流の no-arg 配線は維持。
  - 一方で quarantine への
    `...kernel_of_noWieferich_core` 追加は保持。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（InvCore / Spec / Recipe / Core 帯の clean 追加）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `InvCore / Spec / Recipe / Core` 帯へ `hNW5` 注入の clean 群を追加:
    - `triominoWieferichShrinkNumsInvCandidate_hxy/hx0/hy0/hzlt/hpB'_core_clean`
    - `triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel_clean`
    - `triominoWieferichShrinkNumsInvCandidate_exists/hzlt/hpB'/hInv_clean`
    - `triominoWieferichShrinkNumsInvRecipeB_kernel_clean`
    - `triominoWieferichShrinkNumsInvCoreB_kernel_clean`
    - `triominoWieferichShrinkKernelNumsCoreB_kernel_clean`
    - `triominoWieferichShrinkKernelEq/Inv_of_nums_core_clean`
    - `triominoWieferichShrinkKernelEqSeedTrace/Core/Seed/Nums` clean 系
    - `triominoWieferichShrinkKernelCoreB_kernel_clean`
    - `triominoWieferichShrinkKernel_hxmul/hy_eq_of_core_path_clean`
    - `triominoWieferichShrinkKernelEq/Inv_of_seed/nums_clean`
  - 既存 no-arg 公開名は互換のため据え置き（wrapper 層は未追放）。

- 失敗例:
  - 1件発生:
    - `triominoWieferichShrinkNumsInvCandidate_hx0_core_clean` 内で
      `simp [hx0]` が `q = 0 ∨ c.x' = 0` を閉じられず build 失敗。
    - 修正:
      `have hc0 : c.x' = 0 := by simpa [c] using hx0` を挟み、
      `simp [hc0]` へ変更して解消。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（KernelData / XYZ / Trace consumer 本体の clean 化）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `KernelData / XYZ / Trace` 帯を clean 本体 + no-arg wrapper 構造へ更新:
    - `triominoWieferichShrinkKernelDataB_kernel_clean`
    - `triominoWieferichShrinkXYZ_kernel_clean`
    - `triominoWieferichShrinkXYZ_core_clean`
    - `triominoWieferichShrinkTrace_core_clean`
    - `triominoWieferichShrinkXYZTraceB_core_clean`
    - `triominoWieferichShrinkXYZTraceB_impl_clean`
    - `triominoWieferichShrinkXYZCertB_impl_clean`
    - `triominoWieferichShrinkXYZB_impl_clean`
    - `triominoWieferichShrink_hzlt/hpB'/witness_clean`
    - `triominoWieferichShrinkNumsB_impl_clean`
    - `triominoWieferichShrinkCandB_impl_clean`
    - `triominoWieferichShrinkB_clean`
    - `triominoWieferichDescentStepB_impl_clean`
    - `triominoWieferichDescentCoreB_impl_clean`
  - 既存 no-arg 名は互換維持:
    - no-arg 側は
      `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
      を注入する wrapper へ更新。
  - 方針:
    - helper 追加ではなく、consumer 本体を clean core 経由へ差し替え。
    - 旧配線を保持しつつ clean 本線を上位へ延伸。

- 失敗例:
  - なし（今回の差分で新規 build 失敗なし）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（Quarantine 側 wrapper 群の補完）

- 更新:
  - `CosmicPetalBridgeGNDescentBQuarantine.lean`

- 内容:
  - `DescentB` 側から外した no-arg wrapper 群を `Quarantine` に補完:
    - `triominoWieferichShrinkKernelDataB_kernel`
    - `triominoWieferichShrinkXYZ_kernel`
    - `triominoWieferichShrinkXYZ_core`
    - `triominoWieferichShrinkTrace_core`
    - `triominoWieferichShrinkXYZTraceB_core`
    - `triominoWieferichShrinkXYZTraceB_impl`
    - `triominoWieferichShrinkXYZCertB_impl`
    - `triominoWieferichShrinkXYZB_impl`
    - `triominoWieferichShrink_hzlt`
    - `triominoWieferichShrink_hpB'`
    - `triominoWieferichShrink_witness`
    - `triominoWieferichShrinkNumsB_impl`
    - `triominoWieferichShrinkCandB_impl`
    - `triominoWieferichShrinkB`
    - `triominoWieferichDescentStepB_impl`
    - `triominoWieferichDescentCoreB_impl`
  - `triominoWieferichDescent_impl_of_noWieferich_core` が参照する
    `triominoWieferichDescentStepB_impl` を Quarantine 側に復元し、
    `DescentBQuarantine` 単体 build を復旧。

- 失敗例:
  - `DescentB.lean` からの `CosmicPetalBridgeGNNoWieferichResearch` import 除去は未達。
  - 原因:
    - `DescentB.lean` 内に `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
      直参照が 18 箇所残存（`kernel` / `of_pack` 帯）。
    - これらを clean 引数化または Quarantine 追放する追加段が必要。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - いずれも成功。

## 2026-03-07 phase-15 継続（18 箇所一括刈りの試行と切り戻し）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `kernel_noWieferich_core` の直参照 18 箇所を一括で `hNW5_default` 化し、
    `DescentB` から `NoWieferichResearch` import を外す試行を実施。
  - 併せて `localNoLift_core / existsPrime_dvd_GN_not_sq_core / noPowGN_core` を
    `hNW5` 引数付きに更新。

- 失敗例:
  - 一括 `hNW5_default` 化により、`*_clean` 群まで section 変数が伝播して
    implicit lambda 由来の型崩れが大量発生（`Type mismatch` 多発）。
  - この状態では `DescentB` build 不可。

- 対処:
  - 一括 `hNW5_default` 化は切り戻し、ビルド可能な安定形へ復帰。
  - `localNoLift_core` 系の `hNW5` 引数化のみ保持。
  - 結果として `kernel_noWieferich_core` 直参照は
    18 箇所 → 17 箇所に減少（`localNoLift_core` 由来 1 箇所を除去）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功（既知 warning のみ）。

## 2026-03-07 phase-15 継続（縦一列 4 本の Quarantine 追放）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`
  - `CosmicPetalBridgeGNDescentBQuarantine.lean`

- 内容:
  - `kernel/of_pack` 帯から、参照密度が最小の no-arg wrapper 4 本を
    `DescentB` から削除し、`Quarantine` へ同名で移設:
    - `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
    - `triominoWieferichShrinkKernelInv_of_nums_of_pack`
    - `triominoWieferichShrinkKernel_hxmul_of_pack`
    - `triominoWieferichShrinkKernel_hy_eq_of_pack`
  - `Quarantine` 側で
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_of_noWieferich_core`
    が前方参照で落ちないよう、`...kernel_clean` 直呼びに調整。

- 失敗例:
  - 初回移設で `Quarantine` にて
    `Unknown identifier triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
    （定義順）を踏んだ。
  - 修正:
    - `...kernel_of_noWieferich_core` を `...kernel_clean` 直呼びへ変更して解消。

- 効果:
  - `DescentB.lean` 内の
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    直参照が 17 箇所 → 12 箇所へ減少。
  - `NoWieferichResearch` import は未除去（残 12 箇所のため）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功。

## 2026-03-07 phase-15 継続（3 本追放 + 失敗復旧）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`
  - `CosmicPetalBridgeGNDescentBQuarantine.lean`

- 内容:
  - 先に `DescentB` のビルド失敗を復旧:
    - `No goals to be solved`（`hxdiv` 証明末尾の余分 `simpa`）を削除。
    - 削除済み wrapper 参照
      `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack`
      / `..._hy_eq_of_pack`
      を、`LinkSpec_of_pack` からの直接再構成へ置換。
  - その後、次バッチとして 3 本を `DescentB` から削除し `Quarantine` に移設:
    - `triominoWieferichShrinkKernelNums_of_pack`
    - `triominoWieferichShrinkKernelEq_of_nums_of_pack`
    - `triominoWieferichShrinkNumsInvRecipe_of_pack`
  - `DescentB` 側は `*_clean` へ切替:
    - `triominoWieferichShrinkKernelInv_of_nums_of_pack_clean`
    - `triominoWieferichShrinkKernel_hxmul_of_pack_clean`
    - `triominoWieferichShrinkKernel_hy_eq_of_pack_clean`
    - `triominoWieferichShrinkNumsInvCandidateEq_of_pack`
    - `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel`
    - `hzlt/hpB'` 回収帯の `r0` 生成と `simpa` を
      `triominoWieferichShrinkNumsInvRecipe_of_pack_clean` ベースへ置換。
  - 既定 bridge を 1 点に集約:
    - `private def triominoWieferichNoWieferichBridge_default`

- 失敗例:
  - 途中状態で `DescentB` が以下で失敗:
    - `No goals to be solved`
    - `Unknown identifier triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack`
    - `Unknown identifier triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack`
  - 原因:
    - wrapper 除去後の参照残りと、`calc` 後の余剰行。
  - 対応:
    - 上記 3 箇所を局所修正し、ビルド復旧のうえで移設作業を続行。

- 効果:
  - `DescentB.lean` 内の
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    直参照を 9 箇所 → 7 箇所へ削減。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功（既知 warning のみ）。

## 2026-03-07 phase-15 継続（NumsInvCandidate クラスター集約）

- 更新:
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `NumsInvCandidate` クラスターの fixed injection wrapper 6 本を、
    `kernel_noWieferich_core` 直注入から
    `triominoWieferichNoWieferichBridge_default` 経由へ切替:
    - `triominoWieferichShrinkNumsInvCandidate_of_pack`
    - `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack`
    - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow`
    - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x`
    - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y`
    - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z`
  - 既存 clean 本体 (`*_clean`) は不変更で、no-arg 側のみ配線を差し替え。

- 効果:
  - `DescentB.lean` 内の
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
    直参照を 7 箇所 → 1 箇所へ削減（残りは default 定義点のみ）。

- 失敗例:
  - なし（このバッチは型崩れなしで通過）。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功（既知 warning のみ）。

## 2026-03-07 phase-15 継続（default 分離で DescentB 直汚染 0）

- 更新:
  - `CosmicPetalBridgeGNNoWieferichDefault.lean`（新規）
  - `CosmicPetalBridgeGNDescentB.lean`

- 内容:
  - `DescentB` 内の最終汚染点だった
    `triominoWieferichNoWieferichBridge_default` を専用モジュールへ分離。
  - 新規ファイル `CosmicPetalBridgeGNNoWieferichDefault.lean` に
    fixed injection (`...kernel_noWieferich_core`) を 1 点集約。
  - `DescentB` は
    `import CosmicPetalBridgeGNNoWieferichResearch` を削除し、
    `import CosmicPetalBridgeGNNoWieferichDefault` へ切替。
  - 併せて `DescentB` 内の private default 定義を削除。

- 効果:
  - `DescentB.lean` 内で
    - `CosmicPetalBridgeGNNoWieferichResearch` 直 import: 0 件
    - `...kernel_noWieferich_core` 直参照: 0 件
  - 汚染注入点は `CosmicPetalBridgeGNNoWieferichDefault.lean` に隔離。

- 確認:
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine`
  - `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - すべて成功（既知 warning のみ）。
## 2026-03-07: NumsInvCandidate no-arg 4本の Quarantine 移送（小バッチ）

### 目的
- `DescentB` 側の no-arg 薄 wrapper をさらに外へ押し、`*_clean` 利用へ寄せる。
- 対象は 4 本：
  - `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z`

### 実施
- `CosmicPetalBridgeGNDescentB.lean` から上記 4 本を削除。
- 同名 wrapper を `CosmicPetalBridgeGNDescentBQuarantine.lean` に追加（fixed injection）。
- `DescentB` 内の参照を `*_clean + triominoWieferichNoWieferichBridge_default` に置換。

### 失敗と復旧
- 初回ビルドで 2 箇所失敗（`unsolved goals`）。
  - 原因：`div_eq_shadow_x/y/z` wrapper 除去で `simp` の書き換えが弱くなり、`x / q = ... ∨ q = 0` が残留。
  - 対応：該当 2 箇所を `simp [hxdiv]`（明示書き換え）へ変更して復旧。
- 復旧後、`DescentB` / `Quarantine` / `CosmicPetalBridgeGN` を再ビルドし通過。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN` : OK

### 現在地
- no-arg wrapper を 4 本追加で Quarantine 側へ移送完了。
- `DescentB` は同クラスターで `*_clean` 呼び出し主体にさらに寄った。
## 2026-03-08: NumsInvCandidate no-arg 追加搬出（4本）

### 実施
- `DescentB` から no-arg 4本を除去:
  - `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z`
- 同名 wrapper を `Quarantine` へ移設。
- `DescentB` 内の参照を `*_clean + triominoWieferichNoWieferichBridge_default` に差し替え。

### 失敗と復旧
- 2箇所で `unsolved goals`（`x / q = ... ∨ q = 0`）発生。
- 原因は `simp` が旧 wrapper 由来の書き換えに依存していたため。
- `simp [hxdiv]` へ修正して復旧。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN` : OK

### 状態
- `DescentB` 内で上記4名の no-arg 名は 0 件。
## 2026-03-08: NumsInvCandidate 本体2本の移送（of_pack / div_eq_shadow）

### 目的
- 次バッチ対象 2 本を `DescentB` から外し、`Quarantine` 側へ移送:
  - `triominoWieferichShrinkNumsInvCandidate_of_pack`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow`

### 実施
- `CosmicPetalBridgeGNDescentBQuarantine.lean` に上記 2 本の同名 wrapper を追加（fixed injection）。
- `CosmicPetalBridgeGNDescentB.lean` から上記 2 本の no-arg 本体を削除。
- `DescentB` 側には局所集約として
  - `triominoWieferichShrinkNumsInvCandidate_of_pack_default`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_default`
  を追加し、内部参照を `*_clean + default` 系へ統一。

### 失敗と復旧
- 一括置換直後に `simp` 引数へ関数項が混入し、`Invalid simp theorem` 多発。
  - 対応: 長い部分適用式を `*_default` abbrev へ集約して解消。
- 続いて 2 箇所で `x / q = ... ∨ q = 0` 未解決が発生。
  - 対応: 該当箇所を `simp [hxdiv]` に変更して解消。
- その後 linter 警告（`unnecessarySimpa`, `unusedSimpArgs`）が出たため、`simp` / `simp [hxdiv]` へ最終整形。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine` : OK
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN` : OK

### 状態
- `DescentB` 内で以下 2 名の no-arg 定義参照は 0 件:
  - `triominoWieferichShrinkNumsInvCandidate_of_pack`
  - `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow`
- `DescentB` 内の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core` 直参照は継続して 0 件。

## 2026-03-08: 数学芯の主定理文を固定（gap/body 非閉包）

### 目的
- リファクタリング中心から数学芯中心へ移るため、
  既存 core を「主定理名」で固定する。

### 実施
- `CosmicPetalBridgeGNDescentB.lean` に主定理名を追加:
  - `triominoGapBody_nonPPowerClosed_of_branchB`
    - 内容: Branch B (`p ≥ 5` 側) で `GN p (z-y) y` は `p` 乗になれない。
    - 既存 `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noPowGN_core` を明示名で再公開。
  - `triominoGapBody_selfSimilarity_breaks_of_noWieferich`
    - 内容: odd prime dispatcher (`p=3 / p≥5`) 下で gap/body 縮小 data は矛盾へ落ちる。
    - 既存 `triominoWieferichShrinkGapGNPowData_impossible_of_noWieferich` を明示名で再公開。

### 失敗と復旧
- 失敗なし（追加は既存定理への thin alias のみ）。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK

### 状態
- 「なぜ `p≥3` で閉じないか」を指す主定理文がコード上で直接参照可能になった。

## 2026-03-08: 平方世界 vs 高冪世界の比較原理を固定

### 目的
- 数学芯を明文化する比較定理を追加し、
  `p=2` と `p≥3` の分解構造差をコード上で直接参照できるようにする。

### 実施
- `CosmicPetalBridgeGNDescentB.lean` に以下を追加:
  - `triominoSquareWorld_gap_mul_sum`
  - `triominoHigherWorld_gap_mul_GN`
  - `triominoSquareVsHigher_gap_body_comparison`

### 失敗と復旧
- 初回実装で `p=2` 側を `pow_sub_pow_factor_cosmic_N` + `GN_linear` で処理したが、
  補題の返り型が `GN` ではなく和表示だったため型不一致で失敗。
- `Nat.sq_sub_sq` ベースへ差し替えて復旧。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK

### 状態
- 「同格分解（平方世界）」と「異格分解（高冪世界）」の比較が
  定理名で直接追える状態になった。

## 2026-03-08: Higher-power non-closure 主文の追加

### 目的
- 比較原理と no-closure を 1 本の主文に束ねる。

### 実施
- `CosmicPetalBridgeGNDescentB.lean` に
  `triominoHigherPower_nonClosure_principle_of_branchB` を追加。
- 内容は既存の
  - `triominoHigherWorld_gap_mul_GN`
  - `triominoGapBody_nonPPowerClosed_of_branchB`
  を合成した thin theorem。

### 失敗と復旧
- 失敗なし。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK

### 状態
- Branch B 側で「分解（gap×body）+ body 非 `p` 乗閉包」を
  1 本の定理名で参照できるようになった。

## 2026-03-08: 世界の分岐定理（Branch B）を追加

### 目的
- `p=2` と `p≥5` の世界差を、同一文脈で一息に読める総括定理として固定する。

### 実施
- `CosmicPetalBridgeGNDescentB.lean` に
  `triominoPowerWorld_bifurcation_of_branchB` を追加。
- 内容:
  - 平方世界: `z^2 - y^2 = (z - y) * (z + y)`
  - 高冪世界（Branch B）: `z^p - y^p = (z - y) * GN ...` かつ `GN ... ≠ v^p`
  を同時に返す。

### 失敗と復旧
- 失敗なし。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK

### 状態
- 「平方世界の同格閉包」と「高冪世界の非閉包」を
  1 本の定理名で対比参照できる状態になった。

## 2026-03-08: square-closure exception 総文を追加

### 目的
- 「`p=2` だけが閉包例外」という読みを、Branch B 文脈で直接参照できるようにする。

### 実施
- `CosmicPetalBridgeGNDescentB.lean` に
  `triominoSquareClosure_exception_of_branchB` を追加。
- `triominoPowerWorld_bifurcation_of_branchB` の射影として
  - 平方世界の同格分解
  - 高冪 body の非 `p` 乗閉包
  を 1 本で返す形に固定。

### 失敗と復旧
- 失敗なし。

### 検証
- `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB` : OK

### 状態
- 「平方世界の例外性」を主文として直接参照可能になった。
