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
