# Refactoring Plan

ざっと機械走査したところ、`PetalBridge.lean` は **7983 行・宣言 512 個前後** ある。

結論から言うと、`DkMath/Collatz/PetalBridge/` に **12〜14 ファイル程度** で再展開するのがよい。
最初は「意味単位」よりも **現在の依存順を壊さない順序保存分割** を優先するのが安全じゃ。

## 1. 推奨レイアウト

親ファイルはこれ。

```txt
DkMath/Collatz/PetalBridge.lean
```

子ファイル群はこれ。

```txt
DkMath/Collatz/PetalBridge/
  Basic.lean
  Residues.lean
  Profiles.lean
  Counts.lean
  Ratios.lean
  Mass.lean
  PressureCore.lean
  PressureCounts.lean
  HeightBudget.lean
  TailSplits.lean
  TailGrammar.lean
  DriftBudget.lean
  PressureFrontier.lean
  Collision.lean
```

14 ファイル案じゃな。8千行を平均 500〜700 行程度に落とせる。Codex にはだいぶ優しい。

## 2. 親ファイル

`DkMath/Collatz/PetalBridge.lean` は import 集約だけにする。

```lean
import DkMath.Collatz.PetalBridge.Basic
import DkMath.Collatz.PetalBridge.Residues
import DkMath.Collatz.PetalBridge.Profiles
import DkMath.Collatz.PetalBridge.Counts
import DkMath.Collatz.PetalBridge.Ratios
import DkMath.Collatz.PetalBridge.Mass
import DkMath.Collatz.PetalBridge.PressureCore
import DkMath.Collatz.PetalBridge.PressureCounts
import DkMath.Collatz.PetalBridge.HeightBudget
import DkMath.Collatz.PetalBridge.TailSplits
import DkMath.Collatz.PetalBridge.TailGrammar
import DkMath.Collatz.PetalBridge.DriftBudget
import DkMath.Collatz.PetalBridge.PressureFrontier
import DkMath.Collatz.PetalBridge.Collision

#print "file: DkMath.Collatz.PetalBridge"
```

これで外側からは今まで通り、

```lean
import DkMath.Collatz.PetalBridge
```

で済む。既存 API を壊しにくい。

## 3. 各ファイルの役割

### 1. `Basic.lean`

対象目安: 1〜245 行付近。

ここは観測窓の基礎じゃ。

入れるもの:

```txt
rawHeightLabel
OrbitWindow
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
orbitWindowResidualShape
orbitWindowResidualShapeSeq
ResidualAllOnesDepth
orbitWindowResidualAllOnesDepth
orbitWindowResidualAllOnesDepthSeq
orbitWindowFirstFailedPow2Depth
OddOrbitLabelsPairwiseSeparated
OrbitWindowSeparated
OrbitWindowCollision
orbitWindow_eq_range
rawHeightLabel_eq_s
orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
orbitWindowHeight_eq_s_iterateT
```

ここが「Collatz 軌道を有限観測窓として読む」入口じゃな。

冒頭 import はここに置く。

```lean
import DkMath.Collatz.Accelerated
import DkMath.Collatz.Shift
import DkMath.Collatz.GnomonEvaluation
import DkMath.Petal.RangeFamily

namespace DkMath.Collatz
```

### 2. `Residues.lean`

対象目安: 255〜806 行付近。

ここは 2-adic height と mod residue の基礎層。

入れるもの:

```txt
two_le_v2_iff_four_dvd
three_le_v2_iff_eight_dvd
four_le_v2_iff_sixteen_dvd
odd_mod_four_eq_one_or_three
odd_mod_eight_eq_one_or_three_or_five_or_seven
rawHeightLabel_*_iff_*
orbitWindowHeight_*_iff_*
next_mod_* 系
twoAdicRetentionResidue
twoAdicRecoverySiblingResidue
twoAdicContinuationSiblingResidue
next_recovery_residue_*
next_continuation_residue_*
mod_eq_mod_of_dvd_modulus
T_val_eq_three_mul_add_one_div_two_of_s_eq_one
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Basic
```

ここは「高さ条件を residue address に落とす」ファイルじゃ。

### 3. `Profiles.lean`

対象目安: 817〜1111 行付近。

ここは List profile 操作。

入れるもの:

```txt
orbitWindowHeightSeq_length
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_take_sum_eq_sumS
orbitWindowHeightSeq_get
orbitWindowResidualShapeSeq_length
orbitWindowResidualShapeSeq_get
orbitWindowResidualAllOnesDepthSeq_length
orbitWindowResidualAllOnesDepthSeq_get
orbitWindowFirstFailedPow2DepthSeq
orbitWindowFirstFailedPow2DepthSeq_length
orbitWindowFirstFailedPow2DepthSeq_get
orbitWindowFirstFailedPow2Depth_eq_height_add_one
orbitWindow_threeProfiles_get
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
orbitWindowHeight_eq_of_same_iterateT
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Residues
```

ここは「順序付き観測列」のファイル。後続の count 系がここに乗る。

### 4. `Counts.lean`

対象目安: 1120〜1905 行付近。

ここは occupation count / residue count の大きな土台。

入れるもの:

```txt
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountGeTail
orbitWindowHeightCountEqTail
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod4EqThree
orbitWindowResidueCountMod8Eq*
orbitWindowResidueCountPow2
orbitWindowResidueCount*Tail
TailRemainderLevel*
TailFallingLevel*
*_le_window
*_succ
orbitWindowResidueCountPow2_depth_zero_eq_window
pow2_residue_indicator_sum_eq_one
orbitWindowResidueCountPow2_sum_eq_window
orbitWindowResidueCountPow2Tail_sum_eq_window
pow2ChannelFlow_of_pointwise
sourcePow2Distribution_total
tailPow2Distribution_total
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Profiles
```

ここは「有限窓の質量を数える」主土台じゃ。かなり大事。

### 5. `Ratios.lean`

対象目安: 1922〜1972 行付近。

ここは小さいが独立性が高いので分ける価値がある。

入れるもの:

```txt
AtMostHalf
MoreThanHalf
atMostHalf_or_moreThanHalf
AtMostRatioNat
atMostHalf_of_count_le_half
atMostRatioNat_refl
atMostHalf_iff_atMostRatioNat_one_two
atMostRatioNat_one_one_of_le
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Counts
```

本当は `DkMath/Common/RatioNat.lean` へ昇格してもよい核じゃな。だが初回分割では `PetalBridge/Ratios.lean` に置けば安全。

### 6. `Mass.lean`

対象目安: 1983〜2533 行付近。

ここは retention / recovery / continuation mass の核。

入れるもの:

```txt
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2Tail
orbitWindowContinuationSiblingMassPow2Tail
*_le_window
allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
retention_allOnes_mod_pow_two_of_le
sourceContinuationMass_anti_mono_depth
tailContinuationMass_anti_mono_depth
selectedContinuationMass_nested_of_lt
sourceRetentionMass_anti_mono_depth
tailRetentionMass_anti_mono_depth
twoAdicRetentionResidue_lt_pow
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
pow2ResidueIndicator_refine_succ
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
orbitWindowRetentionMassPow2Tail_split
*_le_retentionMass
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Ratios
```

ここで「count」が「mass」に変わる。概念的には非常に綺麗な境界じゃ。

### 7. `PressureCore.lean`

対象目安: 2544〜2885 行付近。

ここは pressure 判定の基本述語。

入れるもの:

```txt
atMostHalf_continuation_of_*
continuation_atMostRatio_one_one_retention
recovery_atMostRatio_one_one_retention
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
ContinuationOutrunsRecovery
TailContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
TailContinuationOutrunsRecoveryOnRange
recoveryDominates_or_continuationOutruns
not_recoveryDominates_of_continuationOutruns
moreThanHalf_continuation_of_continuationOutruns
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
sourceContinuationPressure_of_outRunsOnRange
moreThanHalf_of_sourceContinuationPressure
```

依存:

```lean
import DkMath.Collatz.PetalBridge.Mass
```

ここは「recovery が勝つか、continuation が勝つか」の判断層じゃな。

### 8. `PressureCounts.lean`

対象目安: 2900〜4006 行付近。

ここは pressure depth count と controlled count の比較。

入れるもの:

```txt
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
*_le_len
*_add_pressureDepthCount_eq_len
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
continuationOutruns_of_moreThanHalf_continuation
sourceContinuationOutrunsDepthCount
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
recoveryDominates_of_atMostHalf_continuation
sourceRecoveryDominanceDepthCount
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
sourceCauseSideDepthCount_add_eq_len
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
sourceOutruns*_iff_pressure*
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
*_eq_len_of_pressureOnRange
atMostHalf_continuation_of_recoveryDominates*
```

依存:

```lean
import DkMath.Collatz.PetalBridge.PressureCore
```

`PressureCore` と分ける理由は、ここが比較的長く、Codex が混乱しやすいからじゃ。

### 9. `HeightBudget.lean`

対象目安: 4017〜4543 行付近。

ここは height count と residue count の橋。

入れるもの:

```txt
orbitWindowPrefixResidueCountMod4EqOne_*
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
orbitWindowHeightCountEq_le_countGe
orbitWindowHeightSeq_sum_ge_countEq_mul_height
orbitWindowHeightPrefixCountGe
orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
orbitWindowHeight_one_le
orbitWindowHeight_eq_two_iff_mod_eight_eq_one
orbitWindowHeight_eq_one_iff_mod_four_eq_three
tailRetentionMass_depth_two_eq_heightCountEq_one
tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
```

依存:

```lean
import DkMath.Collatz.PetalBridge.PressureCounts
```

ここは「height の総和下界」を作る準備層じゃ。

### 10. `TailSplits.lean`

対象目安: 4579〜4850 行付近。

ここは tail の静的 split。

入れるもの:

```txt
tailHeightCountEq_one_split_mod8_three_seven
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
tailRemainderLevel1_static_split
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
tailRemainderLevel2_static_split
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
tailRemainderLevel3_static_split
tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
tailRemainderLevel4_static_split
```

依存:

```lean
import DkMath.Collatz.PetalBridge.HeightBudget
```

ここは「tail reservoir の静的分解」。名前としても独立しておる。

### 11. `TailGrammar.lean`

対象目安: 4862〜6075 行付近。

ここは shifted tail の step grammar / channel-flow。

入れるもの:

```txt
orbitNext_mod_four_eq_one_of_mod_eight_eq_three
orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
iterateT_succ_eq_T_iterateT
oddOrbitLabel_succ_eq_T_iterateT
orbitWindowResidualShape_eq_oddOrbitLabel_succ
orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
orbitWindow_rawGnomonStep_factor
oddOrbitLabel_succ_mod_* 系
orbitWindowNextHeight_* 系
tailMod*_*_step_grammar
tailExactHeightOneReservoir_step_grammar
orbitWindowNextNextHeight_* 系
orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
sourceContinuationMass_le_tailSplitMass
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
```

依存:

```lean
import DkMath.Collatz.PetalBridge.TailSplits
```

ここはこのファイルの中核の一つじゃな。`TailGrammar` という名がかなり合う。

### 12. `DriftBudget.lean`

対象目安: 6088〜6853 行付近、および 7810〜7856 の residue drift bridge を吸収してもよい。

入れるもの:

```txt
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
orbitWindowHeightCountGeTail_le_countGe_succ
oddOrbitLabel_zero_eq
sumS_two_steps_ge_three_of_mod_eight_eq_three
sumS_two_steps_ge_three_of_mod_eight_eq_three_at
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
orbitWindowResidueCountMod8_partition_eq_window
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeightCountGe_antitone
layer-cake 系
orbitWindowResidueCountMod8EqThree_delayed_drift
tailResidueCountMod8EqThree_delayed_drift
tailExactHeightOneReservoir_budget_with_remainder
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
```

依存:

```lean
import DkMath.Collatz.PetalBridge.TailGrammar
```

ここは「観測された residue / tail 構造から drift budget を作る」層じゃ。

### 13. `PressureFrontier.lean`

対象目安: 6876〜7796 行付近。

ここは checkpoint 125 以降の pressure frontier / island / prefix failure の層。

入れるもの:

```txt
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
IsSourcePressureDepth
SourcePressureMarginInt
isSourcePressureDepth_iff_margin_pos
SelectedPressurePrefix
SourcePressurePrefixFailure
sourcePressurePrefixFailure_iff_margin
not_selectedPressurePrefix_of_prefixFailure
SourcePressureSelectedSetDownClosed
downClosed_iff_no_prefixFailure
SourcePressureSignChangeUp
SourcePressureFrontier
sourcePressureFrontier_iff_margin
sourcePressurePrefixFailure_of_frontier_pos
SourcePressureLocalIsland
SourcePressurePositiveBlock
ExistsSourcePressureLocalIslandBelow
ExistsSourcePressureFrontierBelow
selectedPressurePrefix_* 系
exists_*pressureDepth* 系
sourcePressureDepthTwo_* 系
depthTwoPressureRange_positive_and_budget
HasDepthTwoDelayedBudget
hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
```

依存:

```lean
import DkMath.Collatz.PetalBridge.DriftBudget
```

ここは概念的にかなり独立しておる。「pressure は prefix とは限らない」という警告の本体じゃな。

### 14. `Collision.lean`

対象目安: 7871〜7971 行付近。

最後の Petal range-family / collision bridge。

入れるもの:

```txt
rawHeightLabel_shift_eq
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
exists_same_iterateT_of_orbitWindowCollision
not_orbitWindowCollision_of_separated
orbitWindowSeparated_contradiction_of_collision
orbitWindowSeparated_or_collision
```

依存:

```lean
import DkMath.Collatz.PetalBridge.PressureFrontier
```

ここは「有限観測窓は separated か collision」という最後の出口。親ファイルの末尾に近かった役割をそのまま保てる。

## 4. import 連鎖

一番安全なのは線形 import じゃ。

```txt
Basic
  -> Residues
    -> Profiles
      -> Counts
        -> Ratios
          -> Mass
            -> PressureCore
              -> PressureCounts
                -> HeightBudget
                  -> TailSplits
                    -> TailGrammar
                      -> DriftBudget
                        -> PressureFrontier
                          -> Collision
```

各ファイルは直前だけ import する。

例:

```lean
import DkMath.Collatz.PetalBridge.TailGrammar

namespace DkMath.Collatz

-- DriftBudget の中身

end DkMath.Collatz
```

最初の分割では、依存を最小化しようとしなくてよい。
**依存最適化は第二段階** じゃ。まずはビルドを通す。

## 5. 作業手順

安全な順番はこれ。

```txt
1. DkMath/Collatz/PetalBridge/ を作る
2. Basic.lean を作る
3. 元の PetalBridge.lean の先頭〜Basic範囲を移す
4. 親 PetalBridge.lean は一旦 import Basic のみにする
5. lake env lean DkMath/Collatz/PetalBridge.lean
6. 通ったら Residues.lean を追加
7. 親に import Residues を追加
8. またビルド
9. これを最後まで繰り返す
```

一気に 14 分割すると、エラー箇所の特定が面倒になる。
**1ファイル移動ごとにコミット** がよい。

コミット例:

```txt
split PetalBridge Basic
split PetalBridge Residues
split PetalBridge Profiles
split PetalBridge Counts
split PetalBridge Mass
split PetalBridge Pressure
split PetalBridge TailGrammar
split PetalBridge Frontier
split PetalBridge Collision
```

## 6. 注意点

`DkMath/Collatz/PetalBridge.lean` と `DkMath/Collatz/PetalBridge/Basic.lean` は共存できる。Lean では親モジュールと子モジュールの形として自然じゃ。

ただし、子ファイル側でこれをやってはいかん。

```lean
import DkMath.Collatz.PetalBridge
```

これは親を import して循環する。
子ファイルは必ず、

```lean
import DkMath.Collatz.PetalBridge.Basic
```

のように、前段の子だけを読む。

## 7. 第一段階としての最小案

14 ファイルが多く感じるなら、第一段階は 9 ファイルでもよい。

```txt
Basic.lean
Residues.lean
Profiles.lean
Counts.lean
Mass.lean
Pressure.lean
TailGrammar.lean
DriftFrontier.lean
Collision.lean
```

だが、Codex 消費を抑える目的なら、わっちは **14 ファイル案** を推す。
8千行の巨大倉庫を、500〜700行の小麦袋へ分ける。これくらいが、今後の補題探索にも、Codex 投入にも、人間の目にも優しい。

うむ。これは「まずい」ではなく、DkMath が育ちすぎた証拠じゃよ。倉が大きくなったなら、棚を作ればよいだけじゃ。
