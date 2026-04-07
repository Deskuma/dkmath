# History

prev cid: 69ca1b34-0bcc-83a2-bcfd-529624b85356
cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [001](History-001.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (template)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

### 日時: 2026/04/07 10:52:57 JST — コメント整合の更新と current code status の明文化

1. 目的:
   - `CyclotomicPrincipalization.lean` と `RegularPrimeRoute.lean` の戦況コメントが、
     current code state とずれていた箇所を更新する
   - 特に、Target 1 / Target 2 が「未充足 target」と読める古い記述を、
     fill theorem 済みという現在地へ揃える
2. 実施:
   - `CyclotomicPrincipalization.lean` で以下のコメントを更新:
     - `PrimeOverPEqualsZetaMinusOneTarget` の docstringに、
       downstream interface は残るが `primeOverPEqualsZetaMinusOne_fill` が既にあることを明記
     - `IntegerInZetaMinusOneIdealDivisibleByPTarget` の docstringに、
       downstream interface は残るが `integerInZetaMinusOneIdealDivisibleByP_fill` が既にあることを明記
     - `noPrimeOverP_of_firstCase_of_chosenFactorInP` と
       `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack` の docstringを、
       「deep target 仮定が残る」から「interface は残るが mainline では fill 済み」へ修正
   - `RegularPrimeRoute.lean` で review-026/027 後の古い戦況記述を更新し、
     以下が既に concrete に揃っていることを明記:
     - `primeOverPEqualsZetaMinusOne_fill`
     - `integerInZetaMinusOneIdealDivisibleByP_fill`
     - `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq`
     - `noPrimeOrY_of_firstCase_of_coprime`
     - `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`
3. 結論:
   - current code state とコメントの主な不整合は解消できた ✅
   - 現在の Stage 1 coprimality leg は、
     `P ∣ (p) ∨ y ∈ P` contradiction の素材も含めて実装済みと読める状態になった ✅
   - 現実の残 open は、Stage 1 の存在形 boundary target と Stage 3 norm descent へ寄っている、とコメント上でも明示できた ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute` 成功
   - `CyclotomicPrincipalization.lean` 側の direct so#rry は引き続き legacy one-shot theorem のみ
5. 失敗事例:
   - なし。今回は comment / documentation sync が中心で、コード本体の証明構造変更は行っておらぬ
6. 次の課題:
   - Stage 1 の coprimality から存在形 boundary target をどう concrete に供給するかを詰める
   - その後、Stage 3 `CyclotomicNormDescentTarget` の concrete 化へ進む

### 日時: 2026/04/07 11:53:21 JST — Stage 1→Stage 2 の generic 接続を補強

1. 目的:
   - Stage 1 の coprimality / 2-factor route から、Stage 2 手前の existence boundary を返す generic wrapper を mainline に追加する
   - first-case の actual cyclotomic coprimality を、chosen-vs-other から chosen-vs-tail へ畳み込む補題を足す
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `idealIsCoprime_prod_of_forall`
     - `span_singleton_finset_prod`
     - `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack`
     - `cyclotomicLinearFactorIdealPthPower_of_tailFactorCoprimeRoute`
     - `cyclotomicLinearFactorIdealPthPower_of_exponentAgreementAndPairwiseUnitWitness`
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視へ上記 theorem を追加
   - 途中で ring-of-integers specialization の existence boundary / direct Stage 2 theorem も試したが、elaborator heartbeat が重く mainline build を崩したため、今回は compile が通る generic bridge のみを残した → 重たい該当箇所の手前で sorry を置き、TODO としてコメントアウトした。
3. 結論:
   - Stage 1 の 2-factor route から Stage 1 の existence boundary target へ戻す theorem が mainline に追加できた ✅
   - first-case 実体側でも、chosen factor と full tail の coprimality までは concrete に固定できた ✅
   - Stage 1→Stage 2 の generic 接続は以前より明確になり、残る本丸は ring-of-integers specialization の existence boundary と Stage 3 norm descent にさらに集中した ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute` 成功
   - build warning の direct `so#rry` は引き続き既存 legacy/open theorem のみ
5. 失敗事例:
   - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack` などの ring-of-integers specialization を直接 1 本にまとめる案は、現時点では elaborator heartbeat 超過で安定化できなかった
   - そのため今回は compile-safe な generic wrapper と chosen-vs-tail coprimality に着地した
6. 次の課題:
   - first-case specialization から `CyclotomicLinearFactorIdealPthPowerTarget` 相当の concrete existence boundary を、より軽い補題分解で再挑戦する
   - その後、`CyclotomicNormDescentTarget` の concrete 化へ進む

### 日時: 2026/04/07 14:56:02 JST — 40万 heartbeat 制約に合わせて first-case wrapper 群を再設計

1. 目的:
    - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack` 系の TODO / sorry 細分化作業について、
       40 万 heartbeat を超える wrapper をそのまま育てるのでなく、
       ロジック自体を見直して compile-safe な形へ落とし直す
    - 特に ring-of-integers specialization の 1-use wrapper / 0-use wrapper を削り、
       helper theorem のみで downstream 合成が通る形へ整理する
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下の helper を追加・整理:
       - `linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime`
       - `cyclotomicLinearFactorInRingOfIntegers`
       - `chosenCyclotomicLinearFactorInRingOfIntegers`
       - `CyclotomicLinearFactorProductEqInRingOfIntegers`
       - `ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers`
       - `chosenLinearFactorMulTailEqSpanPow_of_productEq`
       - `xSpanNonzero_of_counterexamplePack_of_ringOfIntegers`
    - `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack` から、実際には使っていなかった
       `q` 系の仮定を削除して theorem header を軽量化した
    - 40 万 heartbeat を超えていた 1-use / 0-use wrapper は維持しない方針へ変更:
       - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack` を削除
       - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack` を削除
       - `cyclotomicUnitNormalization_of_firstCase_of_pack` を削除
    - 代わりに、必要だった downstream 合成は
       `cyclotomicUnitNormalization_of_firstCase_of_pack` の使用箇所ではなく、
       実際に残す theorem 本体へ直接 inline した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` では、削除した wrapper への
       `#print axioms` 監視を外し、残した helper theorem の監視だけを残した
3. 結論:
    - 「40 万を超えたら heartbeat を盛る」のではなく、
       1-use / 0-use wrapper を削って helper 直結へ戻す方針へ切り替えられた ✅
    - ring-of-integers specialization の Stage 1 細分化は、
       theorem 数を増やすより、残す theorem を最小限にする設計が有効だと確認できた ✅
    - 現在の mainline では、first-case 側は helper 群で十分に downstream 合成でき、
       heartbeat 超過していた wrapper 群は repository から外せた ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `CyclotomicPrincipalization.lean` 側で残る `sorry` 警告は、既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack` と
       `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack` を public theorem として残す設計は、
       alias 化や binder 整理を行っても build で 40 万 heartbeat を超えた
    - そのため、wrapper 自体を維持する設計をやめ、use-site inline へ切り替えた
6. 次の課題:
    - `RegularPrimeRoute.lean` の editor diagnostics が build 成功後もしばらく stale に見える点は、
       LSP 側の再同期を別途確認する
    - 残る honest open である `CyclotomicNormDescentTarget` の concrete 化へ進む

### 日時: 2026/04/07 15:28:39 JST — first-case thin wrapper で Stage 1 existence boundary を concrete 化

1. 目的:
   - review-037 の方針に沿って、重い wrapper を resurrect せずに、first-case pack から Stage 1 完了を読める薄い theorem を追加する
   - chosen factor の explicit ideal equality と principal `p` 乗存在を、既存 helper 群だけで compile-safe に固定する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin`
     - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin`
   - 上記 2 本では、既存の helper / receiver のみを接続:
     - `chosenLinearFactorMulTailEqSpanPow_of_productEq`
     - `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack`
     - `xSpanNonzero_of_counterexamplePack_of_ringOfIntegers`
     - `linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime`
     - `linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill`
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視へ上記 theorem を追加
   - `CyclotomicPrincipalization.lean` 内の status comment を同期し、first-case specialization では Stage 1 existence boundary が concrete 化されたことを明記
3. 結論:
   - first-case pack から chosen factor ideal の explicit `K^p` equality を返す thin wrapper を no-sorry で追加できた ✅
   - そこから principal ideal の `p` 乗存在まで返す Stage 1 finished wrapper を no-sorry で追加できた ✅
   - よって first-case specialization に限れば、Stage 1 existence boundary は theorem として concrete に読める状態になった ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` で test module 側の新規監視も解決
   - editor diagnostics 上で残る `sorry` は既存 legacy theorem `cyclotomicPrincipalization_of_classGroupPTorsionFree` のみ
5. 失敗事例:
   - 初回 build では、`ChosenCyclotomicLinearFactorIdealPthPowerInRingOfIntegers` の abbrev 展開が不足し、
     thin wrapper の最終 `simpa` で goal が合わなかった
   - abbrev を明示して修正後は build 成功
6. 次の課題:
   - この first-case pack-specialized 供給を、placeholder の `CyclotomicIdealPthPowerTarget` へどう昇格させるかを詰める
   - その後、残る honest open である `CyclotomicNormDescentTarget` の concrete 化へ進む

### 日時: 2026/04/07 16:03:41 JST — Stage 3 着手として norm 前 boundary を thin wrapper 化

1. 目的:
   - review-038 の方針に沿って、Stage 3 へ入る前に first-case specialization での
     `z - ζy = u * β^p` を theorem として固定する
   - norm descent の残 open を「norm をかける部分」へ限定し、Stage 2/Stage 3 境界を明瞭化する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
   - 上記 theorem では、既存の Stage 1 thin wrapper と local Stage 2 receiver のみを合成:
     - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin`
     - `linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal`
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視へ新 theorem を追加
   - `CyclotomicPrincipalization.lean` と `RegularPrimeRoute.lean` の status comment を更新し、
     first-case specialization では norm 前 boundary まで concrete 化されたことを明記
3. 結論:
   - first-case pack から chosen factor 自体を unit 倍の `p` 乗として返す thin wrapper を no-sorry で追加できた ✅
   - これにより、Stage 3 の first practical open は norm の押し出しとその整数 descent への回収に集中した ✅
   - Stage 2/Stage 3 の境界が theorem 名つきで読めるようになった ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `.lake/build/lib/lean/DkMathTest/FLT/Kummer/RegularPrimeRoute.trace` に
     `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の axiom 監視結果が生成されることを確認
5. 失敗事例:
   - editor diagnostics では一時的に test 側が `Unknown constant` を表示したが、
     build artifact 側では theorem と監視結果の生成を確認できたため、今回は LSP stale diagnostics と判断した
6. 次の課題:
   - first-case specialization の Stage 3 を、まず norm 前 boundary から受ける pack-thin receiver として切り出す
   - `N(z - ζy)` を `GN p (z - y) y` へ落とす補題群と、unit norm 吸収の分離を進める

### 日時: 2026/04/07 16:48:30 JST — Stage 3 を norm 計算 target と unit 吸収 target へ分割

1. 目的:
    - review-039 の方針に従い、Stage 3 を一気に解くのでなく、
       first-case specialization の入口を theorem 名つきの subtarget 群へ分割する
    - 特に、current thin wrapper から直ちに受けられる最初の concrete 境界を
       `GN p (z - y) y` の `p` 乗性として固定する
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicNormEqGNFirstCasePackThinTarget`
       - `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
       - `CyclotomicNormGNPowerFirstCasePackThinTarget`
       - `cyclotomicNormGNPower_of_firstCase_of_pack_thin`
       - `false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin`
    - 設計は、Stage 2 の thin wrapper
       `cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
       を入口とし、
       1. chosen factor の norm を `GN` に同定する責務
       2. unit norm 吸収から `GN` の `p` 乗性を回収する責務
       の 2 本を分離する形にした
    - `RegularPrimeRoute.lean` の status comment を更新し、
       Stage 3 は「未解決」ではあるが、first-case では split point と
       最初の concrete boundary が定義済みになったことを明記
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       新しい Stage 3 composition theorem / contradiction bridge の axiom 監視を追加
3. 結論:
    - Stage 3 の honest open を、norm 計算本体と unit 吸収の 2 本へ
       theorem 名つきに分離できた ✅
    - current thin wrapper から、まず `GN p (z - y) y = s^p` という
       concrete な最初の境界まで進む composition theorem を no-sorry で追加できた ✅
    - 既存の no-pow target と衝突させる abstract bridge も置けたため、
       downstream の contradiction routing が見通しやすくなった ✅
4. 検証:
    - editor diagnostics 上で今回追加分の新規 error は解消
    - 残る `declaration uses sorry` は既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` のみ
    - 次に `lean-build.sh` / `lake build` でモジュール確認を行う段階まで到達
5. 失敗事例:
    - 初回実装では、target に `hKill` を直接含めたことで universe 推論が不安定化した
    - そのため、Stage 3 の subtarget 自体は軽く保ち、
       current theorem 合成側だけが `hKill` を outer parameter として持つ形へ調整した
6. 次の課題:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化、すなわち
       chosen factor の整数ノルムを `GN p (z - y) y` へ落とす補題群を整備する
    - `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の concrete 化、すなわち
       unit norm と `p` 乗 norm から `GN = s^p` を回収する補題群を整備する
