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
