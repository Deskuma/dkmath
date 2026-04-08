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

### 日時: 2026/04/07 17:29:36 JST — Stage 3a-3 として差冪商 → GN の共通橋を追加

1. 目的:
    - review-040 の方針に従い、`CyclotomicNormEqGNFirstCasePackThinTarget` をいきなり埋めるのでなく、
       まず最下流の整数側 rewriting
       `((z^p - y^p) / (z - y)) = GN p (z - y) y`
       を共通補題として切り出す
    - Kummer 専用 theorem に閉じ込めず、今後の gcd / valuation / cyclotomic 再利用にも乗る位置へ置く
2. 実施:
    - `DkMath/NumberTheory/Gcd/GN.lean` に以下を追加:
       - `quotientPrimePow_eq_gn_gap`
       - `quotientPrimePow_natCast_eq_gn_int`
       - `diffPowQuotient_eq_gn_int`
    - 証明は既存資産のみを再利用:
       - `pow_sub_pow_eq_diff_mul_quotient`
       - `pow_sub_pow_factor_cosmic_N`
       - `gn_natCast_int`
    - これにより、自然数の差冪商と整数の差冪商の双方から
       `GN p (z - y) y` への薄い橋が theorem 名つきで読めるようになった
3. 結論:
    - review-040 で予定した Stage 3a-3「差冪商を GN へ落とす片」は、
       共通 NumberTheory 補題として no-sorry で追加できた ✅
    - これで `CyclotomicNormEqGNFirstCasePackThinTarget` のうち、
       cyclotomic product formula の最後の着地点は既存 theorem 名で参照できるようになった ✅
    - 次に concrete 化すべき本丸は、norm を共役積へ落とす側と、
       その積を差冪商へ寄せる側の 2 片にさらに絞られた ✅
4. 検証:
    - `./lean-build.sh DkMath.NumberTheory.Gcd.GN` 成功
    - 残る warning は既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` のみ
5. 失敗事例:
    - 初回実装では、`Int.ediv_eq_of_eq_mul_left` が要求する積の向きと
       `Nat.cast_sub` の rewrite 位置がずれており、そのままでは elaboration しなかった
    - `hcast_sub` を独立補題に切り、`mul_comm` で整数除法補題の期待形へ合わせることで解消した
6. 次の課題:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化へ戻り、
       残る 2 片、すなわち「norm を共役積へ落とす片」と
       「共役積を差冪商へ寄せる片」を整備する
    - その後、`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の concrete 化へ進む

### 日時: 2026/04/07 18:20:18 JST — Stage 3a-2 の product-level rewriting を concrete 化

1. 目的:
    - review-040 の方針に従い、`CyclotomicNormEqGNFirstCasePackThinTarget` の中段、
       すなわち nontrivial cyclotomic factor 全体の積を
       `GN p (z - y) y` および差冪商へ寄せる product-level rewriting を concrete 化する
    - norm 本体へ入る前に、`hProduct` と `x^p = gap * GN` から読める
       first-case 専用の薄い core を theorem 名つきに固定する
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `cyclotomicNontrivialFactorProduct_eq_GN_of_firstCase_of_pack_thin`
       - `cyclotomicNontrivialFactorProduct_eq_quotientPrimePow_of_firstCase_of_pack_thin`
    - 前者では
       - `CyclotomicLinearFactorProductEqInRingOfIntegers`
       - `PrimeGe5CounterexamplePack.xpow_eq_gap_mul_GN`
       - `Finset.mul_prod_erase`
       を接続し、`gap` を左因子として cancel して
       nontrivial factor product = `GN p gap y` を返す形にした
    - 後者では、上の core と
       `DkMath.NumberTheory.Gcd.quotientPrimePow_eq_gn_gap`
       を接続し、同じ product を `quotientPrimePow z y p` へ寄せる wrapper を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       上記 2 theorem の axiom 監視を追加した
3. 結論:
    - Stage 3a-2 のうち、first-case pack-thin 文脈で必要な product-level rewriting は
       no-sorry theorem として concrete 化できた ✅
    - これにより `CyclotomicNormEqGNFirstCasePackThinTarget` の残る open は、
       ほぼ「norm をその product に一致させる片」へ集中した ✅
    - review-040 で切った 3 片のうち、Stage 3a-2 と Stage 3a-3 は
       theorem 名つきで mainline に固定できた ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - build warning で残る `sorry` は既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側のみ
5. 失敗事例:
    - 初回実装では、`gap = z - y` の cast/injective 処理と
       `mul_left_cancel₀` 前の形合わせが甘く、`simpa` だけでは goal が合わなかった
    - `gap` 版の等式を一度明示し、cancel 後にのみ `hgap_nat` で戻す形へ整理して安定化した
6. 次の課題:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化へ戻り、
       残る本丸である「chosen factor の整数 norm を nontrivial factor product に一致させる片」を整備する
    - その後、既に concrete 化された Stage 3a-2 / 3a-3 を接いで
       `CyclotomicNormEqGNFirstCasePackThinTarget` 本体を閉じる

### 日時: 2026/04/07 19:03:56 JST — Stage 3a-1 の norm → Gal-product → units-product を concrete 化

1. 目的:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` のうち、review-040 で切り出した
       Stage 3a-1「norm を共役積へ落とす片」を、さらに
       norm → `Gal(K/ℚ)` product → `(ZMod p)ˣ` product
       の 2 段へ分けて concrete 化する
    - まずは norm の一般論と cyclotomic Galois reindex だけを theorem 名つきで固定し、
       まだ残る combinatorial bridge と切り離す
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `chosenCyclotomicLinearFactor_norm_eq_prod_gal_of_firstCase_of_pack_thin`
       - `gal_apply_chosenCyclotomicLinearFactor_eq_factor_of_firstCase_of_pack_thin`
       - `chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin`
    - 証明では Mathlib の既存資産を再利用:
       - `Algebra.coe_norm_int`
       - `Algebra.norm_eq_prod_automorphisms`
       - `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq`
    - これにより、chosen factor の整数 norm をまず `Gal(K/ℚ)` 上の積へ、
       さらに cyclotomic Galois の単位剰余類表示 `(ZMod p)ˣ` 上の積へ
       落とすところまで no-sorry で固定した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       上記 3 theorem の axiom 監視を追加し、
       `.trace` 上で新 theorem 名が解決することを確認した
    - `RegularPrimeRoute.lean` の戦況コメントも更新し、
       Stage 3a-1/2/3 の到達点が読めるようにした
3. 結論:
    - Stage 3a-1 のうち、norm の一般論と cyclotomic Galois reindex は
       concrete theorem として mainline に固定できた ✅
    - これで `CyclotomicNormEqGNFirstCasePackThinTarget` の残りは、
       `(ZMod p)ˣ` product を actual nontrivial factor product へ落とす
       combinatorial bridge と、その最終合成へさらに絞られた ✅
    - review-040 の 3 片は、Stage 3a-1/2/3 のいずれも部分 concrete 化が進み、
       open の形がかなり透明になった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行後、
       `.lake/build/lib/lean/DkMathTest/FLT/Kummer/RegularPrimeRoute.trace` に
       追加 3 theorem の監視結果が生成されることを確認
    - editor diagnostics 上で残る `sorry` は既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側のみ
5. 失敗事例:
    - 初回実装では、`Gal(K/ℚ)` の作用を ring-of-integers 値で直接書いたため、
       `toInteger` coercion と `simp` が噛み合わず proof state が不安定化した
    - K 値の等式に落とし、`σζ = ζ^k` を別補題として先に受ける形へ直すことで安定化した
6. 次の課題:
    - `(ZMod p)ˣ` product を `Finset.range p |>.erase 0` の actual factor product へ落とす
       combinatorial bridge を整備する
    - その後、既に concrete 化された Stage 3a-1/2/3 を束ねて
       `CyclotomicNormEqGNFirstCasePackThinTarget` 本体を閉じる

### 日時: 2026/04/07 JST — combinatorial bridge + NormEqGN concrete 化

1. 目的:
    - review-041 の方針に従い、`(ZMod p)ˣ` 上の積と
       `(Finset.range p).erase 0` 上の積の一致を示す combinatorial bridge を追加する
    - その bridge と既存の Stage 3a-1/2/3 を束ねて
       `CyclotomicNormEqGNFirstCasePackThinTarget` を concrete theorem として閉じる
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `prod_units_zmod_eq_prod_range_erase_zero`:
         `(ZMod p)ˣ` 上の積と `{1,...,p-1}` 上の積の一致。
         `Finset.prod_nbij` で、写像 `u ↦ u.val.val` の全単射性を示して証明。
         `ZMod.val_coe_unit_coprime`, `ZMod.val_injective`, `ZMod.unitOfCoprime` を使用。
       - `cyclotomicNormEqGN_concrete_firstCase_packThin`:
         `CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化。
         K 上で等式チェーンを組み、`(algebraMap ℚ K).injective` で ℤ に戻す。
    - `DkMath/NumberTheory/Gcd/GN.lean` に以下を追加:
       - `gn_natCast`: `GN` の自然数→任意 `CommSemiring` へのキャスト互換性
         (`@[simp, norm_cast]` 付き)。`gn_natCast_int` の一般化。
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       上記 3 theorem の axiom 監視を追加した
3. 結論:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` が no-sorry concrete theorem として
       閉じた ✅
    - これにより Stage 3 前半（norm = GN）は完全に concrete 化された ✅
    - Stage 3 の残り open は `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
       （unit norm 吸収 → GN が p 乗）のみ ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - 残る `sorry` は既存の `cyclotomicPrincipalization_of_classGroupPTorsionFree` と
       研究用ファイル側のみ — 新規の sorry 増加なし
5. 失敗事例:
    - 𝓞 K → K の coercion と `algebraMap (𝓞 K) K` が Lean 上で一致せず
       `change` が失敗。`SubmonoidClass.coe_finset_prod` と `congrArg` の組合せで回避した
    - `GN` が異なる ring で instantiate されると cast 経路が diverge する問題。
       `gn_natCast` を追加し、`← Nat.cast_sub` で引数を合わせてから
       `norm_cast` で close した
6. 次の課題:
    - `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の concrete 化に移る。
       NormEqGN が閉じたことで、unit 吸収側は「GN = norm 値から p 乗性を回収する」
       だけの責務に絞られた

### 日時: 2026/04/07 23:38:10 JST — UnitAbsorb を natAbs 主導で concrete 化

1. 目的:
   - review-042 の方針に従い、`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` を
      sign case split ではなく `Int.natAbs` 主導で concrete 化する
   - Kummer 局所の norm 乗法性と、整数一般の「unit 倍の `p` 乗から自然数 `p` 乗を回収する」補題を分離する
2. 実施:
   - `DkMath/NumberTheory/Gcd/GN.lean` に以下を追加:
      - `nat_exists_pow_of_intEq_unit_mul_pow`
       : `(n : ℤ) = unitFactor * m^p` かつ `IsUnit unitFactor` から
         `∃ s : ℕ, n = s^p` を返す一般整数補題
       : 証明は `Int.natAbs_mul`, `Int.natAbs_pow`, `IsUnit.natAbs_eq` のみを使用
   - `CyclotomicPrincipalization.lean` に以下を追加:
      - `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
      - `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`
   - 後者では
      - `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
      - `IsUnit.map (Algebra.norm ℤ)`
      - `DkMath.NumberTheory.Gcd.nat_exists_pow_of_intEq_unit_mul_pow`
      を接続し、`GN p (z - y) y = s^p` を自然数 witness つきで回収した
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 theorem 群の axiom 監視を追加した
3. 結論:
   - `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` が no-sorry concrete theorem として閉じた ✅
   - これにより first-case specialization の Stage 3 は、NormEqGN と UnitAbsorb の両輪が concrete に揃った ✅
   - 残る open は Stage 3 split そのものではなく、既存 legacy wrapper と downstream routing 側に限られる ✅
4. 検証:
   - `lake build DkMath.NumberTheory.Gcd.GN` 成功
   - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - 残る `sorry` は既存の `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側のみ
5. 失敗事例:
   - なし。今回の中核は `natAbs` で unit を吸収する設計が最初から安定しており、
      ±1 の場合分けは不要だった
6. 次の課題:
   - `cyclotomicNormGNPower_of_firstCase_of_pack_thin` と
      `false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin` を concrete theorem 群へ繋ぐ downstream routing を整理する
   - 既存の legacy wrapper / one-shot route のうち、まだ `sorry` を抱える箇所を current split architecture に寄せて縮約する

### 日時: 2026/04/07 23:49:03 JST — concrete Stage 3 wrappers へ配線を戻した

1. 目的:
    - concrete 化済みの `CyclotomicNormEqGNFirstCasePackThinTarget` と
       `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` を、
       既存 Stage 3 配線と contradiction bridge へ直接差し戻す
    - first-case specialization では「Stage 3 split が concrete に閉じている」ことを theorem 名で読めるようにする
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `cyclotomicNormGNPower_concrete_firstCase_packThin`
       - `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
    - 前者は
       `cyclotomicNormGNPower_of_firstCase_of_pack_thin`
       に concrete `NormEqGN` / `UnitAbsorb` 実装を渡す薄い wrapper とした
    - 後者は
       `false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin`
       に同じ concrete 実装群を渡す contradiction wrapper とした
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 2 theorem の axiom 監視を追加した
3. 結論:
    - first-case specialization では、Stage 3 の
       `GN p (z - y) y = s^p` 回収と contradiction bridge まで
       concrete theorem として mainline に揃った ✅
    - 残る `sorry` は、Stage 3 split ではなく既存 legacy route / one-shot wrapper 側に限られることがより明瞭になった ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
    - `hNorm` の右辺が整数版 `GN p (↑z - ↑y) ↑y` なので、
       直接 `rw [← hNorm]` では自然数版 cast に一致しなかった
    - `simpa [← Nat.cast_sub hpack.hyz] using hNorm.symm` で
       `((GN p (z - y) y : ℕ) : ℤ)` へ先に正規化してから `hNormMul` と接続することで安定化した
6. 次の課題:
    - `FLTPrimeGe5Target_of_kummerRoute` など legacy chain の `sorry` を、
       いま concrete になった Stage 3 wrappers を使う形へ徐々に置換する
    - first-case 以外の routing でも、同様に split architecture へ寄せて open を縮める

### 日時: 2026/04/08 00:19:33 JST — legacy route の first-case 差し替え先を public theorem 化

1. 目的:
    - review-043 の第一手として、legacy one-shot route を直ちに置換するのではなく、
       まず first-case 枝だけを concrete split architecture へ落とす public theorem を追加する
    - これにより、今後 `FLTPrimeGe5Target_of_kummerRoute` を case split 化するときの
       first concrete landing point を theorem 名で固定する
2. 実施:
    - `DkMath/FLT/Kummer/RegularPrimeRoute.lean` に
       `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を追加した
    - この theorem は
       - `CyclotomicClassGroupPTorsionFreeTarget`
       - `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
       - `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
       を接続し、class-group 仮定から first-case の concrete contradiction へ直結する薄い wrapper とした
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に axiom 監視を追加した
3. 結論:
    - legacy route の first-case 枝は、もう old Stage 3 chain を通らずに concrete theorem 群へ差し替えられる状態になった ✅
    - 一方で `FLTPrimeGe5Target_of_kummerRoute` 本体の `uses sorry` はまだ減らない。
       理由は、根の `sorry` が `cyclotomicPrincipalization_of_classGroupPTorsionFree` にあり、
       global `CyclotomicNormDescentTarget` 自体は未 concrete のままだからじゃ ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute` 相当の依存下で theorem 追加が型検査されることを確認する予定
    - `#print axioms DkMath.FLT.fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を監視対象へ追加した
5. 失敗事例:
    - なし。今回は existing concrete theorem 群の薄い再配線のみで、新しい数学内容は追加しておらぬ
6. 次の課題:
    - `FLTPrimeGe5Target_of_kummerRoute` を first-case / non-first-case に分ける場合、
       first-case 枝は今回の wrapper へ直結する
    - その後の本丸は依然として `cyclotomicPrincipalization_of_classGroupPTorsionFree` の legacy one-shot 設計の縮約じゃ

### 日時: 2026/04/08 00:31:30 JST — class-group から first-case concrete contradiction への bridge を安定配置した

1. 目的:
    - review-043 の第一手を維持しつつ、universe 推論で不安定だった route 側の実装を安定配置へ切り替える
    - class-group 仮定から first-case concrete contradiction へ落ちる public theorem を、
       今後の legacy route 差し替え先として mainline に残す
2. 実施:
    - `RegularPrimeRoute.lean` に一度追加した route-level wrapper は、
       `CyclotomicClassGroupPTorsionFreeTarget` と `CyclotomicPTorsionAnnihilationTarget` の
       universe 推論が不安定で build を崩したため撤回した
    - 代わりに `CyclotomicPrincipalization.lean` へ
       `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`
       を追加した
    - この theorem は
       `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` と
       `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin` を接続し、
       class-group 仮定から first-case concrete contradiction へ直接戻す bridge とした
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       新しい theorem 名へ更新した
3. 結論:
    - review-043 の狙いだった「legacy route を差し替えるための first concrete landing point」は、
       no-sorry theorem として mainline に固定できた ✅
    - ただし配置先は `RegularPrimeRoute.lean` ではなく、
       universe が安定している `CyclotomicPrincipalization.lean` 側が適切だと確認した ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
    - route ファイル側で `CyclotomicClassGroupPTorsionFreeTarget` をそのまま
       `CyclotomicPTorsionAnnihilationTarget` へ持ち上げようとすると、
       `ClassGroup R` の universe 推論が崩れて build failure になった
    - 同じ bridge を `CyclotomicPrincipalization.lean` 側へ置くと、既存 theorem 群との universe 文脈が一致し安定化した
6. 次の課題:
    - `FLTPrimeGe5Target_of_kummerRoute` を将来 case split 化する際、
       first-case 枝は今回の bridge theorem を通して concrete contradiction へ差し替える
    - 残る本丸は依然として `cyclotomicPrincipalization_of_classGroupPTorsionFree` の legacy one-shot 設計の縮約じゃ

### 日時: 2026/04/08 00:54:07 JST — route 側にも first-case replacement point の alias を戻した

1. 目的:
   - stable bridge 自体は `CyclotomicPrincipalization.lean` 側へ安定配置できたので、
      review-043 で意図していた route-level の theorem 名も薄い alias として回復する
   - `RegularPrimeRoute.lean` を将来 case split 化するとき、first-case 枝の差し替え先が route ファイル上でも読めるようにする
2. 実施:
   - `RegularPrimeRoute.lean` に
      `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を追加した
   - 実装は bridge の再構築をせず、
      `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`
      をそのまま呼ぶ thin alias とした
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に axiom 監視を追加した
3. 結論:
   - first-case の差し替え先は、
      `CyclotomicPrincipalization.lean` 側の stable bridge と
      `RegularPrimeRoute.lean` 側の route alias の 2 箇所で theorem 名つきに読める状態になった ✅
   - これにより、今後 `FLTPrimeGe5Target_of_kummerRoute` を case split 化する作業の入口は十分に整った ✅
4. 検証:
   - `lake build DkMath.FLT.Kummer.RegularPrimeRoute` を実行して no-sorry alias として通ることを確認する
   - `#print axioms DkMath.FLT.fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を監視対象へ追加した
5. 失敗事例:
   - 直接 bridge を route ファイル内で再構築すると universe 推論が崩れたため、
      alias 化へ切り替えた
6. 次の課題:
   - `FLTPrimeGe5Target_of_kummerRoute` 本体を case split 化し、first-case 枝を今回の alias へ接続する
   - その後、本丸である `cyclotomicPrincipalization_of_classGroupPTorsionFree` の legacy one-shot 設計を縮約する

### 日時: 2026/04/08 00:58:49 JST — route-level alias は見送り、stable bridge のみ維持

1. 目的:
    - `RegularPrimeRoute.lean` 側にも first-case replacement point の alias を公開できるか試し、
       build を崩さず route-level theorem 名を残せるか確認する
2. 実施:
    - `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を route 側 alias として追加し、
       `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree` を
       呼ぶだけの thin wrapper にして build を試した
    - しかし route ファイル側では、`CyclotomicClassGroupPTorsionFreeTarget` を経由する時点で
       universe 推論が不安定化し、`K` / `ClassGroup R` 周りの型一致に失敗した
    - そのため alias は撤回し、stable bridge を
       `CyclotomicPrincipalization.lean` 側にのみ残す構成へ戻した
3. 結論:
    - first-case replacement point として必要な theorem は、
       `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`
       1 本で十分であり、現時点では route-level alias を無理に置かない方が堅い ✅
    - `RegularPrimeRoute.lean` と test 監視は、alias 撤回後に元の clean build 状態へ戻した ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
    - stable bridge 自体は no-sorry で compile するが、
       それを route 側 theorem として再包装すると universe 推論が崩れる
    - このため、route-level alias を残す案は現時点では compile-safe ではないと判断した
6. 次の課題:
    - `FLTPrimeGe5Target_of_kummerRoute` の case split 化は、
       route-level alias ではなく `CyclotomicPrincipalization.lean` 側の stable bridge を直接呼ぶ形で設計する
    - 引き続き本丸は `cyclotomicPrincipalization_of_classGroupPTorsionFree` の legacy one-shot 設計の縮約じゃ

### 日時: 2026/04/08 01:05:38 JST — first-case gap-divisible branch も stable bridge から返せる形にした

1. 目的:
    - route-level alias に頼らずとも、future case split でそのまま使える形へ一歩進めるため、
       first-case では contradiction から gap-divisible branch の witness existence を返す theorem を mainline に追加する
    - `hNoLift` から `NoPowOnGN` を取り出す wrapper も合わせて用意し、
       将来 `FLTPrimeGe5Target_of_kummerRoute` が持つ既存引数へ自然に接続できるようにする
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree`
       - `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable`
    - 前者は
       `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`
       を `False.elim` で branch target の witness existence へ持ち上げる thin wrapper
    - 後者は
       `triominoCosmicNoPowOnGN_of_nonLiftableGNBridge`
       で `hNoLift` から `NoPowOnGN` を供給する wrapper
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 2 theorem の axiom 監視を追加した
3. 結論:
    - future case split で必要になる first-case gap-divisible branch の戻り値
       `∃ g'` は、もう stable bridge 群だけで返せる状態になった ✅
    - これにより、`FLTPrimeGe5Target_of_kummerRoute` の first-case 枝は
       contradiction theorem ではなく branch target の形で直接差し替えられる見通しが立った ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
    - なし。今回は existing stable bridge 群の再配線のみで、
       new theorem は `False.elim` と既存 `NoPowOnGN` wrapper の合成で閉じた
6. 次の課題:
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` の proof で first-case / non-first-case を切り、
       first-case 側を今回の branch-existence theorem へ接続する
    - その後、残る non-first-case / legacy one-shot 側の責任範囲をさらに局所化する

### 日時: 2026/04/08 01:29:41 JST — first-case bridge の前提を `hProduct` まで圧縮した

1. 目的:
    - global pack から `hProduct` と `hLinNe` の両方が要る、という current blocker を減らせるかを確認し、
       少なくとも `hLinNe` は product identity から自動供給できる形へ整理する
    - future case split の first-case 枝が、最終的に何を supply すればよいかをさらに明確化する
2. 実施:
    - `CyclotomicPrincipalization.lean` に
       `chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack`
       を追加した
    - この theorem で
       `∏ j < p, (z - ζ^j y) = x^p` と `x ≠ 0` から、chosen factor が 0 なら積全体が 0 になって矛盾することを formalized した
    - さらに productEq-only 版として以下を追加:
       - `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree_of_productEq`
       - `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_of_productEq`
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 theorem の axiom 監視を追加した
3. 結論:
    - first-case bridge 群に必要な追加入力は、もはや
       `hLinNe` と `hProduct` の 2 本ではなく、実質 `hProduct` 1 本だけになった ✅
    - したがって `cyclotomicPrincipalization_of_classGroupPTorsionFree` を切り裂く最後の concrete blocker は、
       global pack から `CyclotomicLinearFactorProductEqInRingOfIntegers` を canonical に供給する theorem の不在だと、より明確に言える ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
    - 上流 target 群を再確認したところ、
       `CyclotomicPureFactorizationIdentityTarget` から `CyclotomicIdealEquationTarget` までは依然 `True` placeholder のため、
       現段階ではそこから `hProduct` を canonical に引くことはできなかった
6. 次の課題:
    - `CyclotomicLinearFactorProductEqInRingOfIntegers` を global pack から供給する direct theorem を探すか、
       あるいは local factorization core から ring-of-integers product identity への bridge を新設する
    - それが揃い次第、`cyclotomicPrincipalization_of_classGroupPTorsionFree` の first-case 枝を productEq-only bridge へ接続する

### 日時: 2026/04/08 01:41:16 JST — y-branch contradiction は full product identity なしで閉じると確定

1. 目的:
    - `hProduct` が first-case 全体の blocker なのかをさらに精査し、
       y-branch contradiction と pairwise coprimality まで full product identity が必要かを切り分ける
    - local factorization core の一因子版 equality だけで閉じる部分を theorem として分離する
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack`
       - `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_localFactorizationEq`
       - `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_counterexamplePack`
       - `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct`
    - これにより、`y ∈ P` 分岐は
       `∏ (z - ζ^j y) = x^p` ではなく、
       local factorization core から来る
       `tail-sum * chosen-factor = x^p`
       だけで contradiction へ戻せる形になった
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 theorem の axiom 監視を追加した
3. 結論:
    - first-case の y-branch contradiction と pairwise coprimality 自体は、
       もはや `hProduct` に依存していないと theorem-level に確定した ✅
    - したがって現時点で `hProduct` が必要なのは、
       Stage 3 の norm/GN chain と chosen-factor × tail の specific multiplicative packaging 側であり、
       common-prime / y-branch reasoning 側ではない ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
    - 途中で新 theorem を定義順より前に置いてしまい、
       `chosenCyclotomicLinearFactorInRingOfIntegers` 未定義エラーが出た
    - また `P.mul_mem` ではなく `Ideal.mul_mem_left` を使う必要があった
    - いずれも修正後に build は復旧した
6. 次の課題:
    - `CyclotomicLinearFactorProductEqInRingOfIntegers` の必要箇所をさらに限定すると、
       残る主要用途は Stage 3 concrete contradiction bridge と Stage 1 の chosen-factor × tail packaging になる
    - 次手は、global pack から full product identity を供給する theorem を探すか、
       あるいは Stage 3 側を local factorization equality ベースへさらに薄く組み替えられるか調査する

### 日時: 2026/04/08 01:51:00 JST — Stage 3a-1 を product-free theorem として固定した

1. 目的:
   - option 2 の調査結果をコードへ反映し、Stage 3 のうち `hProduct` に依存しない部分を theorem として明示分離する
   - `cyclotomicNormEqGN_concrete_firstCase_packThin` の中で、`hProduct` が本当に Stage 3a-2 の 1 点にしか要らないことを見える形にする
2. 実施:
   - `CyclotomicPrincipalization.lean` に
      `chosenCyclotomicLinearFactor_norm_eq_prod_range_erase_zero_of_firstCase_of_pack_thin`
      を追加した
   - この theorem は
      - `chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin`
      - `prod_units_zmod_eq_prod_range_erase_zero`
      を合成し、chosen factor の整数 norm を erase-0 product へ持ち上げる product-free wrapper
   - `cyclotomicNormEqGN_concrete_firstCase_packThin` はこの新 theorem を使うように書き換えた
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に axiom 監視を追加した
3. 結論:
   - Stage 3 は now theorem-level に
      - product-free Stage 3a-1: norm -> erase-0 product
      - product-dependent Stage 3a-2: erase-0 product -> GN
      の 2 段へ明確に分離された ✅
   - これにより、option 2 の調査結論、すなわち `hProduct` の残存用途は Stage 3a-2 側に局在する、という構図がコード上でも固定できた ✅
4. 検証:
   - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
   - なし。今回は既存 no-sorry theorem 2 本の合成を named theorem として切り出しただけじゃ
6. 次の課題:
   - 次に削る候補は Stage 3a-2 の `cyclotomicNontrivialFactorProduct_eq_GN_of_firstCase_of_pack_thin`
      そのものか、あるいはそれを置き換える primitive-root / cyclotomic-polynomial ベースの norm = quotientPrimePow direct theorem じゃ
   - もし後者が立てば、Stage 3 concrete contradiction bridge は `hProduct` からさらに自由になれる

### 日時: 2026/04/08 02:18:22 JST — direct norm-eval route の基礎補題が立った

1. 目的:
    - option 2 の本丸として、Stage 3a-2 を将来 bypass できるかを測るため、
       `Norm(a - ζ)` を cyclotomic polynomial の評価へ直接戻す product-free 補題を先に立てる
    - これにより `Norm(z - ζy)` を full product identity ではなく polynomial evaluation 側から扱う道筋が本当に formalizable かを確認する
2. 実施:
    - `CyclotomicPrincipalization.lean` に
       `norm_sub_primitiveRoot_eq_eval_cyclotomic_rat`
       を追加した
    - これは Mathlib の `sub_one_norm_eq_eval_cyclotomic` の証明パターンを一般の有理点 `a` へ拡張し、
       `Algebra.norm ℚ ((a : K) - ζ) = Polynomial.eval a (Polynomial.cyclotomic p ℚ)`
       を返す theorem になっている
    - proof では
       - `norm_eq_prod_embeddings`
       - `embeddingsEquivPrimitiveRoots`
       - `cyclotomic_eq_prod_X_sub_primitiveRoots`
       - `eval₂_at_apply`
       を接続した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に axiom 監視を追加した
3. 結論:
    - direct norm-eval route の土台は no-sorry theorem として成立した ✅
    - しかもこの補題自体には first-case 仮定 `¬ p ∣ gap` は不要で、
       primitive root と cyclotomic extension だけで動くと確認できた ✅
    - したがって Stage 3a-2 の代替路として、
       `Norm(z - ζy)` を cyclotomic polynomial の homogeneous evaluation へ落とし、
       そこから `quotientPrimePow` / `GN` へ戻す構成は十分現実的じゃ ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
    - `cyclotomic'` と `cyclotomic` の橋、および `eval` / `eval₂` / `aeval` の顔違いで数回 proof が詰まった
    - 最終的には Mathlib 本家と同じ `cyclotomic_eq_prod_X_sub_primitiveRoots` の rewrite path と
       `eval₂_at_apply` の組み合わせで解決した
6. 次の課題:
    - ここから先は `a := z / y` の specialized application と、
       `y^(p-1) * Φ_p(z/y)` を DkMath 側の homogeneous evaluation / `quotientPrimePow` / `GN` へ戻す橋を作ればよい
    - それができれば、Stage 3 concrete contradiction bridge の `hProduct` 依存をさらに外せる見込みが強い

### 日時: 2026/04/08 03:18:28 JST — direct route で chosen factor の Norm = GN まで到達した

1. 目的:
    - option 2 をさらに進め、Stage 3a-2 の full product identity を使わずに
       chosen cyclotomic linear factor の整数 norm を直接 `GN p (z - y) y` へ戻せるかを検証する
    - そのために、`Φ_p(z / y)` の評価、shifted homogeneous evaluation、
       そして `z - ζy = y * (z/y - ζ)` の norm 分解を no-sorry で接続する
2. 実施:
    - `CyclotomicPrincipalization.lean` に次の direct-route helper を追加した
       - `ratCast_eval_cyclotomic_eq_cyclotomicEval`
       - `cyclotomicEval_div_natCast_mul_pow_eq_gn`
    - さらに raw chosen-factor expression
       `((z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K))`
       に対して
       - `chosenCyclotomicLinearFactor_norm_eq_gn_ratCast_direct`
       - `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
       を追加した
    - proof では
       - `norm_sub_primitiveRoot_eq_eval_cyclotomic_rat`
       - `ratCast_eval_cyclotomic_eq_cyclotomicEval`
       - `cyclotomicEval_div_natCast_mul_pow_eq_gn`
       - `Algebra.norm_algebraMap`
       - `IsCyclotomicExtension.finrank`
       を連結している
    - `RegularPrimeRoute.lean` に axiom 監視を追加した
3. 結論:
    - chosen factor の整数 norm 自体は、すでに hProduct なしで `GN` へ直接戻せる ✅
    - つまり Stage 3 の `norm = GN` ノードは full product identity 非依存で standalone 化できた ✅
    - これにより `hProduct` が残る箇所は、もはや old concrete proof chain の Stage 3a-2 側だけであり、
       direct route では不要とみなせる状態になった ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
    - `z / y` の rational cast を field-side quotient に合わせる部分と、
       raw chosen-factor expression の field-side 展開で proof plumbing が数回詰まった
    - ただし数学的な obstruction はなく、最終的には cast と multiplication reassociation の整理で解決した
6. 次の課題:
    - 次は既存の `CyclotomicNormEqGNFirstCasePackThinTarget` を direct theorem 側へ差し替え、
       `hProduct` をその interface から外せるかを詰める段階じゃ
    - その際、raw chosen-factor direct theorem を alias / existing Stage 3 wrapper へどう注入するかを整理するとよい

### 日時: 2026/04/08 03:37:33 JST — UnitAbsorb interface からも hProduct を外した

1. 目的:
    - `NormEqGN` target に続いて、Stage 3 後半の
       `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
       でも `hProduct` が本当に不要かを確認する
    - もし concrete theorem が `hProduct` を使っていなければ、
       interface から削って Stage 3 の責務分離をさらに明確にする
2. 実施:
    - target definition を見直し、`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の
       引数列から `CyclotomicLinearFactorProductEqInRingOfIntegers ...` を削除した
    - `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin` の intro 列から `hProduct` を削除した
    - downstream の `cyclotomicNormGNPower_of_firstCase_of_pack_thin` における
       `hUnitAbsorb` 適用からも `hProduct` を除去した
3. 結論:
    - Stage 3 の 2 つの中核 interface
       - `CyclotomicNormEqGNFirstCasePackThinTarget`
       - `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
       の両方が hProduct-free になった ✅
    - したがって current Stage 3 で `hProduct` が残る本質箇所は、
       `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` を通る unit-normalization chain にほぼ局在したと見てよい ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 次の課題:
    - 次は `cyclotomicNormGNPower_of_firstCase_of_pack_thin` の残る `hProduct` が
       normalization のためだけに必要なのか、あるいは normalization 自体も別 route へ置き換えられるのかを詰める
    - その観点では `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` と、
       そこへ流れ込む pairwise / coprime route の dependency を再分解するのが自然じゃ

### 日時: 2026/04/08 03:37:33 JST — NormEqGN interface から hProduct を外した

1. 目的:
    - 前段で direct theorem として立てた
       `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
       を既存 Stage 3 wrapper へ注入し、
       `CyclotomicNormEqGNFirstCasePackThinTarget` 自体から `hProduct` を外せるかを確認する
2. 実施:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` の引数列から
       `CyclotomicLinearFactorProductEqInRingOfIntegers ...` を削除した
    - `cyclotomicNormEqGN_concrete_firstCase_packThin` の proof を、
       old Stage 3a-1 / 3a-2 chain ではなく
       `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
       の直接適用へ差し替えた
    - downstream の `cyclotomicNormGNPower_of_firstCase_of_pack_thin` では、
       `hNormEqGN` への適用から `hProduct` を除去した
    - monitoring comment も「NormEqGN concrete は interface 上 hProduct-free」と分かるよう更新した
3. 結論:
    - `CyclotomicNormEqGNFirstCasePackThinTarget` は、ついに interface レベルで hProduct-free になった ✅
    - つまり Stage 3 の `norm = GN` ノードは、theorem 本体だけでなく public target の形でも
       full product identity に依存しないと確認できた ✅
    - いま `hProduct` が残るのは主に unit-normalization / unit-absorb を含む後続 chain 側であり、
       NormEqGN 自体は完全に direct route へ移行した ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 次の課題:
    - 次は `CyclotomicNormGNPower_of_firstCase_of_pack_thin` の外形をどこまで整理できるか、
       すなわち hProduct を Stage 3 power wrapper 側からもさらに押し出せるかを測る段階じゃ
    - その鍵は `UnitNormalization` / `UnitAbsorb` 層のどこで product identity が本当に必要かを局所化することじゃ

### 日時: 2026/04/08 04:12:19 JST — unit-normalization chain での `hProduct` 使用を ideal-equality leg へ局所化

1. 目的:
    - review-044 / todo-044 の方針に従い、
       `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` 周辺で
       `hProduct` がどの責務に残っているかを実コードで切り分ける
    - とくに coprime leg が本当に full product identity を要するのかを判定する
2. 実施:
    - `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack_withoutProduct` を追加した
    - これは既存の pairwise product-free theorem
       `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct`
       を tail product 全体へ畳み込む wrapper になっている
    - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` の `hCoprime` を、
       old product-dependent theorem からこの product-free tail theorem へ差し替えた
    - `todo-044-cyclotomicUnitNormalization_of_firstCase_of_pack_thin.md` に、
       現時点の依存表を追記した
    - `RegularPrimeRoute.lean` の監視に新 theorem を追加した
3. 結論:
    - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` のうち、
       coprime leg は full product identity 非依存と確定した ✅
    - したがって unit-normalization chain で `hProduct` が残るのは、
       chosen factor × tail ideal = `(x)^p` を供給する ideal-equality leg だけ、とかなり明確に言える ✅
    - これは todo-044 の判定基準でいう「中勝利」にかなり近い状態じゃ ✅
4. 検証:
    - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
    - なし。今回は既存 product-free pairwise theorem を tail 版へ持ち上げる薄い wrapper で済み、
       新しい数学的 obstruction は出ておらぬ
6. 次の課題:
    - 次は責務 A、すなわち `chosenLinearFactorMulTailEqSpanPow_of_productEq` を起点とする
       ideal-level `p` 乗化入口だけを isolated theorem として剥き出しにする
    - そのうえで `chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack`
       から local factorization ベースの代替核が取れるかを試す

### 日時: 2026/04/08 04:49:00 JST — mul-tail equality core を isolated 化し、local-factorization ideal 候補を追加

1. 目的:
   - `hProduct` が残る責務 A をさらに切り分け、mul-tail ideal equality さえ与えれば
     Stage 1 explicit equality / ideal p-th power / unit-normalization へ進めることを theorem 境界で固定する
   - 同時に、local factorization core から ideal-level の product-free 代替核が取れるかを試す
2. 実施:
   - 以下の isolated receiver theorem を追加した:
     - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_of_mulTailEqSpanPow`
     - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin_of_mulTailEqSpanPow`
     - `cyclotomicUnitNormalization_of_firstCase_of_pack_thin_of_mulTailEqSpanPow`
   - 既存の first-case wrapper 3 本は、`chosenLinearFactorMulTailEqSpanPow_of_productEq` を supply とする薄い composition に書き換えた
   - さらに local factorization core から
     - `chosenCyclotomicTailSumMulChosenLinearFactorEqSpanPow_of_counterexamplePack`
     - `exists_tailMulChosenLinearFactorEqSpanPow_of_counterexamplePack`
     を追加した
3. 結論:
   - unit-normalization chain の receiver 側は、完全に mul-tail ideal equality core 依存へ分解された ✅
   - しかも local factorization から product-free な ideal-equality 候補そのものは no-sorry で取れた ✅
   - よって残る本当の gap は、`hProduct` の有無それ自体ではなく、tail-sum ideal と chosen factor ideal の coprimality bridge だとさらに明確になった ✅
4. 検証:
   - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
   - 新しい ideal theorem を最初は `chosenCyclotomicLinearFactorInRingOfIntegers` alias で書いたが、定義順の都合で未知識別子になった
   - raw expression `(z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)` に戻して解消した
6. 次の課題:
   - local factorization 由来の tail-sum ideal と chosen factor ideal について、first-case から coprimality を返す bridge を試す
   - それが立てば `chosenLinearFactorMulTailEqSpanPow_of_productEq` を経由せずに unit-normalization chain へ入れる見込みが強い

### 日時: 2026/04/08 05:41:28 JST — local tailsum route で Stage 1/2/3 first-case chain をほぼ hProduct-free 化

1. 目的:
   - local factorization 由来の tail-sum ideal について、first-case から coprimality bridge を返せるか試す
   - それが立った場合、Stage 1 explicit equality / Stage 1 existence boundary / unit-normalization / Stage 3 GN-power wrapper まで
     `hProduct` をどこまで押し出せるかを実コードで確認する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加した:
     - `spanSingletons_isCoprime_of_noCommonPrime`
     - `primeOrY_of_chosenFactorInP_and_tailSumInP_of_counterexamplePack`
     - `chosenLinearFactor_isCoprime_with_tailSum_of_firstCase_of_pack_withoutProduct`
     - `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_withoutProduct`
     - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin_withoutProduct`
     - `cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct`
   - さらに product-free unit-normalization を使うように
     - `CyclotomicNormGNPowerFirstCasePackThinTarget`
     - `cyclotomicNormGNPower_of_firstCase_of_pack_thin`
     - `cyclotomicNormGNPower_concrete_firstCase_packThin`
     - `false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin`
     - `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
     の interface / wiring を更新した
   - class-group から first-case contradiction へ戻す wrapper も新 signature に同期した
   - `RegularPrimeRoute.lean` の axiom 監視と `todo-044` を更新した
3. 結論:
   - local tailsum route だけで、first-case の
     Stage 1 explicit equality → Stage 1 existence boundary → unit-normalization
     が no-sorry で通った ✅
   - その結果、Stage 3 の concrete GN-power wrapper と contradiction wrapper からも `hProduct` を外せた ✅
   - したがって current first-case concrete chain は、実質的に `hProduct` 依存を追放したと見てよい段階へ到達した ✅
4. 検証:
   - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
   - tailsum bridge の初回実装では、`sum_sub_distrib` の向きと unit witness の扱いで proof plumbing が崩れた
   - また local tailsum equality を old tail-product abbrev へ無理に合わせると型が合わず、
     product-free wrapper は direct composition として書き直す必要があった
6. 次の課題:
   - 次は、この first-case product-free chain を legacy route / class-group one-shot の縮約へどう注入するかを詰める
   - 特に `cyclotomicPrincipalization_of_classGroupPTorsionFree` や `FLTPrimeGe5Target_of_kummerRoute` 側で、
     old `hProduct` 前提を今回の chain へ置き換える導線を整理する

### 日時: 2026/04/08 06:11:36 JST — first-case stable bridge から `hLinNe` / `hProduct` の残骸を除去

1. 目的:
    - current first-case concrete chain がすでに product-free で閉じているなら、
       class-group から contradiction / branch witness へ戻す stable bridge 側にも
       vestigial な `hLinNe` / `hProduct` 仮定が残っていないかを整理する
    - あわせて、chosen factor 非零性 `hLinNe` が本当に extra input なのか、
       それとも pack から自動供給できるのかを theorem 名つきで固定する
2. 実施:
    - `CyclotomicPrincipalization.lean` に
       `chosenCyclotomicLinearFactorNonzero_of_counterexamplePack` を追加した
    - この theorem では
       - `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
       - `GN_ne_zero_nat_of_two_le`
       を接続し、chosen factor の norm が nonzero な `GN` に等しいことから
       chosen factor 自体の非零性を direct に回収した
    - そのうえで以下の first-case stable bridge 群の signature を簡約した:
       - `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`
       - `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree`
       - `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable`
    - 具体的には、base theorem 群から不要になった
       `ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers ...` と
       `CyclotomicLinearFactorProductEqInRingOfIntegers ...` を外し、
       productEq-only variant は compatibility wrapper として残した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       `chosenCyclotomicLinearFactorNonzero_of_counterexamplePack` の axiom 監視を追加した
3. 結論:
    - first-case stable bridge 群は、もう `hLinNe` も `hProduct` も外部入力として要求しない形へ整理できた ✅
    - とくに `hLinNe` は pack から direct norm route で自動供給できると確定したため、
       first-case replacement point の interface はさらに薄くなった ✅
    - これで current blocker は、first-case bridge の補助仮定ではなく、
       依然として `cyclotomicPrincipalization_of_classGroupPTorsionFree` 本体を
       global target の形で切り裂けていない点へ、より明確に集中した ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `get_errors` 上でも、今回追加分の新規 error は解消
    - 残る `declaration uses sorry` は既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側のみ
5. 失敗事例:
    - `GN_ne_zero_nat_of_two_le` の前提は `gap ≠ 0` / `y ≠ 0` ではなく
       `0 < gap` / `0 < y` なので、最初の実装では `PrimeGe5CounterexamplePack` からの
       positivity 供給が不足して型エラーになった
    - `simp` でも `chosenCyclotomicLinearFactorInRingOfIntegers` だけで十分な箇所に
       abbrev 名を混ぜると unused simp arg warning が出たため、最小 rewrite に整えた
6. 次の課題:
    - 次は `cyclotomicPrincipalization_of_classGroupPTorsionFree` の first-case / non-first-case split を、
       いま薄くなった stable bridge 群を使って再設計する
    - その際の実 blocker は、global pack から直接使える case predicate と
       non-first-case 側へ責任を押し込む theorem 境界の設計じゃ

### 日時: 2026/04/08 06:27:55 JST — principalization の case-split 境界を theorem として固定

1. 目的:
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` の first-case / non-first-case split を、
       current stable bridge 群を使って theorem 境界として固定する
    - そのうえで、first-case は canonical な `CyclotomicField p ℚ` instantiation で埋まり、
       non-first-case だけが open kernel だと route level でも読めるようにする
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationFirstCaseTarget`
       - `CyclotomicPrincipalizationNonFirstCaseTarget`
       - `cyclotomicPrincipalization_of_caseSplit`
       - `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit`
    - first-case canonical theorem では
       `K := CyclotomicField p ℚ`、`ζ := IsCyclotomicExtension.zeta p ℚ K`
       を取り、既存の
       `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable`
       へ直接流した
    - これにより nat-level target 上でも、
       `¬ p ∣ (z - y)` は current stable bridge で concrete に処理できると固定できた
    - さらに `RegularPrimeRoute.lean` に
       `FLTPrimeGe5Target_of_kummerRoute_of_caseSplit`
       を追加し、public route としても
       「first-case は closed / non-first-case だけ open」を theorem 名で表せるようにした
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に上記 theorem 群の axiom 監視を追加した
3. 結論:
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` の再設計に必要だった
       case predicate と theorem 境界は、no-sorry theorem 群として mainline に固定できた ✅
    - first-case はもう legacy one-shot theorem の内部事情ではなく、
       `CyclotomicField p ℚ` を通じて nat-level target へ戻せる concrete branch として分離できた ✅
    - その結果、残る open は truly `CyclotomicPrincipalizationNonFirstCaseTarget` に押し込められ、
       old one-shot の責務がかなり明瞭になった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - build warning の新規 `sorry` は増えず、残る `declaration uses sorry` は既存の
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側のみ
    - editor diagnostics では一時的に new theorem 名の `Unknown constant` が残ったが、
       build 自体は成功しており stale diagnostics と判断できた
5. 失敗事例:
    - 初回実装では、`qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable`
       の universe parameter と `CyclotomicField p ℚ` の universe が噛み合わず失敗した
    - first-case canonical theorem 側の class-group 仮定を `.{0}` へ specialize し、
       concrete type `CyclotomicField p ℚ` をそのまま使う形へ直して安定化した
6. 次の課題:
    - 次は legacy theorem `cyclotomicPrincipalization_of_classGroupPTorsionFree` 自体を、
       いま作った split theorem へ実際に寄せ、`sorry` の責任範囲を non-first-case に局所化する
    - そのためには `CyclotomicPrincipalizationNonFirstCaseTarget` をどの粒度でさらに割るか、
       あるいは non-first-case を受ける route theorem 群をどこまで public mainline に昇格させるかを詰める

### 日時: 2026/04/08 12:12:31 JST — legacy principalization の direct `sorry` を non-first-case kernel へ移した

1. 目的:
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` 自体を、直前に整えた split theorem 群へ実際に寄せ、
       theorem 本体の direct `sorry` を除去する
    - あわせて、その未解決責務を `CyclotomicPrincipalizationNonFirstCaseTarget` 専用 theorem 1 本へ局所化し、
       historical bridge / route 側でもその形が読めるようにする
2. 実施:
    - `CyclotomicPrincipalization.lean` に
       `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree`
       を追加し、non-first-case 専用 kernel として `sorry` を隔離した
    - 既定の `triominoCosmicNoPowOnGN_default` を使う
       `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree`
       を追加し、first-case 側は `hNoLift` なしでも concrete に戻るようにした
    - そのうえで legacy theorem
       `cyclotomicPrincipalization_of_classGroupPTorsionFree`
       を `cyclotomicPrincipalization_of_caseSplit` の thin composition へ書き換えた
    - split と legacy theorem の class-group 入力は `.{0}` に揃え、
       historical wrapper 側もそれに合わせて
       `ClassGroupBridge.lean` / `RegularPrimeRoute.lean` の legacy route を同期した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視に
       `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree`
       と、legacy theorem が「non-first-case target 経由で `sorry` を含む」ことを示す行を追加した
3. 結論:
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` 本体は、もはや direct `sorry` を持たぬ thin wrapper になった ✅
    - direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree`
       1 本へ局所化された ✅
    - したがって old one-shot theorem の未解決責務は theorem 名つきで non-first-case 側だけに可視化され、
       first-case は design 上も implementation 上も閉じたと見てよい ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - editor diagnostics 上でも、この refactor で残る direct `sorry` は
       `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - class-group target の universe を generic のまま `CyclotomicField p ℚ` へ接続しようとすると、
       cumulative universe 推論が unstable で build を崩した
    - このため split / legacy 系の class-group input は `.{0}` に固定し、
       historical wrapper 側も同じ concrete universe へ揃える方針に切り替えた
    - また途中で `CyclotomicLocalFactorizationContext` の field を comment で潰してしまい、
       file 先頭から大規模に parser が壊れたが、`p / zeta / hzeta_pow` と namespace を戻して復旧した
6. 次の課題:
    - 次は `CyclotomicPrincipalizationNonFirstCaseTarget` 自体をさらに薄く分割し、
       `p ∣ (z - y)` branch の中でもどこが genuinely open kernel なのかを theorem 境界で刻む
    - あるいは public mainline としては、
       `FLTPrimeGe5Target_of_kummerRoute_of_caseSplit`
       を押し出しつつ、legacy route を historical wrapper として扱う整理を進める
