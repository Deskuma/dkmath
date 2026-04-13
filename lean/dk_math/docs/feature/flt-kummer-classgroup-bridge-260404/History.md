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

### 日時: 2026/04/08 13:26:58 JST — non-first-case kernel を prepare / descent の 2 段へ分割

1. 目的:
    - review-046 の方針に従い、`CyclotomicPrincipalizationNonFirstCaseTarget` を一塊の open kernel として抱えるのでなく、
       theorem 境界を `prepare` と `descent` の 2 段へ分ける
    - これにより `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` の direct `sorry` を、
       さらに下流の non-first-case descent kernel へ押し下げる
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationNonFirstCaseDatum`
       - `CyclotomicPrincipalizationNonFirstCasePrepareTarget`
       - `CyclotomicPrincipalizationNonFirstCaseDescentTarget`
       - `cyclotomicPrincipalizationNonFirstCase_of_kernelSplit`
       - `cyclotomicPrincipalizationNonFirstCasePrepare`
       - `cyclotomicPrincipalizationNonFirstCaseDescent_of_classGroupPTorsionFree`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_kernelSplit`
    - `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` は、
       canonical prepare definition と descent kernel を合成する thin wrapper へ書き換えた
    - `RegularPrimeRoute.lean` には public mainline 側の finer split として
       `FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit` を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       prepare は clean、descent kernel だけが `uses sorry` と読めるよう更新した
3. 結論:
    - non-first-case 側の open は、もはや target 1 本ではなく
       `prepare` と `descent` の 2 段へ分解して監査できる形になった ✅
    - canonical prepare は no-sorry で閉じ、direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCaseDescent_of_classGroupPTorsionFree` 1 本へさらに局所化された ✅
    - public route 側でも `FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit` により、
       same split architecture を theorem 名つきで読めるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行でも新 split 名が downstream から解決されることを確認
    - build warning の新規 `sorry` は `cyclotomicPrincipalizationNonFirstCaseDescent_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - 初回実装では datum を入力変数から独立な record にしたため、
       `hDesc data` の返り値を `∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p` へ戻せず型が合わなかった
    - そのため datum を `(p x y z q)` で parameterize し、prepare target は Prop ではなく関数型 kernel として持つ設計へ修正した
    - editor diagnostics では build success 後もしばらく `Unknown constant` が残ったが、今回も stale diagnostics と判断できた
6. 次の課題:
    - 次は `CyclotomicPrincipalizationNonFirstCaseDescentTarget` の中身をさらに valuation / reduction / witness の 2 段または 3 段へ刻めるかを調べる
    - あわせて public mainline の説明では、`FLTPrimeGe5Target_of_kummerRoute_of_caseSplit` に加え
       `FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit` を non-first-case 監査線として前へ出す

### 日時: 2026/04/08 13:44:24 JST — non-first-case descent kernel を existence 語彙へさらに refined した

1. 目的:
    - review-046 の次手として、`CyclotomicPrincipalizationNonFirstCaseDescentTarget` の open を
       そのまま `g' * GN = (x/q)^p` で抱えるのでなく、まず整数 descent existence
       `z'^p = (x/q)^p + y^p` へ押し下げる
    - これにより direct `sorry` の所在を、GN witness kernel ではなく existence kernel へさらに局所化する
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationNonFirstCaseDescentExistenceTarget`
       - `cyclotomicPrincipalizationNonFirstCaseDescent_of_existence`
       - `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_existenceKernelSplit`
    - `cyclotomicPrincipalizationNonFirstCaseDescent_of_classGroupPTorsionFree` は、
       直接 `sorry` を持つのでなく
       `cyclotomicPrincipalizationNonFirstCaseDescent_of_existence`
       を通して existence kernel から GN witness を回収する thin theorem に書き換えた
    - `RegularPrimeRoute.lean` には public mainline 側の refined split として
       `FLTPrimeGe5Target_of_kummerRoute_of_existenceKernelSplit` を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       direct `sorry` の所在が existence kernel であると読める形へ更新した
3. 結論:
    - non-first-case の open は、`prepare -> existence -> GN witness` の 3 段として監査できる形になった ✅
    - `g' * GN = (x/q)^p` への変換自体は generic theorem
       `descentExistence_exists_iff_gnReduction_exists` により no-sorry で閉じると固定できた ✅
    - direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree`
       1 本へさらに押し下げられた ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行でも refined split 追加後に downstream build が継続成功
    - build warning の新規 `sorry` は `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - editor diagnostics では今回も `Unknown constant` がしばらく残ったが、build 側では new theorem 群の型検査が通っており stale diagnostics と判断した
    - theorem 順序を `descent_of_classGroupPTorsionFree` 先置きのままにすると、
       まだ定義していない existence kernel を参照して elaboration が不安定になるため、
       existence kernel -> descent bridge の順へ並べ直した
6. 次の課題:
    - 次は existence kernel 自体を valuation / reduction のどちらへさらに押し込めるか、
       既存の peel / packet-from-error / q-adic existence 語彙との接続点を棚卸しする
    - public mainline と監視上は、`FLTPrimeGe5Target_of_kummerRoute_of_existenceKernelSplit` を
       non-first-case の最新監査線として前面に出す

### 日時: 2026/04/08 13:54:27 JST — non-first-case existence kernel を valuation / reduction の 2 段へ分割

1. 目的:
    - 直前に導入した `CyclotomicPrincipalizationNonFirstCaseDescentExistenceTarget` をさらに裂き、
       `p ∣ (z-y)` branch の bookkeeping と genuinely open な reduction を theorem 境界で分離する
    - これにより direct `sorry` の所在を existence kernel ではなく reduction kernel へさらに押し下げる
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationNonFirstCaseValuationDatum`
       - `CyclotomicPrincipalizationNonFirstCaseValuationTarget`
       - `CyclotomicPrincipalizationNonFirstCaseReductionTarget`
       - `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_valuationReductionSplit`
       - `cyclotomicPrincipalizationNonFirstCaseValuation`
       - `cyclotomicPrincipalizationNonFirstCaseReduction_of_classGroupPTorsionFree`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_valuationReductionKernelSplit`
    - `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree` は、
       canonical valuation packaging と reduction kernel を合成する thin wrapper へ書き換えた
    - `RegularPrimeRoute.lean` には public mainline 側の最細 split として
       `FLTPrimeGe5Target_of_kummerRoute_of_valuationReductionKernelSplit` を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       valuation は clean、direct `sorry` は reduction kernel のみと読める形へ更新した
3. 結論:
    - non-first-case の open は、`prepare -> valuation -> reduction -> existence -> GN witness` の 5 段として監査できる形になった ✅
    - valuation 段は canonical packaging で no-sorry に固定でき、direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCaseReduction_of_classGroupPTorsionFree`
       1 本へさらに押し下げられた ✅
    - public route 側でも `FLTPrimeGe5Target_of_kummerRoute_of_valuationReductionKernelSplit` により、
       same refined architecture を theorem 名つきで読めるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行でも split 追加後に downstream build が継続成功
    - build warning の新規 `sorry` は `cyclotomicPrincipalizationNonFirstCaseReduction_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - editor diagnostics では今回も新 theorem 名が `Unknown constant` として残ったが、build 側では route/test downstream まで型検査が通っており stale diagnostics と判断した
    - 先に reduction kernel ではなく existence kernel を direct placeholder にしたままだと、
       valuation 段を theorem 名つきで監査できないため、wrapper / kernel の責務分離が曖昧になった
6. 次の課題:
    - 次は reduction kernel を、既存の peel / packet-from-error / exceptional existence 語彙のどこへ接続できるかをさらに刻む
    - とくに `p ∣ (z-y)` 側の数学内容を、valuation packaging の下流で
       `reduction -> packet/error` の向きに押し込めるかを調べる

### 日時: 2026/04/08 14:04:38 JST — non-first-case reduction kernel を error / packet の 2 段へ分割

1. 目的:
    - valuation / reduction split の次段として、non-first-case reduction を peel 側の語彙に合わせて
       `error` と `packet` の 2 段へさらに刻む
    - これにより direct `sorry` の所在を reduction kernel ではなく packet kernel へ押し下げる
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationNonFirstCaseErrorDatum`
       - `CyclotomicPrincipalizationNonFirstCaseErrorTarget`
       - `CyclotomicPrincipalizationNonFirstCasePacketTarget`
       - `cyclotomicPrincipalizationNonFirstCaseReduction_of_errorPacketSplit`
       - `cyclotomicPrincipalizationNonFirstCaseError`
       - `cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_errorPacketKernelSplit`
    - `cyclotomicPrincipalizationNonFirstCaseReduction_of_classGroupPTorsionFree` は、
       canonical error packaging と packet kernel を合成する thin wrapper へ書き換えた
    - `RegularPrimeRoute.lean` には public mainline 側の最細 split として
       `FLTPrimeGe5Target_of_kummerRoute_of_errorPacketKernelSplit` を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       error は clean、direct `sorry` は packet kernel のみと読める形へ更新した
3. 結論:
    - non-first-case の open は、`prepare -> valuation -> error -> packet -> reduction -> existence -> GN witness` の 7 段として監査できる形になった ✅
    - error 段は canonical packaging で no-sorry に固定でき、direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree`
       1 本へさらに押し下げられた ✅
    - public route 側でも `FLTPrimeGe5Target_of_kummerRoute_of_errorPacketKernelSplit` により、
       peel 風の packet/error 語彙で non-first-case を監査できるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行でも split 追加後に downstream build が継続成功
    - build warning の新規 `sorry` は `cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - editor diagnostics では今回も route/test 側の新 theorem 名が `Unknown constant` として残ったが、build 側では downstream まで通っており stale diagnostics と判断した
    - packet/error split を route 側だけ先に追加すると、monitoring の新 theorem 名が LSP 上で解決されず見通しが悪くなるため、principalization 側の theorem 境界追加と同時に更新する方が安定した
6. 次の課題:
    - 次は packet kernel を、既存の `PacketFromError` / `PeelPthRootCore` / `TailError` 語彙のどこへ接続できるかをさらに詰める
    - そのうえで `RegularPrimeRoute.lean` の長い戦況コメントも、最新の packet/error split を主導線として同期する

### 日時: 2026/04/08 14:11:41 JST — non-first-case packet kernel を TailError / PacketFromError 語彙へさらに refined した

1. 目的:
    - 直前の packet/error split を、既存 peel 側の naming に揃えて
       `TailError` と `PacketFromError` の 2 段へさらに刻む
    - これにより direct `sorry` の所在を generic packet kernel ではなく、peel 側と対応の取りやすい PacketFromError 名の theorem へ押し下げる
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加した:
       - `CyclotomicPrincipalizationNonFirstCaseTailErrorDatum`
       - `CyclotomicPrincipalizationNonFirstCaseTailErrorTarget`
       - `CyclotomicPrincipalizationNonFirstCasePacketFromErrorTarget`
       - `cyclotomicPrincipalizationNonFirstCasePacket_of_tailErrorPacketFromErrorSplit`
       - `cyclotomicPrincipalizationNonFirstCaseTailError`
       - `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree`
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_tailErrorPacketFromErrorKernelSplit`
    - `cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree` は、
       canonical TailError packaging と PacketFromError kernel を合成する thin wrapper へ書き換えた
    - `RegularPrimeRoute.lean` には public mainline 側の最細 split として
       `FLTPrimeGe5Target_of_kummerRoute_of_tailErrorPacketFromErrorKernelSplit` を追加した
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視も、
       TailError は clean、direct `sorry` は PacketFromError kernel のみと読める形へ更新した
3. 結論:
    - non-first-case の open は、`prepare -> valuation -> error -> tailError -> packetFromError -> packet -> reduction -> existence -> GN witness` の 9 段として監査できる形になった ✅
    - direct `sorry` の所在は
       `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree`
       1 本へさらに押し下げられ、既存 peel 語彙との対応が読みやすくなった ✅
    - public route 側でも `FLTPrimeGe5Target_of_kummerRoute_of_tailErrorPacketFromErrorKernelSplit` により、
       non-first-case 側の最新 split を theorem 名つきで追えるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 実行でも split 追加後に downstream build が継続成功
    - build warning の新規 `sorry` は `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree` のみ
5. 失敗事例:
    - editor diagnostics では今回も route/test 側の新 theorem 名が `Unknown constant` として残ったが、build 側では downstream まで通っており stale diagnostics と判断した
    - TailError/PacketFromError 名を route/test 側へ先に追加すると stale diagnostics のノイズが増えるため、principalization 側の theorem 境界追加と同時に入れる方が安定した
6. 次の課題:
    - 次はこの PacketFromError 名の kernel を、既存の `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` や `PrimeGe5BranchAPeelPthRootCoreTarget` とどの粒度で接続できるかをさらに詰める
    - その後 `RegularPrimeRoute.lean` の長い戦況コメントも、今の最深 open が PacketFromError 名であることに合わせて同期する

### 日時: 2026/04/08 14:38:53 JST — Kummer TailError datum から Branch A normal form / q-support / peel exact-error を露出

1. 目的:
   - review-047 の方針に従い、`PacketFromError` kernel をこれ以上縦に割るのでなく、
     Kummer 側の `TailError` datum を既存 Branch A / peel 語彙へ no-sorry で翻訳する接続点を作る
   - 特に、`q ∣ x` かつ `q ∣ (z-y)` で入ってくる Kummer non-first-case の `q` が、
     Branch A normal form ではどちら側の support に乗るかを theorem 名つきで固定する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加した:
     - `cyclotomicPrincipalizationNonFirstCaseTailErrorDatum_normalForm`
     - `cyclotomicPrincipalizationNonFirstCaseTailErrorDatum_q_dvd_t_not_dvd_s`
     - `cyclotomicPrincipalizationNonFirstCaseTailErrorDatum_to_peelTailError`
   - 上記により、Kummer tail-error datum から:
     - Branch A normal form の `(t,s)`
     - `Nat.Coprime t s`, `Nat.Coprime t y`, `Nat.Coprime s y`, `¬ p ∣ s`
     - `q ∣ t ∧ ¬ q ∣ s`
     - peel 側 exact error equation `p * B = C + (p^(p-1) * t1^p) * E`
     までは no-sorry で回収できる形にした
   - `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree` 本体も、
     上記 adapter を先に呼んでから最後の `sorry` に入る形へ書き換え、
     open が「normal form / q-support を取った後の真の descent 部分」だと読めるようにした
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視へ
     上記 3 theorem を追加した
3. 結論:
   - Kummer non-first-case の `TailError` datum は、
     既存 Branch A 語彙へ no-sorry で翻訳できるところまで具体化できた ✅
   - `q ∣ x` かつ `q ∣ (z-y)` の Kummer prime `q` は、
     normal form では `s` 側でなく `t` 側に必ず乗ることが固定できた ✅
   - よって current blocker は、bookkeeping や exact-error 抽出ではなく、
     この `t`-side support から actual descent existence `z'^p = (x/q)^p + y^p` をどう起こすかに集中した ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` で、
     新規 adapter 3 本はいずれも `sorry` なしで監視に載ることを確認した
5. 失敗事例:
   - 初回実装では、`q ∣ (z-y)` を `hgap` で書き換える箇所を datum 全体へ `rw` してしまい、
     `q ∣ t` 抽出補題がそのままでは型検査に失敗した
   - `hqgap` フィールドだけを書き換える形へ直すことで build は復旧した
6. 次の課題:
   - 次は、今回露出した `q ∣ t ∧ ¬ q ∣ s` と peel exact-error を起点に、
     `PacketFromError` kernel の残差を
     `p ∣ t` 側の peel descent / それ以外の枝との関係でどう existence 語彙へ回収するかを詰める
   - `RegularPrimeRoute.lean` の長い戦況コメントも、
     「Kummer prime は normal form の t-side support に乗る」ことまで同期すると監査しやすい

### 日時: 2026/04/08 20:44:22 JST — review-048 に従い Kummer peel open を normal-form kernel へ押し下げ

1. 目的:
   - `review-048.md` の方針どおり、`cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree`
     をそのまま open とみなすのでなく、
     TailError / exact-error の bookkeeping を剥がした薄い kernel へ責務を押し下げる
   - `#print axioms` 監視でも、次に見るべき最深 open 名を明示化する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescentTarget`
     - `cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_normalFormDescent`
     - `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
   - 既存の
     `cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree`
     は direct `sorry` を持つ本体のままにせず、
     新設した normal-form kernel からの thin wrapper に差し替えた
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axiom 監視へ
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     を追加した
3. 結論:
   - review-048 の「exact-error data → existing Branch A peel vocabulary の adapter」を
     theorem 名つきで mainline に追加できた ✅
   - class-group 側の direct open は、
     `PeelExactErrorDescent` 全体ではなく
     `PeelNormalFormDescent_of_classGroupPTorsionFree`
     へさらに押し下げられた ✅
   - 分岐判断:
     - exact-error から直ちに既存 peel packet theorem へ接ぐ案も検討した
     - ただし既存 peel packet 側は `∃ pkt'` を返し、Kummer 側は `∃ z'` を返すため、
       まずは exact-error / datum packaging を剥がす adapter を先に固定する方が
       次の接続先比較をしやすいと判断してこちらを優先した
4. 検証:
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - build warning 上の direct `sorry` は
     `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` の新 kernel 側へ移動したことを確認
5. 失敗事例:
   - 既存 peel machinery の `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` を
     そのまま Kummer exact-error theorem に流し込む案は、
     結論語彙が `pkt'` と `z'` で異なるため、このサイクルでは直接 adapter にできなかった
6. 次の課題:
   - `CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     の仮定列と、既存 restore / realization seed / peel core の仮定列を並べ、
     `z'` existence を返す最短の接続先を特定する
   - とくに `PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget` や
     restore 側 verification 群へ接げるかを調べ、
     `(x / q)^p + y^p = z'^p` を直接返す adapter を狙う

### 日時: 2026/04/08 21:31:22 JST — restore への support mismatch と existing peel PacketFromError への接続を theorem 化

1. 目的:
   - 前回の次課題どおり、
     `CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     の仮定列を restore / realization seed / peel packet 側と突き合わせ、
     どこまで既存 API に直接接げるかを theorem 名つきで固定する
   - とくに `RealizationSeedTarget` の `q ∣ s`, `¬ q ∣ t` と、
     Kummer peel branch の `q`-support が一致するかを形式的に確かめる
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `cyclotomicPrincipalizationNonFirstCasePeelNormalForm_q_dvd_t_not_dvd_s`
     - `cyclotomicPrincipalizationNonFirstCasePeelNormalForm_false_of_q_dvd_s`
     - `CyclotomicPrincipalizationNonFirstCasePeelPacketTarget`
     - `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
   - 上記により、
     Kummer peel normal form では distinguished prime `q` が
     `t` 側に乗り `s` 側には乗らないことを、
     datum を経由せず normal-form header だけで直接読めるようにした
   - あわせて、
     既存 Branch A の `PrimeGe5BranchAValuationPeelPacketFromErrorTarget`
     へは default tail-error machinery を通して接げることを theorem 化した
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の no-sorry 監視へ
     上記 theorem を追加し、
     `RegularPrimeRouteSorry.lean` では deepest open 名を
     `PeelNormalFormDescent_of_classGroupPTorsionFree` に更新した
3. 結論:
   - `PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget` 直結は、
     仮定列の support が逆向きであるため、
     同じ distinguished prime `q` をそのまま流す route では使えぬと確定した ✅
   - 一方で、existing peel 側の最短接続先は
     `PrimeGe5BranchAValuationPeelPacketFromErrorTarget`
     であり、ここまでは now theorem-level で接続できる ✅
   - したがって current honest open は、
     `restore / realization seed` への直結ではなく、
     `pkt'` existence から Kummer の欲しい `z'` existence へ戻す新 adapter
     もしくは peel 側で `z'` を直接返す新 kernel にあると判断した ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - build warning の direct `sorry` は引き続き
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     のみ
5. 失敗事例:
   - `PrimeGe5BranchAPeelPthRootCoreTarget` へ直接接ぐ theorem も検討したが、
     こちらは seed / canonical / error の 3 つを同じ `(t1,B,C,E)` で揃える必要があり、
     今回のサイクルでは `PacketFromError` 経由の方が短く安全だった
6. 次の課題:
   - `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
     の先で得られる `∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z`
     から、Kummer 側の欲しい
     `∃ z' : ℕ, z' ^ p = (x / q) ^ p + y ^ p`
     をどう回収するかを詰める
   - 特に `PrimeGe5BranchANormalFormPacket` から `x' = x / q`, `y' = y` を伴う
     smaller-counterexample realization を返す既存 restore / packaging 補題が再利用できるかを棚卸しする

### 日時: 2026/04/08 21:42:18 JST — `pkt' -> z'` は quotient provenance だけが残差だと theorem 化

1. 目的:
   - `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
     の先で得られる `∃ pkt'` から、
     Kummer の欲しい `∃ z'` を返すために何が足りないかを theorem 境界で固定する
   - とくに `PrimeGe5BranchANormalFormPacket` に
     `pkt'.x = x / q`, `pkt'.y = y` が乗れば十分かどうかを明示化する
2. 実施:
   - `CyclotomicPrincipalization.lean` に以下を追加:
     - `cyclotomicPrincipalizationNonFirstCasePeelDescentExistence_of_packet_xyEq`
     - `CyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLiftTarget`
     - `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_packetQuotientLift`
   - 上記により、
     smaller packet `pkt'` に quotient provenance
     `pkt'.x = x / q` と `pkt'.y = y`
     が付けば、`pkt'.pack.hEq` を使うだけで
     `pkt'.z ^ p = (x / q) ^ p + y ^ p`
     が直ちに出ることを no-sorry で固定した
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の no-sorry 監視へ
     上記 2 theorem を追加した
3. 結論:
   - `∃ pkt'` から `∃ z'` への橋そのものは、実は難所ではなかった ✅
   - 真に残っているのは、
     `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
     の出力 packet に対して
     `pkt'.x = x / q` と `pkt'.y = y`
     をどう回収するか、その quotient provenance 1 点だと整理できた ✅
   - 分岐判断:
     - restore 側の `RealizationSeedTarget` や `PthRootTarget` の再利用も引き続き検討した
     - しかし same-`q` route では `q ∣ s`, `¬ q ∣ t` が必要で、
       Kummer peel 側の `q ∣ t`, `¬ q ∣ s` と support が逆向きである
     - したがってこのサイクルでは restore 直結を追うより、
       `pkt' -> z'` に必要な最小 provenance を theorem 化する方が先と判断した
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - build warning の direct `sorry` は引き続き
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     のみ
5. 失敗事例:
   - 既存 restore / packet packaging 群の再利用だけで
     `pkt'.x = x / q`, `pkt'.y = y` が即座に取れる補題は、このサイクルでは見つからなかった
   - `PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete` は
     「smaller counterexample pack + p∣gap + z'<z から packet を作る」方向であり、
     今回必要な「既存 packet に quotient provenance を付ける」方向とは逆だった
6. 次の課題:
   - `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` が返す packet について、
     original `(x,y,q)` に対する quotient provenance
     `pkt'.x = x / q`, `pkt'.y = y`
     を返す新 target / theorem を設計する
   - あるいは existing peel packet を経由せず、
     peel side で `∃ z'` を直接返す `PthRoot` 型 kernel を
     Kummer normal-form 仮定向けに新設する

### 日時: 2026/04/09 01:13:23 JST — deepest open を `PeelPacketQuotientLift` へ 1 段押し下げ

1. 目的:
   - `review-049.md` の方針に従い、
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     を thin wrapper 化して、
     direct `sorry` を `packet + quotient provenance` kernel に押し下げる
   - 監視ファイル側でも、
     deepest open がどこにあるかを theorem 名で固定する
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     を追加し、
     class-group 入力から
     `CyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLiftTarget`
     を返す新 kernel とした
   - 既存の
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
     は
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_packetQuotientLift`
     を通す thin wrapper に置き換えた
   - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` では
     `...PeelNormalFormDescent_of_classGroupPTorsionFree`
     を no-sorry 監視へ移し、
     `...PeelPacketQuotientLift_of_classGroupPTorsionFree`
     を sorry 監視へ追加した
   - `DkMathTest/FLT/Kummer/RegularPrimeRouteSorry.lean` でも
     deepest open の説明を
     `packet + quotient provenance kernel`
     に更新した
3. 結論:
   - `∃ pkt'` から `∃ z'` への no-sorry adapter 群は維持したまま、
     current honest open を
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     の 1 theorem に局所化できた ✅
   - これにより、
     `PeelNormalFormDescent` は既に bookkeeping 層へ落ちており、
     次に詰めるべき内容は
     `pkt'.x = x / q`, `pkt'.y = y`
     という quotient provenance の回収だけだと明確になった ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - build warning の direct `sorry` は
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     に移動した
5. 失敗事例:
   - 最初の差分では旧 docstring が wrapper theorem の位置に残り、
     新 kernel の docstring と連続して
     `unexpected token '/--'; expected 'lemma'`
     を引いた
   - docstring を新 kernel と wrapper の各 theorem へ付け直すことで解消した
6. 次の課題:
   - `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
     の返す `pkt'` に対して、
     original `(x,y,q)` との quotient provenance
     `pkt'.x = x / q`, `pkt'.y = y`
     を付与する最短の補題を設計する
   - 既存 restore / packaging 群のうち、
     smaller-counterexample realization から
     上記 provenance を再構成できるものがないかを、
     target の入出力単位で再棚卸しする

### 日時: 2026/04/09 03:07:14 JST — named smaller-counterexample route は structural に閉じると整理

1. 目的:
   - quotient provenance 問題を調べる中で、
     既存 restore / packet packaging 群のどこまでが genuinely open で、
     どこから先が purely structural かを theorem で固定する
   - とくに
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     のような named smaller counterexample が直接得られた場合、
     Kummer peel 側の packet/provenance bookkeeping が即座に閉じるかを確認する
2. 実施:
   - `TriominoCosmicBranchA.lean` に以下を追加:
     - `primeGe5BranchANormalFormPacket_of_counterexample`
     - `primeGe5BranchANormalFormPacket_lt_of_namedSmallerCounterexample`
   - これにより、
     `PrimeGe5CounterexamplePack p x' y' z'` と `p ∣ (z' - y')`
     があれば、same coordinates のまま
     `PrimeGe5BranchANormalFormPacket p`
     へ再包装できることを no-sorry で固定した
   - `CyclotomicPrincipalization.lean` には
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_namedSmallerCounterexample`
     を追加し、
     named smaller counterexample
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     から
     `pkt'.x = x / q`, `pkt'.y = y`
     つき packet を structural に回収できるようにした
3. 結論:
   - `packet` 生成自体はもう honest open ではない ✅
   - すなわち、
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     と `p ∣ (z' - y)` と `z' < z`
     が直接出れば、
     Kummer peel 側の `packet + quotient provenance` は
     thin adapter だけで閉じると整理できた ✅
   - したがって current arithmetic residue は、
     existing `PacketFromError` output への provenance 付与に加えて、
     named smaller counterexample をどう直接構成するか、
     という route でも読めるようになった
4. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - build warning の direct `sorry` は引き続き
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     のみ
5. 失敗事例:
   - 最初は新 theorem を `TriominoCosmicBranchA.lean` 前半へ置いたため、
     後方で定義される
     `primeGe5BranchAShapeValue_of_factorization`
     を前方参照して build が落ちた
   - theorem を normal-form 基本定理群の後ろへ移し、
     依存順に整列することで解消した
6. 次の課題:
   - `cyclotomicPrincipalizationNonFirstCasePeelPacket_of_existingPacketFromError`
     が返す arbitrary `pkt'` に provenance
     `pkt'.x = x / q`, `pkt'.y = y`
     を付ける route と、
     named smaller counterexample
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     を直接作る route のどちらが短いかを再比較する
   - とくに existing error equation / tail-error data から、
     packet を経由せず named smaller counterexample を先に立てられないかを調べる

### 日時: 2026/04/09 03:20:48 JST — deepest open を named smaller-counterexample kernel へ再圧縮

1. 目的:
   - structural packaging が既に no-sorry で閉じたことを踏まえ、
     direct `sorry` を
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     からさらに 1 段押し下げる
   - honest open を
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     の直接構成へ寄せる
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `CyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexampleTarget`
     を追加し、
     Kummer peel 仮定から
     named smaller counterexample
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     と
     `p ∣ (z' - y)`, `z' < z`
     を直接返す境界を切った
   - あわせて
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_namedSmallerCounterexampleTarget`
     を追加し、
     named smaller counterexample から packet quotient-lift が
     structural packaging だけで閉じることを theorem 化した
   - 既存の
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_classGroupPTorsionFree`
     は thin wrapper に置き換え、
     direct `sorry` は
     `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_classGroupPTorsionFree`
     へ移した
   - 監視ファイルも同期:
     - `RegularPrimeRoute.lean` では
       `...PeelPacketQuotientLift_of_classGroupPTorsionFree`
       を no-sorry 側へ移し、
       `...PeelNamedSmallerCounterexample_of_classGroupPTorsionFree`
       を sorry 側へ置いた
     - `RegularPrimeRouteSorry.lean` でも
       deepest open の説明を
       `named smaller-counterexample kernel`
       に更新した
3. 結論:
   - `packet + quotient provenance` 自体はもう honest open ではない ✅
   - current direct open は、
     class-group 入力から named smaller counterexample
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     をどう直接作るか、その 1 theorem に圧縮できた ✅
   - これにより、
     arithmetic residue の読み方も
     「arbitrary packet への provenance 付与」
     ではなく
     「named smaller counterexample の直接構成」
     へ寄せられた
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - build warning の direct `sorry` は
     `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_classGroupPTorsionFree`
     に移動した
5. 失敗事例:
   - 最初の差分では
     `cyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLift_of_namedSmallerCounterexampleTarget`
     を target 定義より前に置いてしまい、
     未定義識別子エラーで build が落ちた
   - theorem を target 定義の後ろへ移すことで解消した
6. 次の課題:
   - peel exact-error data
     `p * B = C + (p ^ (p - 1) * t1 ^ p) * E`
     と既存 tail 比較補題から、
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     を直接構成する route が本当に切れないかを詰める
   - もし `z'` existence 先行の方が短いなら、
     そこから named smaller counterexample へ戻す no-sorry bridge
     も追加検討する

### 日時: 2026/04/09 04:04:29 JST — named smaller-counterexample arithmetic を no-sorry 化し、deepest open を descent-existence core へ移動

1. 目的:
   - Kummer peel で `∃ z' : ℕ, z' ^ p = (x / q) ^ p + y ^ p`
     が得られた時点で、
     named smaller counterexample
     `PrimeGe5CounterexamplePack p (x / q) y z'`
     への昇格が purely arithmetic に閉じるかを確定する
   - その結果、direct `sorry` を
     `...PeelNamedSmallerCounterexample_of_classGroupPTorsionFree`
     からさらに 1 段押し下げ、
     `z'` existence core へ局所化する
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_hzEq`
     を追加し、
     `hzEq : z' ^ p = (x / q) ^ p + y ^ p`
     から
     `PrimeGe5CounterexamplePack p (x / q) y z'`,
     `p ∣ (z' - y)`,
     `z' < z`
     を no-sorry で構成できることを theorem 化した
   - あわせて
     `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_normalFormDescent`
     を追加し、
     peel normal-form descent target から named smaller counterexample target への昇格を
     thin wrapper 化した
   - direct `sorry` は新設の
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     にだけ残し、
     `...PeelNamedSmallerCounterexample_of_classGroupPTorsionFree`
     および
     `...PeelNormalFormDescent_of_classGroupPTorsionFree`
     は wrapper 化した
   - 監視ファイルも同期:
     - `RegularPrimeRoute.lean` に
       `...PeelNamedSmallerCounterexample_of_hzEq`
       と
       `...PeelNamedSmallerCounterexample_of_normalFormDescent`
       の no-sorry 監視を追加
     - `RegularPrimeRouteSorry.lean` では
       deepest open を
       `...PeelDescentExistenceCore_of_classGroupPTorsionFree`
       として明示した
3. 結論:
   - named smaller counterexample の arithmetic verification 自体は honest open ではない ✅
   - `PrimeGe5CounterexamplePack p (x / q) y z'`
     と `p ∣ (z' - y)` と `z' < z` は、
     class-group 理論とは独立に、
     `hzEq` だけで閉じると分かった ✅
   - current direct open は
     `∃ z', z' ^ p = (x / q) ^ p + y ^ p`
     を返す core theorem へ移動した ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - build warning の direct `sorry` は
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     に現れることを確認した
5. 失敗事例:
   - 最初の差分では `ZMod p` 上の Frobenius を手書きしていて、
     exponent rewrite が instance dependency と衝突し build が落ちた
   - `ZMod.pow_card` を直接使う形へ簡約して解消した
6. 次の課題:
   - `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     の input 仮定列に対し、
     class-group / principalization 側から `∃ z'` を返す最短 adapter を設計する
   - 既存 restore 側の `RealizationSeed` ではなく、
     Kummer peel normal-form 専用の `z'` existence theorem として閉じる方が
     statement 的に薄いかを再比較する

### 日時: 2026/04/09 04:53:00 JST — Stage 3 `NormDescent` から non-first-case / peel core への adapter 群を追加

1. 目的:
   - current open である
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     が、本質的には global Stage 3
     `CyclotomicNormDescentTarget`
     にのみ依存しているのかを theorem-level に固定する
   - これにより、peel local arithmetic が未解決なのではなく、
     unresolved stage は norm descent 側だと明示する
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_normDescent`
     を追加し、
     `hNorm : CyclotomicNormDescentTarget`
     から generic equivalence
     `descentExistence_exists_iff_gnReduction_exists`
     を通して
     refined non-first-case existence target
     `∃ z', z' ^ p = (x / q) ^ p + y ^ p`
     を返す theorem を置いた
   - あわせて
     `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_normDescent`
     と
     `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_normDescent`
     を追加し、
     peel local 仮定列は `hNorm` があれば全て wrapper で閉じることを固定した
   - `RegularPrimeRoute.lean` の no-sorry 監視にも、
     上記 3 theorem を追加した
3. 結論:
   - non-first-case existence target は Stage 3 `NormDescent` から直接 supply できる ✅
   - peel normal-form descent / named smaller-counterexample も、
     local exact-error kernel の独自数学を要求せず、
     `hNorm` があれば generic bridge + arithmetic wrapper だけで閉じる ✅
   - したがって current class-group-side open は
     「peel 固有 kernel」ではなく、
     class-group / principalization mainline のどこで
     `CyclotomicNormDescentTarget`
     を concrete に supply するか、
     その設計問題として読める ✅
4. 検証:
   - 次の 3 本を回して確認する:
     `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization`
     `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute`
     `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry`
5. 次の課題:
   - `CyclotomicNormDescentTarget` から
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     へ至る non-circular route を、
     refined class-group route
     (`hCl + hUnit + hNorm`)
     と legacy one-shot route のどちらで first-class theorem 化するか決める
   - 必要なら
     `...of_refinedClassGroupRoute`
     形式の theorem を追加して、
     Stage 1 / Stage 2 / Stage 3 の依存関係をさらに明示する

### 日時: 2026/04/09 12:28:54 JST — refined class-group route から Stage 3 receiver / peel core への adapter 名を固定

1. 目的:
   - review-050 に従い、
     current open を「peel 固有 kernel」ではなく
     refined class-group route における Stage 3 receiver 問題として読むため、
     `hCl + hUnit + hNorm`
     から current peel core までの non-circular dependency を theorem 名で固定する
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `cyclotomicNormDescent_of_refinedClassGroupRoute`
     を追加し、
     refined route 上の Stage 3 receiver は `hNorm` そのものだと明示した
   - あわせて
     `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_refinedClassGroupRoute`
     と
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_refinedClassGroupRoute`
     を追加し、
     refined route から
     non-first-case existence / peel normal-form descent core へ落ちる chain を
     wrapper として固定した
   - `RegularPrimeRoute.lean` の no-sorry 監視にも上記 3 theorem を追加した
3. 結論:
   - current `sorry` は依然として
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     に残るが、
     refined route 側では
     `hNorm` が与えられれば peel core まで non-circular に閉じることが明示された ✅
   - したがって、今後の mainline 作業対象は
     「class-group / unit route から `CyclotomicNormDescentTarget` をどう concrete に supply するか」
     であって、peel 局所算術ではないという読みがさらに強くなった ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     のような receiver theorem を新設するか、
     あるいは `CyclotomicNormDescentTarget` の concrete 化を直接進めるかを決める
   - もし receiver theorem を先に置くなら、
     `hCl + hUnit`
     から `hNorm` へ必要な残部品が本当に何かを棚卸しし、
     theorem target を最薄に設計する

### 日時: 2026/04/09 12:56:25 JST — `hCl + hUnit ⟹ hNorm` receiver theorem を切り、Stage 3 open を first-class 化

1. 目的:
   - review-051 の提案どおり、
     次の作業対象を
     `CyclotomicNormDescentTarget`
     の concrete receiver へ明示的に移す
   - そのために
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     を theorem として立て、
     `hCl + hUnit`
     から downstream がどこまで wrapper で閉じるかを固定する
2. 実施:
   - `CyclotomicPrincipalization.lean` に
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     を追加した
     これは現時点では direct `sorry` を含むが、
     Stage 3 receiver 問題そのものを first-class theorem として隔離する役割を持つ
   - あわせて downstream wrapper として
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_and_unitNormalization`
     `cyclotomicPrincipalizationNonFirstCaseDescentExistence_of_classGroupPTorsionFree_and_unitNormalization`
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_and_unitNormalization`
     を追加し、
     `hCl + hUnit + hNorm` ではなく
     `hCl + hUnit`
     だけを引数に取る mainline 名を先に確保した
   - `RegularPrimeRoute.lean` と `RegularPrimeRouteSorry.lean` の監視にも、
     上記 theorem 群を追加した
3. 結論:
   - Stage 3 receiver 問題
     `hCl + hUnit ⟹ hNorm`
     は theorem 名つきの独立 open として切り出せた ✅
   - これにより、
     今後の探索対象は
     `CyclotomicNormDescentTarget` の concrete 化、
     もしくはそのために不足している最小補題の棚卸しだと明確になった ✅
   - 現在 build warning 上の direct `sorry` は
     旧 core
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     と
     新 receiver theorem
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     の 2 箇所に現れる
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     の proof に本当に必要な残仮定が
     `hCl + hUnit` だけか、
     それとも Stage 3 用の追加 receiver が 1 本要るかを棚卸しする
   - もし追加 receiver が必要なら、
     それを `CyclotomicNormDescentTarget` の直前にある最薄 theorem として isolated に切る

### 日時: 2026/04/09 13:11:37 JST — Stage 3 receiver の棚卸しを theorem 分解で実装

1. 目的:
   - `hCl + hUnit ⟹ hNorm`
     という receiver theorem に本当に何が不足しているかを棚卸しし、
     direct `sorry` をより薄い branch-specific theorem へ押し下げる
2. 実施:
   - no-sorry bridge として
     `cyclotomicNormDescent_of_caseSplit`
     を追加し、
     global `CyclotomicNormDescentTarget` は
     first-case branch と non-first-case branch を束ねれば再構成できることを固定した
   - あわせて
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_nonFirstCase`
     を追加し、
     class-group 仮定のもとでは first-case branch は既に concrete なので、
     残る Stage 3 open は non-first-case branch だけだと theorem 化した
   - その上で direct `sorry` を持つ theorem として
     `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     を新設し、
     旧
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization`
     は thin wrapper に置き換えた
   - 監視も更新し、
     `RegularPrimeRoute.lean` では no-sorry 側に
     `...NormDescent_of_caseSplit`
     と
     `...NormDescent_of_classGroupPTorsionFree_and_nonFirstCase`
     を追加、
     `RegularPrimeRouteSorry.lean` では new deepest Stage 3 receiver を
     `...NormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     として追跡する形にした
3. 結論:
   - 棚卸しの結果、
     `hCl + hUnit ⟹ hNorm`
     の missing piece は
     global receiver 全体ではなく
     non-first-case branch 専用 receiver 1 本だと整理できた ✅
   - つまり Stage 3 の honest open は、
     first / non-first split のうち
     non-first-case branch にのみ残ると theorem-level に言えるようになった ✅
   - build warning 上の direct `sorry` も、
     旧 peel core
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     と、
     新 Stage 3 branch receiver
     `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     の 2 箇所になった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     の proof に必要な最小追加 receiver を棚卸しし、
     必要ならさらにその 1 theorem へ direct `sorry` を押し下げる
   - あるいは current branch receiver 自体を、
     existing Stage 1 / Stage 2 no-sorry 部品から直接埋められないかを再検討する

## 2026/04/09 13:44:25 JST

1. 背景:
   - 次の試行として、
     existing Stage 1 / Stage 2 no-sorry 部品から
     current Stage 3 non-first-case receiver を直接埋められないかを再検討した
   - そのため、
     `CyclotomicUnitNormalizationTarget`
     の generic 出口と、
     current non-first-case `NormDescent` receiver の間に
     missing theorem 境界があるかを棚卸しした
2. 実施:
   - `CyclotomicNormDescentNonFirstCaseUnitNormalizedReceiverTarget`
     を追加し、
     non-first-case 側の missing piece を
     「unit-normalized chosen factor
     `z - ζy = unitFactor * β^p`
     から nat-level descent witness を返す receiver」
     として明示した
   - あわせて
     `cyclotomicNormDescentNonFirstCase_of_unitNormalizationAndReceiver`
     を no-sorry で追加し、
     `CyclotomicUnitNormalizationTarget`
     から canonical `CyclotomicField p ℚ` specialization を通して
     上記 receiver へ接ぐ routing 自体は既存部品だけで閉じることを fixed した
   - その結果、
     `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     は thin wrapper 化し、
     direct `sorry` は
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     へ押し下げた
   - 監視も更新し、
     `RegularPrimeRoute.lean` では
     `...NonFirstCase_of_unitNormalizationAndReceiver`
     と
     `...NonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     を no-sorry 側へ追加し、
     `RegularPrimeRouteSorry.lean` では new deepest Stage 3 receiver を
     `...UnitNormalizedReceiver_of_classGroupPTorsionFree`
     として追跡する形に差し替えた
3. 結論:
   - 棚卸しの結果、
     existing Stage 1 / Stage 2 no-sorry 部品で直接届くのは
     branch theorem 全体ではなく、
     unit-normalized chosen factor receiver の直前までだと整理できた ✅
   - したがって Stage 3 non-first-case の honest open は、
     もはや `hUnit` supply ではなく
     chosen-factor equality から nat witness を回収する一点に集約される ✅
   - build warning 上の direct `sorry` も、
     旧 peel core
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     と、
     新 deepest Stage 3 receiver
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     の 2 箇所になった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     の仮定列を、
     first-case で既に no-sorry 化された
     `NormEqGN` / `UnitAbsorb` 型の分解に寄せられるかを再棚卸しする
   - 特に
     `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
     と
     `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
     だけで返せる中間 target をもう 1 段切り出せないかを調べる

## 2026/04/09 19:14:56 JST

1. 背景:
   - 次の試行として、
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     の仮定列を
     first-case 既存の
     `NormEqGN` / `UnitAbsorb`
     型へ寄せられるかを棚卸しした
   - 目的は、
     `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
     と
     `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
     だけで no-sorry に閉じる部分を theorem 境界として切り出し、
     deepest open をさらに pure arithmetic receiver へ押し下げること
2. 実施:
   - non-first-case receiver 向けに
     `CyclotomicNormEqGNUnitNormalizedChosenFactorTarget`
     `CyclotomicNormUnitAbsorbUnitNormalizedChosenFactorTarget`
     `CyclotomicNormGNPowerUnitNormalizedChosenFactorTarget`
     を追加した
   - それぞれに対して
     `cyclotomicNormEqGN_concrete_unitNormalizedChosenFactor`
     `cyclotomicNormUnitAbsorb_concrete_unitNormalizedChosenFactor`
     `cyclotomicNormGNPower_concrete_unitNormalizedChosenFactor`
     を no-sorry で実装し、
     unit-normalized chosen factor から
     `∃ s, GN p (z - y) y = s^p`
     までは既存 direct norm / unit 補題だけで閉じることを fixed した
   - あわせて
     `CyclotomicNormDescentNonFirstCaseGNPowerReceiverTarget`
     を追加し、
     current non-first-case Stage 3 open を
     「`GN p (z - y) y = s^p` から final nat-level witness を返す pure arithmetic receiver」
     として分離した
   - そのうえで
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_gnPowerReceiver`
     を no-sorry で追加し、
     旧
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     は thin wrapper に置き換えた
   - direct `sorry` は
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     へ押し下げ、
     監視も
     `RegularPrimeRoute.lean`
     `RegularPrimeRouteSorry.lean`
     で追従させた
3. 結論:
   - 棚卸しの結果、
     `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
     と
     `norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow`
     だけで no-sorry に届くのは
     final witness 直前の
     `∃ s, GN p (z - y) y = s^p`
     までだと整理できた ✅
   - したがって non-first-case Stage 3 の current honest open は、
     もはや chosen-factor equality 全体ではなく
     pure `GN = s^p` receiver 1 本に集約される ✅
   - build warning 上の direct `sorry` も、
     旧 peel core
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     と、
     新 deepest Stage 3 receiver
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     の 2 箇所になった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     からさらに既存 Branch A no-sorry 部品へ接げるかを棚卸しする
   - 特に
     pure `GN = s^p`
     を
     Branch A 既存語彙の
     `GN = p * s^p`
     や named smaller-counterexample route へ変換する追加 arithmetic receiver が要るかを調べる

## 2026/04/10 12:41:44 JST

1. 背景:
   - review-052 の提案どおり、
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     を pure arithmetic lemma として直接潰す方針を試行した
   - 前段の棚卸しで、
     current deepest open は
     `GN p (z - y) y = s^p`
     から final witness を返す receiver 1 本だと整理できていた
2. 実施:
   - `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     で
     `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default`
     を用い、
     仮定の
     `∃ s, GN p (z - y) y = s^p`
     自体が既存 no-sorry body invariant に反することから
     `False.elim`
     で final witness を返す実装に置き換えた
   - これにより
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree`
     以降の
     `hCl + hUnit`
     mainline wrapper 群はまとめて no-sorry 化された
   - 監視も更新し、
     `RegularPrimeRoute.lean`
     では
     `...GNPowerReceiver_of_classGroupPTorsionFree`
     と、
     それにぶら下がる
     `...of_classGroupPTorsionFree_and_unitNormalization`
     系 theorem 群を no-sorry 側へ移した
   - `RegularPrimeRouteSorry.lean`
     では Stage 3 receiver 群を外し、
     current sorry 監視を old peel core mainline だけへ絞った
3. 結論:
   - review-052 で切り出した pure arithmetic receiver
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     は、
     既存 no-sorry body invariant への即時矛盾として直接閉じた ✅
   - その結果、
     `hCl + hUnit ⟹ hNorm`
     mainline は no-sorry になり、
     Stage 3 non-first-case receiver 問題は解消した ✅
   - build warning 上の direct `sorry` も、
     旧 peel core
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     の 1 箇所だけになった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - current direct `sorry`
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     が、
     いま no-sorry 化された global/non-first-case norm route で
     どこまで thin wrapper に置換できるかを棚卸しする
   - 必要なら old peel core 周辺の監視と theorem 配置を整理し、
     current honest open を 1 箇所として完全に揃える

## 2026/04/10 14:40:45 JST

1. 背景:
   - review-053 の第一手として、
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     が、
     いま no-sorry 化された global / non-first-case norm route で
     そのまま thin wrapper に置換できるかを検査した
   - 判定点は、
     `hCl` 単独で old peel core を no-sorry chain へ載せ替えられるか、
     それとも追加で `hUnit` supply が要るか、の一点
2. 実施:
   - 既存 theorem 群を点検し、
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_and_unitNormalization`
     が
     new no-sorry norm route への thin wrapper である一方、
     `hCl ⟹ hUnit`
     を供給する既存 no-sorry theorem はまだ無いことを確認した
   - その inspection 結果を theorem 名で固定するため、
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree_reducesTo_unitNormalization`
     を追加し、
     old peel core 側で本当に不足している追加入力は
     `CyclotomicUnitNormalizationTarget`
     1 本だけだと明示した
   - 監視も更新し、
     `RegularPrimeRoute.lean`
     ではこの inspection-summary theorem を no-sorry 側へ追加し、
     既に no-sorry 化済みの `hCl + hUnit` route 群も no-sorry 側へ整理した
   - `RegularPrimeRouteSorry.lean`
     では current sorry 監視を old peel core mainline にだけ揃えた
3. 結論:
   - inspection の結果、
     old peel core theorem は
     **`hCl` 単独ではまだ thin wrapper に置換できない** と分かった
   - ただし不足しているものは新しい数学ではなく、
     existing no-sorry chain に入るための
     `hUnit : CyclotomicUnitNormalizationTarget`
     の supply 1 本だけだと theorem-level に固定できた ✅
   - したがって current honest open は引き続き
     `cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
     にあるが、
     意味としては
     「old peel core に `hUnit` をどう供給するか」
     にかなり絞られた ✅
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
5. 次の課題:
   - `hCl ⟹ hUnit`
     を existing Stage 1 / Stage 2 no-sorry chain でどこまで supply できるかを再点検する
   - もしまだ直接 supply できないなら、
     old peel core を current honest open として維持しつつ、
     theorem 名と監視を
     「不足は `hUnit` だけ」
     という読みへさらに揃える

## 2026/04/10 16:56:14 JST

1. 背景:
   - `RegularPrimeRoute.lean` の no-sorry 監視に移した Stage 3 receiver 群について、
     verbose build の `#print axioms` 出力で `sorryAx` 混入が検出された
   - そこで、なぜ no-sorry 扱いになっていたのかを再点検し、
     transitive dependency まで含めて root cause を追跡した
2. 実施:
   - `RegularPrimeRoute.lean` の no-sorry / via-sorry 分類を見直し、
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     以降の Stage 3 receiver / wrapper 群を
     no-sorry から via-sorry へ戻した
   - `#print axioms` を個別に実行して依存を確認し、
     `bodyInvariant_of_NoPowOnGN`
     自体は no-sorry だが、
     そこへ渡している
     `triominoCosmicNoPowOnGN_default`
     が `sorryAx` を含むことを確定した
   - したがって、
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     の `sorryAx` は
     `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default`
     経由の transitive 汚染であり、
     「direct `sorry` が消えたので no-sorry」と見なした以前の移動は誤分類だったと整理した
3. 結論:
   - no-sorry へ移した理由は、
     theorem 本体に direct `sorry` が無くなったことを根拠に
     早計に no-sorry 扱いしたためであり、
     transitive axiom dependency の確認が不足していた
   - 実際の root source は
     `TriominoCosmicGapInvariant.lean`
     の
     `triominoCosmicNoPowOnGN_default`
     で、
     そこから Stage 3 receiver 群へ `sorryAx` が伝播していた
   - したがって current honest open の数学的意味は変わらないが、
     監視分類としては via-sorry に戻すのが正しい
4. 検証:
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRouteSorry` 成功
   - `./lean-build.sh -v '/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMathTest/FLT/Kummer/RegularPrimeRoute.lean'`
     を再実行し、
     no-sorry section に `sorryAx` 混入 theorem が残っていないことを確認した
   - `#print axioms DkMath.FLT.bodyInvariant_of_NoPowOnGN`
     は no-sorry
   - `#print axioms DkMath.FLT.triominoCosmicNoPowOnGN_default`
     は `sorryAx` を含む
   - `#print axioms DkMath.FLT.cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     も `sorryAx` を含む
5. 次の課題:
   - `triominoCosmicNoPowOnGN_default`
     自体の `sorryAx` root をさらに掘るか、
     ひとまず current monitoring を正した状態で
     Kummer mainline の open に戻るかを判断する

## 2026/04/13 12:29:03 JST

1. 背景:
   - `review-054.md` に従い、
     Kummer local theorem をさらに刻むのではなく、
     `triominoCosmicNoPowOnGN_default`
     の upstream root を掘って
     **最小の unresolved input がどこか**
     を theorem 境界で固定する方針を選んだ
   - 分岐判断:
     local wrapper 追加より upstream root の切り出しを優先した
   - 理由:
     現在の bottleneck は Kummer local ではなく、
     `triominoWieferichBranchBridge_default`
     から入る research-side valuation placeholder だと
     `#print axioms` で確認できたため
2. 調査:
   - `#print axioms` により、
     `triominoCosmicNoPowOnGN` 自体は clean で、
     `triominoCosmicNoPowOnGN_default`
     の `sorryAx` は
     `triominoWieferichBranchBridge_default`
     に限って入ることを確認した
   - さらに掘ると、
     `triominoWieferichDescent_impl_clean`
     自体は clean で、
     汚染は injected input
     `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_noWieferich_core`
     にあると分かった
   - その root は
     `CosmicPetalBridgeGNNoWieferichResearch.lean`
     の
     `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_one_core`
     さらにその upstream である
     `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
     に到達した
   - そして direct `sorry` source は
     `ZsigmondyCyclotomicResearch.lean`
     の
     `squarefree_implies_padic_val_le_one`
     だと確定した
3. 実装:
   - `CosmicPetalBridgeGNNoWieferichResearch.lean`
     に
     `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
     を追加し、
     current research debt を
     「primitive-prime branch での `padicValNat ≤ 1` 供給」
     1 本へ抽象化した
   - 同ファイルに
     `...padicValNat_diff_le_one_of_target`
     `...padicValNat_GN_le_one_of_target`
     `...noWieferich_core_of_target`
     を追加し、
     `TriominoNoWieferichBridge`
     までは clean glue で閉じると固定した
   - `CosmicPetalBridgeGNDescentBQuarantine.lean`
     に
     `triominoWieferichDescent_impl_of_padicValNatLeOneTarget`
     を追加し、
     public `WieferichDescentB`
     まで clean に復元できるようにした
   - `CosmicPetalBridgeGN.lean`
     に
     `triominoWieferichBranchBridge_of_padicValNatLeOneTarget`
     を追加し、
     branch contract 自体は target さえあれば clean だと明示した
   - `TriominoCosmicGapInvariant.lean`
     に
     `triominoCosmicNoPowOnGN_of_padicValNatLeOneTarget`
     と
     `triominoCosmicBodyInvariant_of_padicValNatLeOneTarget`
     を追加し、
     Kummer から見える no-pow / body route の clean receiver を用意した
4. 結論:
   - `triominoCosmicNoPowOnGN_default`
     の `sorryAx` は
     default injection 全体が本質なのではなく、
     **research-side primitive-prime valuation target 1 本**
     に還元できることが分かった
   - したがって、
     review-054 の狙いどおり
     「真の bottleneck は upstream debt」
     を theorem 名で固定できた
   - 次に genuine no-sorry を回復するには、
     `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
     を honest statement へ差し替えるか、
     それに代わる true target を供給すればよい
5. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch` 成功
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `lean/dk_math/tmp/checkAxioms-review054-new.lean`
     で新設 theorem 群の `#print axioms` を確認し、
     いずれも `sorryAx` を含まないことを確認した
6. 次の課題:
   - `DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one`
     を使わずに済む既存 no-sorry route
     （例: `..._of_squarefree_GN` / no-lift provider）
     が current branch-B 文脈で使えないかを再点検する
   - もし既存 route で置換できないなら、
     research theorem 側の statement repair を主戦略として進める

## 2026/04/13 13:20:38 JST

1. 背景:
   - `review-055.md` に従い、
     current branch-B 文脈で
     `padicValNat_primitive_prime_factor_le_one`
     を使わずに済む既存 no-sorry route があるかを再点検した
   - 特に
     `..._of_squarefree_GN`
     / `TriominoNoLiftGNBridge`
     / `TriominoCosmicNonLiftableGNBridge`
     から、
     直前に切り出した
     `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
     へ戻せるかを確認した
2. 実施:
   - `CosmicPetalBridgeGNNoWieferichResearch.lean`
     に
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge`
     と
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge`
     を追加した
   - これにより、
     existing honest route である
     `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core`
     と
     `TriominoNoLiftGNBridge`
     から、
     research target を no-`so#rry` で直接埋められることを theorem 化した
   - `TriominoCosmicGapInvariant.lean`
     に
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_nonLiftableGNBridge`
     を追加し、
     current branch-B 文脈の
     `TriominoCosmicNonLiftableGNBridge`
     からも target を no-`so#rry` で回収できると固定した
   - したがって、
     current branch-B 文脈では
     `padicValNat_primitive_prime_factor_le_one`
     は **必須ではない**
     と結論できた
   - あわせて、
     `CyclotomicPrincipalization.lean`
     の
     `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable`
     と
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit`
     が
     `hNoLift` を受け取っていながら実際には捨てていたので、
     review の指摘どおり
     `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable`
     を経由する配線へ修正した
3. 結論:
   - review-055 の第一手は成立した
   - 既存 no-sorry route により、
     `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
     は
     `TriominoSquarefreeGNBridge`
     / `TriominoNoLiftGNBridge`
     / `TriominoCosmicNonLiftableGNBridge`
     から埋められる
   - とくに Kummer first-case 側では
     `hNoLift : TriominoCosmicNonLiftableGNBridge`
     を already 持つ route があるため、
     default dirty bridge に戻らず
     existing clean route を使うよう復帰できた
   - 一方で、
     default global route を完全に clean 化する concrete provider は
     まだ見つかっていない
     ので、
     non-default / first-case-specialized 側は救えたが、
     full default root の clean 化は依然として upstream provider / statement repair の課題である
4. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch` 成功
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
   - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
   - `lean/dk_math/tmp/checkAxioms-review055.lean`
     で
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge`
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge`
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_nonLiftableGNBridge`
     `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable`
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit`
     の `#print axioms` を確認し、
     いずれも `sorryAx` を含まないことを確認した
5. 次の課題:
   - non-default / specialized route では既存 no-sorry bridge で置換できると分かったので、
     次は default root 側に concrete provider が既にないかをさらに棚卸しする
   - もしやはり concrete provider が無いなら、
     `ZsigmondyCyclotomicResearch.lean`
     の statement repair を main 戦略として進める

## 2026/04/13 13:48:32 JST

1. 背景:
   - `review-056.md` に従い、
     default root 側に
     `TriominoSquarefreeGNBridgeProvider`
     / `TriominoNoLiftGNBridgeProvider`
     の concrete provider が既に存在しないかを棚卸しした
   - 目的は、
     `triominoCosmicNoPowOnGN_default`
     の dirty root を
     statement repair に入る前に
     既存 provider だけで clean 化できるかを判定すること
2. 調査:
   - repo 全体検索の結果、
     `TriominoSquarefreeGNBridgeProvider`
     と
     `TriominoNoLiftGNBridgeProvider`
     には
     structure 定義と
     `ImplTarget` / adapter theorem 群はあるが、
     concrete value を与える declaration は見つからなかった
   - したがって、
     current codebase にあるのは
     「provider があれば downstream は clean に戻る」
     という wiring までであり、
     provider そのものの本体実装は未着手だと判断した
   - あわせて
     `#print axioms`
     でも
     `triominoWieferichNoWieferichBridge_default`
     `triominoNoWieferichBridge_default`
     `triominoCosmicNoPowOnGN_default`
     が依然 `sorryAx` を含むことを再確認した
3. 実装:
   - `TriominoSquarefreeGNBridgeProviderImpl.lean`
     に
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_provider_impl`
     と
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLift_provider_impl`
     を追加した
   - これにより、
     default root の clean 化に必要な不足入力は
     `TriominoSquarefreeGNBridgeProviderImplTarget`
     もしくは
     `TriominoNoLiftGNBridgeProviderImplTarget`
     まで押し下げられた
   - 一度
     `TriominoCosmicGapInvariant.lean`
     へ provider-impl import を入れて
     no-pow / body invariant まで戻す theorem を試みたが、
     既存の
     `triominoNoWieferichBridge_impl`
     名と環境衝突を起こしたため、
     その import は戻した
   - よって今回は
     provider 側で
     「target へ戻れる」
     ところまでに留め、
     default root 本体の clean 化は
     concrete provider 供給か statement repair に委ねる整理とした
4. 結論:
   - 棚卸しの結果、
     **既存の concrete provider は見つからなかった**
   - ただし、
     もし provider 実装が入れば
     `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget`
     までは既存 no-`so#rry` route で直結できることを
     theorem 名で固定できた
   - したがって、
     default root clean 化の主戦略は
     予定どおり
     `ZsigmondyCyclotomicResearch.lean`
     の statement repair に移すのが妥当である
5. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl` 成功
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - `lean/dk_math/tmp/checkAxioms-review056.lean`
     で
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_provider_impl`
     と
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLift_provider_impl`
     の `#print axioms` を確認し、
     いずれも `sorryAx` を含まないことを確認した
6. 次の課題:
   - `ZsigmondyCyclotomicResearch.lean`
     の
     `squarefree_implies_padic_val_le_one`
     / `padicValNat_primitive_prime_factor_le_one`
     を honest statement へ修正する戦略を具体化する
   - その際、
     既に本体側にある true theorem
     `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
     へ public wrapper をどう寄せるかを先に棚卸しする

## 2026/04/13 14:03:28 JST

1. 背景:
   - `review-056.md` 後の次課題として、
     `ZsigmondyCyclotomicResearch.lean`
     の legacy false API
     `squarefree_implies_padic_val_le_one`
     / `padicValNat_primitive_prime_factor_le_one`
     を、
     既存の true theorem
     `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
     へどう寄せるかを具体化した
   - 分岐判断:
     今この時点で legacy theorem の型を直接差し替えるのではなく、
     **honest public wrapper を先に追加し、
     legacy theorem は互換のため残す**
     方を選んだ
   - 理由:
     `PrimitiveBeam.lean` と `GcdNextResearch.lean` に
     legacy theorem の caller が残っており、
     そこには現時点で
     `Squarefree (GN d (a - b) b)`
     を supply する既存 no-`so#rry` ルートが無いため
2. 実施:
   - `ZsigmondyCyclotomicResearch.lean`
     に
     `PrimitivePrimeFactorPadicValNatLeOneOfSquarefreeGTarget`
     を追加し、
     current honest statement を
     theorem-level target として固定した
   - 同ファイルに
     `primitivePrimeFactorPadicValNatLeOneOfSquarefreeGTarget_of_trueTheorem`
     を追加し、
     `padicValNat_primitive_prime_factor_le_one_of_squarefree_G`
     から public target へ戻れることを no-`so#rry` で示した
   - さらに public replacement として
     `squarefree_implies_padic_val_le_one_honest`
     と
     `padicValNat_primitive_prime_factor_le_one_honest`
     を追加し、
     「将来 caller が寄るべき true API」
     を明示した
   - legacy false placeholder 側の docstring も更新し、
     以後の置換先が
     `..._honest`
     であることを明記した
3. 結論:
   - statement repair の具体化としては、
     **直ちに既存 API を壊すのではなく、
     true theorem に寄る public honest wrapper 群を先に立てる**
     方針が妥当だと確定した
   - これにより、
     次の作業は
     1. caller ごとに `Squarefree (GN ...)` を持てるかを点検し、
        持てる箇所から `..._honest` へ移行する
     2. 持てない caller については、
        必要仮定の切り出し、または statement repair の追加段階を検討する
     の 2 段で進められる
   - したがって、
     `ZsigmondyCyclotomicResearch` の main 戦略は
     **honest wrapper 先行 + caller migration**
     と読むのが適切である
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.ZsigmondyCyclotomicResearch` 成功
   - `lean/dk_math/tmp/checkAxioms-review056c.lean`
     で
     `primitivePrimeFactorPadicValNatLeOneOfSquarefreeGTarget_of_trueTheorem`
     `squarefree_implies_padic_val_le_one_honest`
     `padicValNat_primitive_prime_factor_le_one_honest`
     の `#print axioms` を確認し、
     いずれも `sorryAx` を含まないことを確認した
5. 次の課題:
   - `PrimitiveBeam.lean`
     と
     `GcdNextResearch.lean`
     の legacy caller ごとに、
     `Squarefree (GN ...)` 仮定を持てるかを棚卸しする
   - もし caller 側で `Squarefree (GN ...)` を持てないなら、
     その caller は引き続き research placeholder 依存だと認め、
     statement repair の次段
     （仮定追加・target 分離・lemma 名変更）
     を設計する

## 2026/04/13 14:29:13 JST

1. 背景:
   - `ZsigmondyCyclotomicResearch.lean`
     には
     `..._honest`
     wrapper を立てたが、
     実際に legacy caller が
     `Squarefree (GN ...)`
     を持てるかどうかは
     `PrimitiveBeam.lean`
     と
     `GcdNextResearch.lean`
     ごとに切り分ける必要があった
2. 実施:
   - `PrimitiveBeam.lean`
     に
     `primitive_prime_padic_bound_diff_of_squarefree_GN`
     を追加し、
     primitive-prime valuation caller 自体は
     `Squarefree (GN d (a - b) b)`
     が入れば
     `padicValNat_primitive_prime_factor_le_one_honest`
     へそのまま寄せられることを no-`so#rry` で固定した
   - 同ファイルに
     `primitive_prime_factor_forbids_perfect_pow_diff_of_squarefree_GN`
     と
     `primitive_prime_obstructs_GN_perfect_power_of_squarefree_GN`
     を追加し、
     `PrimitiveBeam` の 2 個の legacy caller は
     「statement repair の次段 = `Squarefree (GN ...)` 仮定追加」
     で移行できることを theorem 名で明示した
   - `GcdNextResearch.lean`
     には
     `primitive_prime_padic_bound_diff_of_squarefree_GN`
     を追加し、
     同ファイル内の primitive-prime caller も
     squarefree-GN route へは寄せられることを fixed した
   - 一方で
     `padicValNat_d3_upper_bound`
     の
     `d = 3` かつ `q ∣ a - b`
     分岐は primitive-prime route ではないため、
     `PadicValNatD3BoundaryReceiverTarget`
     を新設し、
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     へ分解した
   - 既存
     `padicValNat_d3_upper_bound`
     は、
     その boundary receiver に
     legacy
     `squarefree_implies_padic_val_le_one`
     を inject する thin wrapper に置換した
3. 結論:
   - `PrimitiveBeam.lean`
     の legacy caller は
     **current proof context だけでは**
     `Squarefree (GN ...)`
     を持っていないが、
     repair 方向は明快で、
     追加仮定を入れれば honest route に移行できる
   - `GcdNextResearch.lean`
     でも primitive-prime caller は同様に移行可能だが、
     `padicValNat_d3_upper_bound`
     の boundary-divisor branch は
     `Squarefree (GN ...)`
     では埋まらず、
     **別 theorem / target に分離するのが正しい**
     と確定した
   - したがって statement repair の次段は
     1. primitive-prime family:
        `Squarefree (GN ...)`
        仮定を足す rename / overload
     2. boundary-divisor family:
        `PadicValNatD3BoundaryReceiverTarget`
        の concrete theorem 化
     の 2 系統に分けて進めるべきだと判断した
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.PrimitiveBeam` 成功
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功

## 2026/04/13 14:48:08 JST

1. 背景:
   - `review-057` の戦略に従い、
     次の主戦場として
     `PadicValNatD3BoundaryReceiverTarget`
     を既存 no-`so#rry` 部品で concrete 化できるかを再点検した
   - ただしこの target は
     `d = 3` かつ `q ∣ a - b`
     枝に対して
     `padicValNat q (a^3 - b^3) ≤ 1`
     を要求しており、
     その statement 自体が正しいかを先に検査する必要があった
2. 実施:
   - `GcdNextResearch.lean`
     に
     `padicValNat_d3_boundary_counterexample`
     を追加し、
     concrete 反例
     `(a,b,q) = (4,1,3)`
     で
     `padicValNat 3 (4^3 - 1^3) = 2`
     すなわち
     `¬ (padicValNat 3 (4^3 - 1^3) ≤ 1)`
     を no-`so#rry` で固定した
   - その上で
     `padicValNatD3BoundaryReceiverTarget_is_false`
     を追加し、
     current boundary receiver target は
     **証明未完ではなく statement が偽**
     であることを theorem 名で明示した
   - 同時に、
     boundary family で本当に言える clean statement として
     `PadicValNatD3BoundarySharedPrimeTarget`
     を追加し、
     `padicValNatD3BoundarySharedPrimeTarget_of_gcdBoundaryGNThree`
     で
     「`q ∣ a-b` かつ `q ∣ S0(a,b)` なら `q = 3`」
     を
     `gcd_boundary_GN_three_dvd_three`
     から no-`so#rry` で回収した
3. 結論:
   - `review-057`
     が主戦場として指していた boundary-divisor family について、
     まず
     `PadicValNatD3BoundaryReceiverTarget`
     を直接埋める路線は成立しない、
     と確定した
   - ゆえに次段の repair は
     「boundary branch の valuation 上界を無理に証明する」
     ではなく、
     **共有素因子分類 (`q = 3`) や boundary-special theorem へ
     target を置き換える**
     方向で進めるべきである
   - これにより
     primitive-prime family は引き続き
     `Squarefree (GN ...)`
     追加で移行、
     boundary-divisor family は
     `PadicValNatD3BoundarySharedPrimeTarget`
     を起点にした別 theorem 群へ整理、
     という二戦線分離がさらに確定した
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功

## 2026/04/13 16:29:43 JST

1. 背景:
   - `review-058` に従い、
     false と確定した
     `PadicValNatD3BoundaryReceiverTarget`
     を救命するのではなく、
     boundary-divisor family を
     exact valuation API へ置き換える段に進んだ
   - 狙いは
     `q ≠ 3` 枝と `q = 3` 枝を分離し、
     「上界化」ではなく「分類化」で読むことだった
2. 実施:
   - `GcdNextResearch.lean`
     に
     `PadicValNatD3BoundaryNeThreeTarget`
     と
     `PadicValNatD3BoundaryThreeTarget`
     を追加し、
     boundary family の後継 API を
     exact valuation statement として切り直した
   - 同ファイルに
     `three_dvd_S0_of_three_dvd_sub`
     を追加し、
     `3 ∣ a - b`
     なら
     `3 ∣ S0(a,b)`
     を no-`so#rry` で回収した
   - その上で
     `padicValNat_d3_boundary_eq_boundary_of_ne_three`
     を追加し、
     `q ≠ 3`
     かつ
     `q ∣ a - b`
     なら
     `padicValNat q (a^3 - b^3) = padicValNat q (a - b)`
     を
     `prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three`
     と因数分解から no-`so#rry` で示した
   - さらに
     `padicValNat_d3_boundary_eq_boundary_succ_of_three`
     を追加し、
     `3 ∣ a - b`
     なら
     `padicValNat 3 (a^3 - b^3) = padicValNat 3 (a - b) + 1`
     を、
     `three_sq_not_dvd_S0_of_coprime`
     と上の `3 ∣ S0`
     補題から no-`so#rry` で示した
3. 結論:
   - boundary-divisor family の次段は、
     もはや
     `≤ 1`
     receiver を探すことではなく、
     **exact valuation classification**
     を canonical API として採用することだと確定した
   - これで
     `review-058`
     の提案どおり、
     `q ≠ 3`
     枝と
     `q = 3`
     枝を別 theorem として扱う地盤ができた
   - 次は
     `padicValNat_d3_upper_bound`
     など boundary caller 側が本当に必要としている仕事を、
     これら 2 本の exact theorem と
     primitive-prime route に分配して migration する段である
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
   - `lean/dk_math/tmp/check_axioms_review058.lean`
     で
     `padicValNat_d3_boundary_eq_boundary_of_ne_three`
     と
     `padicValNat_d3_boundary_eq_boundary_succ_of_three`
     の `#print axioms` を確認し、
     いずれも `sorryAx` を含まないことを確認した

## 2026/04/13 17:45:37 JST

1. 背景:
   - `review-059`
     の方針に従い、
     `d = 3`
     については
     false な一様上界
     `padicValNat q (a^3 - b^3) ≤ 1`
     を canonical API に置かず、
     caller を
     primitive route /
     boundary-ne-three route /
     boundary-three route
     へ分配する段に入った
   - 直前まで
     `padicValNat_d3_upper_bound`
     がその旧インターフェースを残していたため、
     新しい exact valuation theorem 群を使う正規入口を
     theorem 名で固定する必要があった
2. 実施:
   - `GcdNextResearch.lean`
     に
     `padicValNat_d3_canonical_case_split`
     を追加し、
     `q ∣ a^3 - b^3`
     を入口にして
     `¬ q ∣ a - b`
     /
     `q ∣ a - b ∧ q ≠ 3`
     /
     `q = 3 ∧ 3 ∣ a - b`
     の三分岐を theorem として固定した
   - 同ファイルに
     `padicValNat_d3_layer_b_case_split`
     を追加し、
     GcdAg / PetalDetect の前処理を受けた layer-B 文脈でも
     同じ canonical split を使えるようにした
   - さらに
     `padicValNat_upper_bound_layer_b_stub`
     と
     `padicValNat_upper_bound_integrated`
     に
     `d ≠ 3`
     を追加し、
     `d = 3`
     ケースを false な global upper bound ルートから切り離した
   - そのうえで
     `padicValNat_d3_upper_bound`
     の docstring を更新し、
     新規 caller は
     `padicValNat_d3_canonical_case_split`
     /
     `padicValNat_d3_layer_b_case_split`
     を使うべき legacy wrapper であることを明示した
3. 結論:
   - `d = 3`
     valuation story について、
     **canonical API はもはや `≤ 1` ではなく三分岐分類**
     だとファイル構造の上でも確定した
   - これにより
     `padicValNat_upper_bound_layer_b_stub`
     系は
     `d > 3`
     研究スタブとして意味が明確になり、
     `d = 3`
     を混ぜたまま偽命題を主経路に残す状態を避けられた
   - 次は
     実際の caller 側で
     `d = 3`
     の必要仕事が
     「primitive valuation 上界」
     なのか
     「boundary exact valuation」
     なのかを見て、
     この canonical split へ順次 migration する段である
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功

## 2026/04/13 17:49:50 JST

1. 背景:
   - 直前の整理で
     `padicValNat_d3_upper_bound`
     は legacy wrapper と位置づけ直されたが、
     新規 caller が使うべき replacement としては
     boundary 側の exact theorem 群しか前に出ておらず、
     primitive 側の着地点が theorem 名としてまだ薄かった
   - `review-059`
     の migration 方針に沿うなら、
     `d = 3`
     の primitive route
     `q ∣ a^3 - b^3 ∧ ¬ q ∣ a - b`
     に対する honest upper bound を
     直接呼べる形で立てておくのが筋だった
2. 実施:
   - `GcdNextResearch.lean`
     に
     `padicValNat_d3_primitive_upper_bound`
     を追加し、
     `q ∣ a^3 - b^3`
     かつ
     `¬ q ∣ a - b`
     の primitive branch で
     `padicValNat q (a^3 - b^3) ≤ 1`
     を no-`so#rry` で直接返す補題を固定した
   - 証明は
     `padicValNat_le_one_of_prime_divisor_case_three_strong`
     と
     `padicValNat_a2_ab_b2_upper_bound_stage1`
     を束ねるだけの薄い wrapper に留め、
     `b = 0`
     の退避枝も
     `q ∣ 1`
     から `q = 1`
     を導いて `Nat.Prime q` と矛盾させる形で閉じた
   - そのうえで
     `padicValNat_d3_upper_bound`
     の docstring を更新し、
     新規 caller 向けの recommended replacement 一覧に
     `padicValNat_d3_primitive_upper_bound`
     を追加した
3. 結論:
   - `d = 3`
     の caller migration 先は、
     これで
     primitive route には
     `padicValNat_d3_primitive_upper_bound`
     、
     boundary route には
     `padicValNat_d3_canonical_case_split`
     /
     `padicValNat_d3_layer_b_case_split`
     /
     exact valuation theorem 群、
     という形で見通しよく揃った
   - これにより
     `padicValNat_d3_upper_bound`
     を温存する理由は
     さらに
     compatibility だけ
     に縮み、
     今後は実 caller をこの分配先へ順次寄せるだけの状態に近づいた
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功

## 2026/04/13 22:19:47 JST

1. 背景:
   - `padicValNat_d3_upper_bound`
     の外部 caller はすでに消えており、
     repo 内検索では実コード上の呼び出し先が残っていなかった
   - そこで
     `review-059`
     の「最初の caller を 1 本だけ移植」
     は、
     まず
     `GcdNextResearch.lean`
     内の legacy helper が抱えていた primitive branch の重複証明を
     新 API に差し替える形で着手することにした
2. 実施:
   - `padicValNat_d3_primitive_upper_bound`
     の定義位置を
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     より前へ移し、
     内部 caller から参照できるようにした
   - その上で
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     の
     `q ∤ a - b`
     枝にあった
     `padicValNat_le_one_of_prime_divisor_case_three_strong`
     と
     `padicValNat_a2_ab_b2_upper_bound_stage1`
     の直書きを削り、
     `padicValNat_d3_primitive_upper_bound`
     を呼ぶ形へ差し替えた
   - これにより、
     旧 `padicValNat_d3_upper_bound`
     family の内部でも
     primitive route の仕事は
     新 API 側へ一本化された
3. 結論:
   - 外部 caller はまだ無いが、
     最初の migration 例として
     **legacy helper 内の primitive branch を新 API 呼び出しへ置換**
     できた
   - 以後、
     `padicValNat_d3_upper_bound`
     周辺の残務は
     boundary receiver 注入だけにさらに縮退し、
     primitive 側のロジックは
     `padicValNat_d3_primitive_upper_bound`
     へ集約された
   - 次に外部 caller が現れる場合も、
     primitive branch については
     すでに migration 先が実使用付きで固定された状態になった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功

## 2026/04/13 22:22:43 JST

1. 背景:
   - `padicValNat_d3_upper_bound`
     はすでに
     docstring 上では legacy wrapper と明示され、
     primitive route / canonical split / layer-B split への移行先も揃っていた
   - ただし theorem 自体には
     Lean の deprecation 属性が付いておらず、
     将来の caller が警告なしに旧 API を掴める状態だった
2. 実施:
   - `GcdNextResearch.lean`
     の
     `padicValNat_d3_upper_bound`
     に
     `@[deprecated padicValNat_d3_canonical_case_split (since := "2026-04-13")]`
     を追加した
   - 置換先名は
     `d = 3`
     valuation story の正規入口として固定済みの
     `padicValNat_d3_canonical_case_split`
     を採用し、
     詳細な分配先
     `padicValNat_d3_primitive_upper_bound`
     /
     `padicValNat_d3_layer_b_case_split`
     は引き続き docstring に残した
3. 結論:
   - これで
     `padicValNat_d3_upper_bound`
     は
     **説明上だけでなく Lean 上も deprecated 相当**
     の扱いになった
   - 新規 caller は warning によって
     canonical split への移行を促され、
     旧 theorem は compatibility のためだけに残る状態がより明確になった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
