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
