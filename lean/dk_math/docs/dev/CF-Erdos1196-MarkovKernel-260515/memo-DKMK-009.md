# preview

現状を見る限り、DKMK-009 は「`CapacityKernel` を新規に作る」段階ではありません。
すでに `DkMath.Kernel.Capacity / Normalize / SubProbability`、さらに `LogCapacityKernel` と `GlobalLogCapacityKernel` があります。
なので DKMK-009 は、既存 kernel API を **primitive hitting route の正式な本線として整理・接続する章** にするのがよいです。

**DKMK-009 実装計画**

1. **DKMK-009A: 現状 inventory / scope 固定**
   - `summary-DKMK-008.md`, `evaluation-DKMK-008.md`, `review-045.md` を受けて `roadmap-DKMK-009.md` を作る。
   - 目的を明確化:
     `capacity kernel → normalized sub-probability → SubMarkovShadow → weightedHitMass bound`
   - 非目的:
     tail / truncation / `1 + O(1/log x)` は DKMK-010 以降。

2. **DKMK-009B: generic capacity-kernel hitting bridge**
   - 既存の `SubMarkovShadow.ofCapacityKernel` と `ShadowHittingBridge` を使い、任意の `CapacityKernel σ ι` から primitive hitting bound へ行く薄い theorem-facing wrapper を追加。
   - 候補ファイル:
     `DkMath/NumberTheory/PrimitiveSet/CapacityKernelHittingBridge.lean`
   - 形:

     ```text
     CapacityKernel
       + positive capacity
       + SourceControlledChainFamily
       + index compatibility
       + source mass bound
     → weightedHitMass ≤ C
     ```

3. **DKMK-009C: global log-capacity kernel への特殊化**
   - 009B の generic wrapper を `PrimePowerWitnessProvider.globalLogCapacityKernel` に特殊化。
   - 既存の `globalLogCapacitySubMarkovShadow_*` 系 theorem と重複しすぎる場合は、新 theorem は最小限にして、既存 theorem の「capacity-kernel 由来」であることを docs/API 名で明示する。

4. **DKMK-009D: witness-derived quotient path family との正式接続**
   - DKMK-008L の

     ```text
     prime-power witness
     → quotient path family
     → weightedHitMass bound
     ```

     を、明示的に

     ```text
     globalLogCapacityKernel
     → normalized SubMarkovShadow
     → quotient path family
     → weightedHitMass bound
     ```

     と読める theorem-facing wrapper にする。
   - ここが DKMK-009 の中核。

5. **DKMK-009E: public import / aggregator 更新**
   - 新規ファイルを作るなら `PrimitiveSet.lean` に import 追加。
   - `DkMath.lean` 側まで必要なら最後に確認。
   - 既存 API の互換性は壊さない。

6. **DKMK-009F: docs / report**
   - `report-DKMK-009.md` を作成。
   - `DkMath_Markov_kernel-to-ck.md` に DKMK-009 節を追加。
   - `History.md` は、ユーザー指定どおり最終 build 結果が出てから EOF 追記。

**最初の実装単位としては**、DKMK-009A+B が適切です。
まず計画書を起こし、その後 generic bridge を小さく追加して `lake build DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge` で確認する流れが安全です。

重要な判断点は、新しい抽象を増やすより、既存の `CapacityKernel` / `SubMarkovShadow.ofCapacityKernel` / `ShadowHittingBridge` を DKMK-009 の公式ルートとして束ねることです。
