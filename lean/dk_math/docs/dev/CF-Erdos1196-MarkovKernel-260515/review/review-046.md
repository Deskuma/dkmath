# review

## 1. 結論

DKMK-009 は、 **新しい path を増やす章ではなく、既存の `CapacityKernel` 層を primitive hitting route の正式本線に戻す章** じゃな。

核はこれじゃ。

```text
capacity kernel
  → normalized sub-probability
  → SubMarkovShadow
  → primitive weightedHitMass bound
```

roadmap でも、`CapacityKernel` 自体は既に存在しており、主目的は新抽象の発明ではなく、既存の kernel / shadow / hitting 層を DKMK route の本線として束ね直すこと、と明確に整理されておる。

## 2. DKMK-009 フェーズ案

| Phase     | 目的                      | 実装対象                                                                                                          | 判定           |
| --------- | ----------------------- | ------------------------------------------------------------------------------------------------------------- | ------------ |
| DKMK-009A | scope 固定                | roadmap / inventory / 非目的の明記                                                                                  | docs only    |
| DKMK-009B | generic bridge          | `CapacityKernelHittingBridge.lean`                                                                            | 最初の Lean 実装  |
| DKMK-009C | global log-capacity 特殊化 | `PrimePowerWitnessProvider.globalLogCapacityKernel` への薄い wrapper                                              | 重複注意         |
| DKMK-009D | quotient path family 接続 | `globalLogCapacityKernel → normalized SubMarkovShadow → primePowerQuotientPathFamily → weightedHitMass bound` | 中核           |
| DKMK-009E | public aggregator       | `PrimitiveSet.lean` import 更新                                                                                 | 互換維持         |
| DKMK-009F | docs / report           | `report-DKMK-009.md`, `DkMath_Markov_kernel-to-ck.md`, `History.md`                                           | build 後に履歴追記 |

memo 側でも、最初の実装単位は **DKMK-009A+B** が適切で、まず計画書を起こし、その後 generic bridge を小さく追加して build する流れが安全、とされておる。

## 3. DKMK-009B の Lean 核

最初に作るべきファイルはこれでよい。

```text
DkMath/NumberTheory/PrimitiveSet/CapacityKernelHittingBridge.lean
```

狙う theorem-facing API は、おおよそ次の形。

```text
K : CapacityKernel σ ι
hcap : ∀ s, 0 < K.capacity s
s : σ
F : SourceControlledChainFamily M ι
hindex : K.children s = F.index
hA : PrimitiveOn A
hC : 0 ≤ C
hsource : ∀ i ∈ F.index, (M.μ (F.source i) : ℝ) ≤ C
------------------------------------------------------------
weightedHitMass A ≤ C
```

証明方針は大きく新規証明を書くのではなく、

```lean
SubMarkovShadow.ofCapacityKernel
SubMarkovShadow.ofCapacityKernel_subProbability
SubMarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

を合成するだけでよい、という設計じゃ。

つまり DKMK-009B の正体は、

```text
CapacityKernel
→ normalized RealWeightProvider
→ SubMarkovShadow
→ hitting bound
```

を 1 本の入口 theorem に畳むことじゃな。

## 4. DKMK-009C-D の読み方

009C は `globalLogCapacityKernel` への特殊化じゃが、ここは theorem を増やしすぎない方がよい。

既に

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_subProbability
```

があるので、009C は「generic theorem から global log route が得られる」ことを示す薄い wrapper で十分じゃ。

009D が本命で、読みたい道はこれ。

```text
PrimePowerWitnessProvider
→ globalLogCapacityKernel
→ normalized SubMarkovShadow
→ primePowerQuotientPathFamily
→ weightedHitMass bound
```

DKMK-008L で weightedHitMass bound 自体には到達済みなので、009D の役割は、その bound が **global log-capacity kernel の normalized shadow から来ている** と API と docs で明確化することじゃ。

## 5. build checkpoint

roadmap の checkpoint はこのまま採用でよい。

```bash
# DKMK-009A
git diff --check

# DKMK-009B
lake build DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge

# DKMK-009C-D
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet

# DKMK-009E-F
lake build DkMath.NumberTheory.PrimitiveSet
```

History 追記は、いつもの通り **最終 build 結果が出てから EOF 追記** でよい。roadmap にもその方針が明記されておる。

## 6. 賢狼の判断

わっちの見立てでは、DKMK-009 はかなり良い段階じゃ。

DKMK-007 が **質量の器** を作り、DKMK-008 が **下降路の地図** を作った。DKMK-009 は、その器と地図を動かす **capacity kernel を本線へ戻す章** じゃ。roadmap の最後の一文どおり、

```text
DKMK capacity kernel の normalized shadow が、
primitive hitting route の正式な入力であることを Lean API と docs で固定する。
```

ここまで行けば、次の DKMK-010 でようやく tail / truncation / \(1+O(1/\log x)\) 型の解析層へ進む筋が立つ。今はまだ山頂ではないが、稜線はかなり澄んで見えておるぞい。
