# Codex Start Entry — Workbench Paused

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## Status

```text
ABC-GN-001 ... ABC-GN-009  complete
ABC-GN-010                    paused / not started
active instruction            none
```

`report-007.md` と `FINAL_REPORT.md` の地点で、この workbench は一旦停止している。

現在、Codex が自動的に実装を開始してはならない。新しい `instruction-007.md` または明示的な再開指示が repository に追加され、D. が起動するまで待機すること。

## 再開時の読み順

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/FINAL_REPORT.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/README.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-007.md
lean/dk_math/DkMath/ABC/GNFinalBudgetBridge.lean
```

必要に応じて次も参照する。

```text
lean/dk_math/DkMath/ABC/GNSupportReturn.lean
lean/dk_math/DkMath/ABC/GNValuationExcess.lean
lean/dk_math/DkMath/ABC/GNHighLift.lean
```

## Remaining mathematical cores

```text
1. uniform lifted-radical support growth
2. uniform exceptional valuation excess
3. uniform non-exceptional valuation excess
```

または、三者を同時に制御する support–multiplicity balance theorem を探索する。

## Boundaries

再開指示が発行されるまでは、次を行わない。

```text
new implementation
new checkpoint report
abc_main_axiom modification
FLT7 integration
commit / push / PR / CI operations
```

並行作業 branch:

```text
wip/FLT7-magic-core-260722-WiseWolf
```

この branch は参照・統合・変更対象ではない。`DkMath/FLT/Seven/**` と FLT7 専用 docs を触らない。
