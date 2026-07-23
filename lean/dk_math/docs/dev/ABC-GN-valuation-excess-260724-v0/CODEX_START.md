# Codex Start Entry

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

この branch を checkout し、次を順に読む。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/README.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/instruction-001.md
```

現在の実装指示は `instruction-001.md` である。

その指示だけを実行し、current source の実在 API に合わせて現場判断すること。

実装後は次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-001.md
```

変更を commit / push し、GitHub Lean CI を起動する。

並行作業 branch:

```text
wip/FLT7-magic-core-260722-WiseWolf
```

この branch は参照・統合・変更対象ではない。`DkMath/FLT/Seven/**` と FLT7 専用 docs を触らず、ABC–GN instruction の境界内だけを実装する。

完了後は次 checkpoint へ自動で進まず、PR 上で賢狼レビューを待つこと。
