# Codex Start Entry

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

この branch を checkout し、repository 内の次を順に読む。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/README.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-006.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/instruction-006.md
```

現在の実装指示は `instruction-006.md` である。

その指示だけを実行し、current source の実在 API に合わせて現場判断すること。

実装後は次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-007.md
```

対象 module のローカル build まで行い、結果を User へ返して停止する。

GitHub の commit、push、PR 操作、Lean CI 起動・確認は行わない。これらは User が担当する受け渡し工程である。

並行作業 branch:

```text
wip/FLT7-magic-core-260722-WiseWolf
```

この branch は参照・統合・変更対象ではない。`DkMath/FLT/Seven/**` と FLT7 専用 docs を触らず、ABC–GN instruction の境界内だけを実装する。

完了後は次 checkpoint へ自動で進まず、User へ作業結果を返すこと。
