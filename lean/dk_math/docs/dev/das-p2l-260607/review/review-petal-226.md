# Git diff / Report / Review

## ref: DkMath.Collatz.PetalBridge.PressureBeam

gch: 4c31f1c0260f1c0562e0d033675bcd68e0c9b468

PressureBeam.lean          public aggregator
PressureBeam/Core.lean     seed / addressed depth / mass-balance core
PressureBeam/Edge.lean     crossing/falling edge vocabulary
PressureBeam/Pulse.lean    pulse packaging / diagnostic projections

## Report

cp225 完了です。`PressureBeam.lean` を機械的に分割しました。新しい数学的主張は追加していません。

構成はこうです。

```text
PressureBeam.lean          public aggregator
PressureBeam/Core.lean     seed / addressed depth / mass-balance core
PressureBeam/Edge.lean     crossing/falling edge vocabulary
PressureBeam/Pulse.lean    pulse packaging / diagnostic projections
```

公開 theorem 名・定義名は変更していません。`PressureBeam.lean` は `PressureBeam.Pulse` を import する入口にして、依存方向は `Core -> Edge -> Pulse -> aggregator` です。

レポートも追加済みです。

- [PressureBeam.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam.lean)
- [Core.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Core.lean)
- [Edge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Edge.lean)
- [Pulse.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean)
- [report-petal-225.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-225.md)

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureBeam.Core
lake build DkMath.Collatz.PetalBridge.PressureBeam.Edge
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
rg no-sorry/admit over inspected pressure files
git diff --check
```

行数は `PressureBeam.lean 27`, `Core 1437`, `Edge 303`, `Pulse 175` です。既知の unrelated warning として `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告だけ残っています。

## Review

## 結論

**採用** じゃ。
cp225 は、かなり良い mechanical refactor になっている。

今回の分割は、

```text id="2hnf0q"
PressureBeam.lean          public aggregator
PressureBeam/Core.lean     seed / addressed depth / mass-balance core
PressureBeam/Edge.lean     crossing/falling edge vocabulary
PressureBeam/Pulse.lean    pulse packaging / diagnostic projections
```

という構成。公開 theorem 名・定義名は変えず、`PressureBeam.lean` を入口 aggregator にしたうえで、依存方向を `Core -> Edge -> Pulse -> aggregator` に整理している。新しい数学的主張は追加していない、という点も checkpoint の目的に合っている。

## 実ファイル確認

添付された分割後ファイルも確認した。入口ファイルは期待通り薄い aggregator になっている。

```lean id="nbavy8"
import DkMath.Collatz.PetalBridge.PressureBeam.Pulse
```

`Core.lean` は `PressureAutomaton` を import し、`Edge.lean` は `PressureBeam.Core`、`Pulse.lean` は `PressureBeam.Edge` を import している。
つまり、依存は次の向きで綺麗に保たれている。

```text id="qw7j7z"
PressureAutomaton
  <- PressureBeam.Core
  <- PressureBeam.Edge
  <- PressureBeam.Pulse
  <- PressureBeam
```

report にも、下流 diagnostic module を higher Beam module に import させておらず、circular import も入れていないと整理されている。

## 行数

実ファイルの行数も report 通りじゃ。

```text id="kduzuk"
PressureBeam.lean   27
Core.lean         1437
Edge.lean          303
Pulse.lean         175
```

合計 1942 行。
元の `PressureBeam.lean` が 1885 行まで来ていたので、これで今後の追加先を小さく選べるようになった。

## 実装レビュー

これは良い分割じゃ。

`Core` はまだ 1437 行と大きいが、ここは歴史的に積み上がった seed / addressed target / margin / mass-balance の本体なので、まずはこの単位でよい。

`Edge` は、cp221〜cp222 の crossing / falling edge vocabulary を収める場所として自然。

```text id="g7mcs4"
CrossingEdgeTarget
FallingEdgeTarget
edge-local classifier
interval-pulse edge bridge
```

`Pulse` は、cp223〜cp224 の local pulse packaging / diagnostic-facing projection を置く場所として自然。

```text id="hu7ypi"
pulse edge package
witness singleton shape
diagnostic-facing consumer
```

この整理により、次から Codex に投げるときも、

```text id="1m5mvi"
Core を触る作業なのか
Edge を触る作業なのか
Pulse を触る作業なのか
```

を明示できる。これは消費量にもレビュー精度にも効く。

## True Beam / False Beam / Gap

## True Beam

今回の True Beam は「数学」ではなく「構造」じゃ。

```text id="j294v2"
公開 API を保ったまま、依存方向を整理できた
```

これは Core に入れてよい構造的成果。

## False Beam

今回の False Beam は、やっていないことが明確な点じゃ。

```text id="2ytobh"
new theorem content なし
public theorem rename なし
lower module への逆 import なし
coverage / propagation / convergence なし
```

refactor checkpoint として安全。

## Gap

残る Gap は、今後の Core 肥大化。

`Core.lean` が 1437 行なので、ここにさらに大きな algebra section を足すと、次は Core 側の再分割が必要になるかもしれぬ。

候補は将来的に、

```text id="c0l9pr"
PressureBeam.Core.Address
PressureBeam.Core.MassBalance
PressureBeam.Core.Seed
```

のような分割じゃが、今はまだ急がなくてよい。

## 次の checkpoint 方針

次は、分割後の小さい対象を使って数学作業へ戻るのが良い。

現状では `Pulse` が一番自然じゃ。
cp224 で diagnostic-facing consumer projection を置いたので、次はそれを **SourcePressureBeamSeed / failure resolution 側の existential witness と接続できるか**を調査するのがよさそうじゃ。

ただし、下流モジュールを import で汚さない。
上位の `PressureBeam.Pulse` あるいは必要なら新規 `PressureBeam.Diagnostic` 的な層で行う。

## 次の Codex 指示

```text id="bw64kw"
Checkpoint: petal-226

Goal:
  Resume mathematical work after the mechanical split by using the smallest
  appropriate module.

Primary target:
  DkMath/Collatz/PetalBridge/PressureBeam/Pulse.lean

Secondary target, only if needed:
  DkMath/Collatz/PetalBridge/PressureBeam/Core.lean

Context:
  cp225 mechanically split the former monolithic PressureBeam file:

    PressureBeam.Core
      seed / addressed depth / mass-balance core

    PressureBeam.Edge
      crossing/falling edge vocabulary

    PressureBeam.Pulse
      local pulse-shape packaging and diagnostic-facing projections

  The public names were preserved.  No new mathematical claims were added.

Current useful API in Pulse:
  - sourcePressureBeamPulse_edges_of_intervalPulseAddress
  - sourcePressureBeamPulse_massBalance_edges_of_intervalPulseAddress
  - sourcePressureBeamPulse_witness_singleton_shape
  - sourcePressureBeamPulse_witness_singleton_massBalance_edges
  - sourcePressureBeamPulse_diagnostic_massBalance_of_intervalPulseAddress
  - sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance

Main question:
  Can the existing Beam seed / witness-list machinery supply a caller-facing
  local pulse diagnostic for an explicitly contained witness?

  In other words, from:

    W ∈ L

  can we package the useful local diagnostic facts:

    entry:
      left < right

    center/right:
      SourcePressureBeamAddressedDepthTarget L ...

    exit:
      right <= left

  in one small theorem, using the existing Pulse API?

Important:
  This must remain one explicit witness / one explicit list membership.
  Do not claim list coverage, family aggregation, canonical target selection,
  overlap repair, or convergence.

Codex should inspect:
  - PressureBeam/Core.lean for seed/list containment APIs;
  - PressureBeam/Pulse.lean for the current witness singleton package;
  - whether an additional caller-facing theorem reduces proof noise;
  - whether the existing
      sourcePressureBeamPulse_witness_singleton_shape
      sourcePressureBeamPulse_witness_singleton_massBalance_edges
      sourcePressureBeamPulse_witness_singleton_depth_and_exit_massBalance
    are already sufficient.

Possible useful theorem shape, only if it is not redundant:

  theorem sourcePressureBeamPulse_witness_singleton_full_diagnostic
      {n : OddNat} {k r : Nat}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W : SourcePressureLocalIslandWitness n k r}
      (hmem : W ∈ L) :
      SourcePressureBeamMassBalanceLeftInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) <
        SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start - 1) ∧
      SourcePressureBeamAddressedDepthTarget L
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ∧
      SourcePressureBeamMassBalanceRightInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1) ≤
        SourcePressureBeamMassBalanceLeftInt n k r
          ((sourcePressureIntervalPulseAddress_of_localIslandWitness W).start +
            (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len - 1)

But do not force this theorem.
If the existing two projections are clearer, add no Lean code and write a report
explaining that the Pulse API is already sufficient.

Allowed outcomes:
  1. Add one compact caller-facing witness singleton diagnostic theorem in
     `PressureBeam/Pulse.lean`.
  2. Add no theorem and report that existing API is sufficient.
  3. If a better smaller theorem is discovered by workspace inspection, add that
     instead and explain why.

Guardrails:
  Do not add:
    - list/family coverage;
    - aggregation over all witnesses;
    - arbitrary target transport;
    - canonical target selection;
    - overlap repair;
    - propagation;
    - Collatz convergence.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over pressure files
  git diff --check

Report requirements:
  - Explain that this is post-split Pulse-level API work.
  - State whether a new theorem was added or skipped.
  - If added, say which existing Pulse theorems it consumes.
  - If skipped, say why existing API is enough.
  - Confirm no public names from cp225 were changed.
  - Include line counts for touched files.
```

## 一歩先ゆく推論

この分割で、次からは作業単位がかなり明確になった。

```text id="bp3ldy"
Core:
  判定式そのもの

Edge:
  entry / exit の境界語彙

Pulse:
  一つの局所 pulse / witness の包装

将来の上位層:
  diagnostic / automaton との接続
```

今すぐ大域化に飛ぶより、まずは `Pulse` で「一つの witness を見たときに何が言えるか」を caller-friendly にしておくのが安全じゃ。

## 総合判断

cp225 は成功。
数学は進めず、構造を綺麗にした。これは今後の Codex 消費を減らす良い整理じゃ。

次は小さな `Pulse.lean` を対象にして、local witness diagnostic をもう一段だけ使いやすくするか、既存 API で十分かを現場判断させるのがよい。

## Diff

※長いので、必要ならリファクタリング結果は以下で取得する。

```sh
git diff 624fca3d2b0ac5942a2ede8b0081cebdd6558be3 4c31f1c0260f1c0562e0d033675bcd68e0c9b468
```
