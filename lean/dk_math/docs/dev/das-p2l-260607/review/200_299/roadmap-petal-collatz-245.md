# Roadmap: No.245 cp

## DkMath Collatz / PressureBeam ロードマップ

## 現在地

いま立っている Core はこれ。

```text id="zn9yha"
SourcePressureBeamSeed L
  -> ∃ W, SourcePressureBeamCenteredLocalPulseBox n k r L W
```

この box は、`W` について sign transition、height box、jump box を束ねたもの。cp238 で追加済み。

その後、cp239 で box から sign/target 部分を取り出す projection が入り、cp240 で明示的 list adjacency を包む `SourcePressureBeamNeighborCandidate L W W'` が入った。

つまり現在の土台は、

```text id="bzhy6d"
local pulse box W
+
explicit neighbor candidate W W'
```

ここまで。

---

## Phase 1: Neighbor を診断可能にする

目的：

```text id="c7x52o"
NeighborCandidate L W W'
  -> W' ∈ L
  -> centered diagnostic for W'
```

追加候補：

```lean id="bdp6b2"
sourcePressureBeamNeighborCandidate_left_mem
sourcePressureBeamNeighborCandidate_right_mem
sourcePressureBeamNeighborCandidate_right_center_full_diagnostic
```

ここで `W'` が list 内 witness であることを取り、既存の

```lean id="wxtlmy"
sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
```

へ接続する。

ここは次 checkpoint の本命。

---

## Phase 2: Neighbor の向きを取り出す

`NeighborCandidate` は対称 `Or` なので、次は向きを明示化する。

目的：

```text id="qidm5d"
NeighborCandidate L W W'
  -> AdjacentPairInList L W W'
     or AdjacentPairInList L W' W
```

これは定義そのものだが、caller が使いやすい surface を作る。

候補：

```lean id="zt9j3o"
sourcePressureBeamNeighborCandidate_cases
```

または constructor / eliminator。

```lean id="yja8v6"
sourcePressureBeamNeighborCandidate_of_left
sourcePressureBeamNeighborCandidate_of_right
```

この段階で、`W` と `W'` の順序を持った pair として扱えるようになる。

---

## Phase 3: AdjacentPair diagnostic へ接続

目的：

```text id="xwbrx2"
NeighborCandidate L W W'
  + oriented adjacent pair
  -> adjacent-pair diagnostic
```

ここで既存の list/pair machinery に入る。

対象：

```text id="rtg31j"
SourcePressureLocalIslandWitnessAdjacentDiagnosis
SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
SourcePressureFailureResolution
```

候補 theorem：

```lean id="g1ehru"
sourcePressureBeamNeighborCandidate_adjacent_diagnostic_left
sourcePressureBeamNeighborCandidate_adjacent_diagnostic_right
```

ここで `W` と `W'` の関係が、

```text id="zqbadl"
recovered
overlap obstruction
failure resolution
```

のどれへ落ちるかを見に行く。

---

## Phase 4: PulseTransportResolution を定義

ここで初めて transport 用の名前を与える。

候補：

```lean id="sx9n79"
inductive SourcePressureBeamPulseTransportResolution
```

または軽く `def ... : Prop`。

中身の方向：

```text id="j13xk2"
local pulse box W
+
neighbor candidate W W'
+
adjacent diagnosis
->
transport recovered
or overlap obstruction
```

ここでは「伝播できる」と言い切るより、Lean が返す分岐をそのまま型にする。

```text id="lq8agk"
Recovered branch
Overlap branch
Blocked branch
```

この3分岐で十分。

---

## Phase 5: Box を隣へ移せる条件を探す

目的：

```text id="k8f7i2"
W が local pulse box
W' が neighbor diagnostic を持つ
条件 H がある
->
W' も local pulse / partial box を持つ
```

まずは full box を狙わない。
小さい順に攻める。

1. `W'` の centered diagnostic
2. `W'` の sign pattern
3. `W'` の height bounds
4. `W'` の jump bounds
5. `W'` の local pulse box

候補 theorem：

```lean id="imlws5"
sourcePressureBeamNeighborCandidate_right_center_margin_signs
sourcePressureBeamNeighborCandidate_right_local_box_of_conditions
```

---

## Phase 6: Pulse chain の有限列化

隣への transport 条件が見えたら、次は chain。

対象：

```text id="zhv19u"
List of witnesses
Adjacent chain
Pulse boxes along chain
Obstruction point
```

ここで初めて、

```text id="dhqrkh"
chain continues
or obstruction appears
```

を theorem 化する。

候補：

```lean id="mkvv0b"
SourcePressureBeamPulseChain
SourcePressureBeamPulseChainResolution
```

---

## Phase 7: Big estimate へ戻す

chain ができたら、height / jump bound を合算する。

既存の箱：

```text id="mmgprt"
margin height: [-k, 2k]
net jump: [-3k, 3k]
```

ここから、

```text id="xvv7pf"
chain length m
->
total variation bound
->
local Big estimate
```

を作る。

候補：

```lean id="tsgbpx"
sourcePressureBeamPulseChain_totalVariation_le
sourcePressureBeamPulseChain_localBig_bound
```

---

## Phase 8: Frontier / Automaton へ接続

最後に、local pulse chain を既存の上位層へ返す。

対象：

```text id="yvc2br"
PressureFrontier
PressureAutomaton
PressureDiagnosticDecomposition
PressureFailureResolution
```

ここで、

```text id="5egic4"
local pulse
neighbor
chain
failure resolution
frontier
```

が一本になる。

---

## 直近 3 手

まずはここだけでよい。

```text id="lavin0"
cp241:
  NeighborCandidate -> W' membership -> W' centered diagnostic

cp242:
  NeighborCandidate -> oriented adjacent-pair case split

cp243:
  NeighborCandidate + adjacent diagnosis -> transport resolution skeleton
```

これで Beam の入口ができる。

## 次の Codex 指示・短縮版

```text id="teru8c"
Goal:
  Connect SourcePressureBeamNeighborCandidate to membership and centered
  diagnostics for W'.

Add:
  sourcePressureBeamNeighborCandidate_left_mem
  sourcePressureBeamNeighborCandidate_right_mem
  sourcePressureBeamNeighborCandidate_right_center_full_diagnostic

Use:
  SourcePressureBeamNeighborCandidate definition
  adjacent-pair membership lemmas
  sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center

Do:
  Split hneigh : AdjacentPairInList L W W' ∨ AdjacentPairInList L W' W.
  In both branches, extract W' ∈ L.
  Feed W' membership into centered diagnostic theorem.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## まとめ

今のロードマップは一言で言うとこれ。

```text id="mf5xxu"
local pulse box
  -> neighbor diagnostic
  -> adjacent resolution
  -> transport skeleton
  -> pulse chain
  -> local Big estimate
```

次は `W'` を診断可能にする。
そこから、隣接 pair の分岐へ攻め込む。
