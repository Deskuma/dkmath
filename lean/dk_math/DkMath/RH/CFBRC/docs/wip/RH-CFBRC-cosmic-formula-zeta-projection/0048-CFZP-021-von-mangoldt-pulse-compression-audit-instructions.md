# CFZP-0048 / CFZP-021

## von Mangoldt pulse compression audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-018: arbitrary-slack prime-threshold reach — Green-A
- CFZP-019: branch-free signed-mass budget — Green-A
- CFZP-020: cutoff-frontier signed-mass increment — Green-A
- CFZP-006U/V/W/Y: prime-power event / branch-free / sign-cell / phase-cell layers
- CS14/CS25: canonical prime-power support and finite von Mangoldt mode-sum identities

CFZP-020 により safe-frequency regime `0 < ε < log 2` では

```text
G_(X+1) = G_X + frontierNegativeDebt(X) - frontierPositiveMass(X)
```

が exact に閉じた。

しかし元の prime-side aggregate はすでに finite von Mangoldt sum

```text
Aggregate(X)
  = 2 * ∑_{n ≤ X} Λ(n) * FiniteModeKernel(n)
```

である。従って cutoff を `X -> X+1` と進めたときの変化は、Finset frontier 全体を経由せず、整数 `X+1` の **一つの von Mangoldt-weighted mode pulse** に圧縮できるはずである。

本段の目的はこの一項 pulse を first-class observable にし、

```text
ledger increment
radial-deficit increment
CFZP-020 signed-mass frontier increment
prime-power branch-free event
```

を同じ pulse に exact に同定することである。

最終的に概念形

```text
G_(X+1) = G_X - Pulse(X+1)
```

を得る。

`Λ(X+1)=0` の時刻では pulse は消え、prime-power 時刻だけ arithmetic event が発火する。これにより global deficit flow を「整数 cutoff ごとの prime-power pulse 列」へ圧縮する。

本段では pulse の eventual positivity、block dominance、phase equidistribution、cofinal budget provider、joint limit、limit exchange、RH は証明しない。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaVonMangoldtPulseCompressionAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaVonMangoldtPulseCompressionAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSignedMassCutoffFrontierIncrementAudit
import Mathlib.Tactic
```

必要なら CS14/CS25 の定義元を直接 import してよいが、transitive import で public theorem が見えているなら増やさない。

---

## 2. Gate A — one-mode von Mangoldt pulse

整数 mode `n` に対して pulse を定義する。

推奨 shape:

```lean
noncomputable def cfzp021VonMangoldtPulse
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

係数の括弧順は既存 `pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum` に合わせてよい。

この定義は signed observable であり、nonnegative と宣言してはならない。

---

## 3. Gate B — aggregate one-step pulse identity

既存 finite mode-sum theorem と `Finset.range_succ` / sum recurrence を使い、

```text
Aggregate(X+1) = Aggregate(X) + Pulse(X+1)
```

を exact に証明する。

目標例:

```lean
theorem cfzp021AggregateRayInteractionEnergy_succ_eq_add_pulse
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W (X + 1) =
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X +
        cfzp021VonMangoldtPulse ε W (X + 1) := by
  ...
```

ここは finite identity のみ。infinite series は使わない。

---

## 4. Gate C — branch-free ledger increment = pulse

safe-frequency regime `0 < ε < log 2` で、006V の

```text
Aggregate = branchFreeTrigLedger
```

を両 cutoff に使い、

```text
ledger(X+1) - ledger(X) = Pulse(X+1)
```

および可能なら additive form

```text
ledger(X+1) = ledger(X) + Pulse(X+1)
```

を証明する。

その後 CFZP-020 と合成して、signed-mass frontier net increment が pulse と一致することを public theorem にする。

必須概念形:

```text
frontierPositiveMass(X) - frontierNegativeDebt(X)
  = Pulse(X+1)
```

これにより CFZP-020 の Finset frontier bookkeeping と CS25 の natural-number mode bookkeeping が同じ observable であることを固定する。

---

## 5. Gate D — radial deficit pulse recurrence

safe-frequency regime で中心 theorem:

```text
G_(X+1) = G_X - Pulse(X+1)
```

を証明する。

推奨 shape:

```lean
theorem cfzp021RadialContactDeficit_succ_eq_sub_pulse
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W (X + 1) =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X -
        cfzp021VonMangoldtPulse ε W (X + 1) := by
  ...
```

CFZP-020 recurrence と Gate C の net frontier identity から閉じてもよいし、`G = baseline - Aggregate` 系 public API から直接閉じてもよい。より短く依存の明確な方を選ぶ。

---

## 6. Gate E — pulse sign = one-step deficit direction

Gate D から purely algebraic に

```text
0 ≤ Pulse(X+1) -> G_(X+1) ≤ G_X
Pulse(X+1) ≤ 0 -> G_X ≤ G_(X+1)
Pulse(X+1) = 0 -> G_(X+1) = G_X
```

を証明する。

ここでは pulse sign provider を作らない。conditional adapter のみ。

CFZP-020 の `all frontier events ...` 仮定より一段圧縮された one-number interface になる。

---

## 7. Gate F — non-prime-power quiescence

`X+1` は正なので、既存 von Mangoldt zero characterization を使って、prime power でない cutoff では pulse が 0 になることを証明する。

repository 既存概念を優先する:

```text
IsPrimePowerLabel
isPrimePow
ArithmeticFunction.vonMangoldt_eq_zero_iff
```

等を確認し、既存 canonical predicate と整合する shape を選ぶ。

目標概念:

```text
not prime-power label (X+1)
  -> Pulse(X+1) = 0
  -> ledger(X+1) = ledger(X)
  -> G_(X+1) = G_X
```

CFZP-020 の empty-frontier constancy と同じ事実であることが簡単に結べるなら adapter theorem を追加する。

新しい prime-power predicate は発明しない。

---

## 8. Gate G — prime-power pulse = existing branch-free event

`X+1 = p^j`, `Nat.Prime p`, `0 < j`, `0 < ε < log 2` のとき、von Mangoldt pulse が既存 one-event branch-free observableそのものになることを証明する。

目標概念:

```text
Pulse(p^j)
  = 2 * log p * FiniteModeKernel(p^j)
  = cfzpPrimePowerBranchFreeTrigEvent ε W p j
```

既存 theorem を優先する:

```text
cfzpPrimePowerClosedPhaseEvent_eq_two_log_mul_modeKernel
cfzpPrimePowerClosedPhaseEvent_eq_branchFreeTrigBoundaryDifference
canonicalPrimePowerShadowCost_eq_log_of_witness
ArithmeticFunction.vonMangoldt ... prime power
```

実際の theorem 名は current API を調べて合わせる。

### firewall

同じ natural number に複数の prime/exponent witness を仮定して event を二重計上してはならない。既存 canonical support / unique prime-power representation API を使うか、von Mangoldt equality から witness 非依存な値として閉じる。

---

## 9. Gate H — CFZP-020 frontier exact-label audit

CFZP-020 の frontier membership から、各 frontier pair の natural label が exact に `X+1` であることを証明する。

概念形:

```text
pk ∈ frontier(X)
  -> primePowerPairLabel pk = X+1
```

理由は

```text
label ≤ X+1
and not label ≤ X
```

である。

既存 `mem_pascalPrimePowerPairSupportUpTo_iff` を用い、support definition の内部を不必要に unfold しない。

さらに既存 `primePowerPairLabel_injOn` がそのまま使える場合は、

```text
frontier(X).card ≤ 1
```

または frontier が `Subsingleton` であることまで閉じる。

これは **可能なら必須に近い推奨 gate**。既存 API と型合わせが不自然なら、exact-label theorem だけは必須、cardinality sharpening は roadmap の次段候補へ残してよい。

frontier nonempty iff prime-power label `(X+1)` まで既存 API だけで短く閉じるなら追加してよい。

---

## 10. Gate I — phase-cell sign -> pulse sign adapters

Gate G と 006Y の既存 phase-cell theorem を合成し、prime-power witness がある時刻では

```text
nonposPhaseCellCoverage
  -> 0 ≤ Pulse(p^j)
  -> next radial deficit ≤ current radial deficit
```

および反対符号側

```text
nonnegPhaseCellCoverage
  -> Pulse(p^j) ≤ 0
  -> current radial deficit ≤ next radial deficit
```

の adapter を作る。

重要: これは **一つの prime-power pulse の conditional sign theorem** であり、eventual sign、density、block dominance、cofinal reach は何も与えない。

---

## 11. Gate J — optional finite block telescope

one-step pulse recurrence が素直に `Finset` induction / Nat interval sum へ持ち上がるなら、`X ≤ Y` に対して finite block identity を追加してよい。

概念形:

```text
G_Y = G_X - sum_{X < n ≤ Y} Pulse(n)
```

または同値な ledger block sum。

この theorem は次段で block compensation を扱う入口になる。

ただし Nat interval indexing の調整で本段が肥大化するなら optional とし、CFZP-022 へ送る。

---

## 12. Gap / firewall

本段の終端には明示的 Gap marker を置く。

例:

```lean
inductive Cfzp021VonMangoldtPulseCompressionGap : Prop
  | noIndependentCofinalNetPositivePulseBlockProvider
```

意味:

```text
one-step pulse identity: CLOSED
non-prime-power quiescence: CLOSED
prime-power pulse/event identification: CLOSED
pulse sign -> one-step deficit direction: CLOSED
phase-cell -> one-pulse sign: CONDITIONAL/CLOSED
cofinal net-positive pulse accumulation: OPEN
signed-mass budget provider: OPEN
```

禁止:

- `Λ n ≥ 0` だけから `Pulse n ≥ 0` を推論しない。kernel/event は signed。
- prime-power の存在だけから pulse sign を推論しない。
- one-step nonincrease から global monotonicityを推論しない。
- infinitely many primes / prime powers だけから baseline reach を推論しない。
- phase-cell sign から magnitude reach を推論しない。
- asymptotic density / equidistribution を仮定しない。
- infinite Euler product / infinite sum rearrangementを導入しない。
- joint `(ε,X)` limit / limit exchange を導入しない。
- zero-side/RH-equivalent statement を prime-side provider に使わない。
- global RH を主張しない。

---

## 13. integration

実装後:

1. `DkMath/RH.lean` に新規 module を公開 import。
2. roadmap に `CFZP-021` 節を追加。
3. 何が CLOSED / GAP かを明記。
4. focused build + `lake build DkMath.RH`。
5. 新規 module に `sorry`, `admit`, `axiom`, `native_decide`, `Complex.arg` を入れない。

---

## 14. Exit condition

CFZP-021 の出口は、CFZP-020 の frontier recurrence が natural-number one-mode pulse に圧縮され、少なくとも次が public API になっていること:

```text
Pulse(n) = 2 * Λ(n) * K(n)

Aggregate(X+1) = Aggregate(X) + Pulse(X+1)

G_(X+1) = G_X - Pulse(X+1)

frontierPositiveMass(X) - frontierNegativeDebt(X)
  = Pulse(X+1)

not prime-power(X+1) -> Pulse(X+1)=0

X+1=p^j -> Pulse(X+1)=existing branch-free prime-power event
```

ここまで閉じたら、次段は cumulative budget を **finite pulse blocks / compensation** に書き直し、arbitrary-slack cofinal reach に必要な最小の block-dominance 条件を切り出す。
