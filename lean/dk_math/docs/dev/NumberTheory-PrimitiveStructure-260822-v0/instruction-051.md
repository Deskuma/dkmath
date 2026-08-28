# PRIM-L036 — Parity-Safe Incidence Conservation / Silent-Wave Balance Lean Judgment

日付: 2026-08-26
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 目的

PRIM-L035 で canonical pruning provider は任意 `n` に対して構成可能となり、残る sufficient frontier は

```text
oddActive.card + duplicateDeletion.card < candidate.card
```

の一つの有限 cardinal inequality に圧縮された。

次は新しい provider を作らない。L034/L035 の incidence matrix を prime-wave 側と candidate-support 側から exact に二重計数し、deletion / overlap / uncovered seat の保存式を Lean で固定する。

狙いは、L035 の residual inequality をさらに本質的な有限差へ変形することにある。

一般 graph library、PNT、Jacobsthal bound、解析的 sieve、descent は導入しない。

## 1. 推奨 module

```text
DkMath/NumberTheory/Legendre/ParitySafeIncidenceBalance.lean
```

最小 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeWavePruning
```

facade `DkMath.NumberTheory.Legendre` に import を追加する。

## 2. Candidate / active-support incidence

必要なら次を thin finite definitions として置く。

```text
paritySafeActiveSupport n r
  = squareOffsetAnchorNondivisorSupport n r
```

ただし candidate complete point は odd なので prime `2` は support に存在せず、実質的な support universe は `squareAnchorOddActivePrimes n` であることを theorem で示すこと。

定義名を増やす必要がなければ既存 support を直接使ってよい。

### L036-1 exact incidence transpose

```text
I(n) := Σ q in squareAnchorOddActivePrimes n,
          (paritySafeActiveWaveOffsets n q).card
```

を定義し、同じ量が candidate 側から

```text
Σ r in squareAnchorOddPointCoprimeOffsets n,
  (squareOffsetAnchorNondivisorSupport n r).card
```

として数えられる exact equality を証明する。

これは `Finset.sum_comm` / indicator sums による有限 double counting で閉じること。既存 incidence theorem を無理に一般化しない。

## 3. Nonempty / silent active waves

次を finite definitions として導入する。

```text
paritySafeNonemptyActivePrimes n
paritySafeSilentActivePrimes n
```

意味:

```text
nonempty := active q whose paritySafeActiveWaveOffsets n q is Nonempty
silent   := active \ nonempty
```

証明:

```text
nonempty.card + silent.card = oddActive.card
```

または同等の Nat-safe exact identity。

## 4. Covered / uncovered parity-safe candidates

次を定義する。

```text
paritySafeCoveredCandidates n
paritySafeUncoveredCandidates n
```

`uncovered` は parity-safe candidate で active support が empty な seat。

### L036-2 exact escape semantics

`r ∈ paritySafeUncoveredCandidates n` が、candidate membership と old-prime noncoverage に exact に対応することを証明する。

目標形:

```text
r ∈ paritySafeUncoveredCandidates n
  ↔ r ∈ squareAnchorOddPointCoprimeOffsets n ∧ ¬ SquareOffsetCovered n r
```

`0<n` が必要なら theorem hypothesis に置く。

そこから thin consumer:

```text
(paritySafeUncoveredCandidates n).Nonempty
  -> ∃ p, Nat.Prime p ∧ SquareCell n p
```

を既存 Frontier API だけで接続する。

## 5. Exact local duplicate equality

L035 では private theorem が

```text
extra.card ≤ wave.card - 1
```

までだったが、定義上 equality のはずである。

Lean に直接

```text
(paritySafeActiveWaveExtraOffsets n q).card
  = (paritySafeActiveWaveOffsets n q).card - 1
```

を全 `n,q` で証明させること。

empty wave では両辺 0、nonempty wave では `card_erase_of_mem`。

これを用いて、

```text
paritySafeWaveDuplicateBudget n
  = I(n) - (paritySafeNonemptyActivePrimes n).card
```

または Nat subtraction を避けた exact additive form

```text
nonempty.card + duplicateBudget = I(n)
```

を優先して証明する。

## 6. Candidate-side support excess

candidate support の多重 hit を測る量を定義する。

```text
paritySafeSupportExcess n :=
  Σ r in candidate, (support(r).card - 1)
```

Nat subtraction は各 seat の局所だけに閉じ込める。

### L036-3 candidate-side exact identity

各 candidate の support card は、covered seat では

```text
1 + (support.card - 1)
```

uncovered seat では 0。

従って exact に

```text
covered.card + supportExcess = I(n)
```

を証明する。

さらに

```text
covered.card + uncovered.card = candidate.card
```

も exact に固定する。

## 7. Main conservation identity

prime-wave side と candidate side を合流して、次の Nat-safe exact conservation law を証明する。

```text
nonemptyActive.card
  + duplicateBudget
  + uncoveredCandidates.card
=
candidate.card
  + supportExcess
```

数式では

```text
H + B + U = C + X
```

である。

ここで

- `H`: nonempty active waves
- `B`: additive duplicate budget
- `U`: uncovered candidates
- `C`: all parity-safe candidates
- `X`: support multiplicity excess

これは近似ではなく同じ finite incidence matrix の exact conservation とする。

## 8. Residual criterion の exact compression

active primes は

```text
A = H + S
```

(`S` = silent active waves) と分解される。

上の conservation law から、可能なら次の exact equivalence を Lean で証明する。

```text
oddActive.card + duplicateBudget
    < candidate.card + supportExcess
↔
silentActive.card < uncoveredCandidates.card
```

Nat の算術正規形が煩雑なら、両 exact additive identities と `omega` で閉じる薄い theorem にする。

この theorem は重要である。

L035 の additive duplicate budget に support-overlap credit を戻した corrected criterion が、最終的に

```text
silent active waves < genuinely uncovered candidate seats
```

という単純な finite balance に等価になるかを Lean に裁かせる。

### Consumer

右辺が成立すれば `uncovered.card > 0` なので、L036-2 consumer から square-cell prime を返す。

## 9. Exact candidate cardinal refinement

L034 では odd anchor に対して

```text
totient n ≤ candidate.card
```

までで止めた。

今回の incidence balance に有用なら、odd `n` では canonical packet `(r,n+r)` の complete-point parity が反転するため、各 packet から exactly one candidate が選ばれることを Lean で証明し、

```text
Odd n -> candidate.card = Nat.totient n
```

まで閉じてよい。

これは optional ではなく、証明が薄く閉じるなら public theorem として固定する。even anchor の `2 * totient` theorem は既存 L034 を再利用する。

## 10. Stronger-beam Lean judgment

core build 後、次を concrete theorem attempt として判定する。

1. `silentActive.card < uncovered.card` を既存 L034 packet injection だけから一般に証明できるか。
2. 無理なら、naive map が失敗することを Lean の concrete false beam で固定する。

推奨 false beam:

```text
n = 12
q = 11
```

- `11` は parity-safe odd active prime。
- `paritySafeActiveWaveOffsets 12 11` が empty、すなわち silent wave であることを確認する。
- L034 の even-anchor active-prime seat `r=q=11` は parity-safe candidate だが、

```text
12^2 + 11 = 155 = 5 * 31
```

なので active old prime `5` に cover され、uncovered seat ではない。

従って単純な map `q ↦ q` は silent -> uncovered injection にはならない。

この false beam が通れば、無理に別の ad hoc injection を作らず停止する。

## 11. Outcome

```text
A — EXACT INCIDENCE CONSERVATION / SILENT-ESCAPE FRONTIER COMPRESSION
B — INCIDENCE LEDGER ONLY
C — NO MATERIAL NEW BALANCE
```

A は以下が Lean で全て成立した場合:

- wave-side exact incidence
- candidate-side exact incidence
- main conservation identity
- corrected criterion ↔ silent/uncovered balance の exact equivalence
- uncovered -> Frontier consumer

universal `silent < uncovered` 自体は A の条件に含めない。

## 12. Stop boundary

この checkpoint で LegendreConjecture theorem を追加しない。

以下は禁止:

- PNT / analytic prime density
- Jacobsthal restart
- general graph/matching framework
- probabilistic sieve
- unproved universal injection
- cofactor descent

L036 report:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-incidence-conservation-silent-wave-balance-260826.md
```

validation:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
lake build DkMath.NumberTheory.Legendre
git diff --check
```

通常の trailing-whitespace / forbidden-placeholder audit も実施する。
