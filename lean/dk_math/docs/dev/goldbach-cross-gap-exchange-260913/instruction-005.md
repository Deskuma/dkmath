# CGE-005: Window Pascal Overlap / Pair–Triple Lower Bound 実装指示

## 目的

CGE-004 では balanced window 上で

\[
\mathrm{Incidence}_w = \mathrm{Covered}_w + \mathrm{OverlapExcess}_w
\]

および

\[
\mathrm{Survivors}_w + \mathrm{Incidence}_w
= \mathrm{Window}_w + \mathrm{OverlapExcess}_w
\]

が exact に Lean へ固定された。
また residue capacity による incidence 上界 `C` と overlap 下界 `e` を受け取り、

\[
C < \#\mathrm{Window} + e
\]

なら survivor が存在する conditional provider interface まで得た。

今回 CGE-005 では、未供給だった overlap payment `e` に対して、
**Pascal overlap hierarchy の pair layer と triple layer から機械的に得られる下界**を実装する。

狙いは Strong Goldbach を証明することではない。
まず各 seat の obstruction support の大きさを `k` としたとき、

\[
\binom{k}{2} \le (k-1) + \binom{k}{3}
\]

を local arithmetic kernel として固定し、window 全体で

\[
\mathrm{PairOverlap}_w - \mathrm{TripleOverlap}_w
\le \mathrm{OverlapExcess}_w
\]

を得る。

`Nat.sub` による truncation を避けたい場合は、primary theorem を

\[
\mathrm{PairOverlap}_w
\le
\mathrm{OverlapExcess}_w + \mathrm{TripleOverlap}_w
\]

の形にしてよい。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 背景

CGE-004 で arbitrary finite obstruction world `S` に対して

- `goldbachObstructionSupportIn n t S`
- `goldbachWindowLocalOverlapExcess`
- `goldbachWindowOverlapExcess`

が実装済みである。

一つの seat `t` について

\[
k := \#\mathrm{Support}(t)
\]

とすると、first-overlap payment は

\[
E_1(k)=k-1
\]

である。

一方 Pascal hierarchy では

\[
P_2(k)=\binom{k}{2},
\qquad
P_3(k)=\binom{k}{3}
\]

を pair / triple obstruction multiplicity として読む。

`k=3` のとき

\[
E_1=2,
\qquad
P_2=3,
\qquad
P_3=1,
\]

なので pair count だけでは overlap を過大評価するが、

\[
P_2-P_3=2=E_1
\]

となる。

`k=4` では

\[
E_1=3,
\qquad
P_2=6,
\qquad
P_3=4,
\]

なので

\[
P_2-P_3=2\le3=E_1.
\]

したがって pair-minus-triple は first-overlap excess の安全な下界候補になる。

---

## 既存 API の優先確認

repository-first で少なくとも以下を確認すること。

- `DkMath.NumberTheory.Goldbach.BalancedCapacity`
- `DkMath.NumberTheory.Goldbach.BalancedReflection`
- `DkMath.NumberTheory.Goldbach.PairOverlap`
- `DkMath.NumberTheory.Goldbach.Overlap`

特に既存 `PairOverlap.lean` には full-fiber / canonical small-prime world 用の

- `goldbachOffsetPrimePairMultiplicity`
- `goldbachOffsetROverlapMultiplicity`
- `goldbachLocalPairOverlapResidual`
- `goldbachPrimePairOverlapCount`

等がある。

ただし今回 CGE-005 の owner は **balanced window + arbitrary finite world `S`** とする。
既存 theorem がそのまま使えない場合でも、同じ全域 API をコピーせず、
`goldbachObstructionSupportIn n t S` を基礎にした lightweight generic wrapper を作ること。

---

## production owner

候補:

`DkMath/NumberTheory/Goldbach/BalancedPascalOverlap.lean`

`BalancedCapacity.lean` は first-overlap ledger owner のまま保つ。
pair / triple Pascal layer は新 module に分けることを推奨する。

必要なら `DkMath/NumberTheory/Goldbach.lean` facade に import を追加する。

---

## 最小定義

候補名。既存名と衝突する場合は repository-first で調整してよい。

```lean
goldbachWindowLocalPairMultiplicity
goldbachWindowLocalTripleMultiplicity
goldbachWindowPairOverlapCount
goldbachWindowTripleOverlapCount
```

意味は、arbitrary finite world `S` に対し、seat `t` の support size を `k` として

```text
local pair   = choose k 2
local triple = choose k 3
```

window global count は balanced window 上の和とする。

可能なら generic `r`-fold observer を一つ追加してもよい。

```lean
goldbachWindowLocalROverlapMultiplicity n t S r :=
  Nat.choose (goldbachObstructionSupportIn n t S).card r
```

ただし CGE-005 で必要なのは `r=2,3` のみ。
巨大な hierarchy framework は作らない。

---

## CGE-005 必須 theorem 群

### CGE-005-A: local pair/triple arithmetic kernel

support cardinalityを `k` とした pure Nat lemma として、最低限

\[
\binom{k}{2} \le (k-1)+\binom{k}{3}
\]

を証明する。

候補形:

```lean
Nat.choose k 2 ≤ (k - 1) + Nat.choose k 3
```

既存 Mathlib lemma / Pascal recurrence を優先して使う。
小さい `k` の場合分けは可だが、巨大な `omega` brute force にしない。

この lemma を support に適用し、seat-local theorem

```text
localPair ≤ localOverlapExcess + localTriple
```

を得る。

可能なら corollary として

```text
localPair - localTriple ≤ localOverlapExcess
```

も追加してよい。

---

### CGE-005-B: window global pair-minus-triple lower bound

local inequality を balanced window 全体で和し、

\[
\boxed{
\mathrm{PairOverlap}_w
\le
\mathrm{OverlapExcess}_w + \mathrm{TripleOverlap}_w
}
\]

を production theorem にする。

さらに Nat subtraction で安全に出せるなら

\[
\boxed{
\mathrm{PairOverlap}_w-\mathrm{TripleOverlap}_w
\le
\mathrm{OverlapExcess}_w
}
\]

を corollary として追加する。

この theorem は arbitrary finite world `S` で成立する形を優先する。
`S = primeScalesUpTo P` は後段の corollary に限定する。

---

### CGE-005-C: pair–triple supplied provider criterion

CGE-004 の conditional provider theoremへ、

```text
PairOverlap - TripleOverlap ≤ OverlapExcess
```

を overlap lower bound として直接差し込める corollary を作る。

概念形:

\[
C < \#\mathrm{Window} + (P_2-P_3)
\]

かつ

\[
\mathrm{Incidence}\le C
\]

なら window survivor が存在する。

できれば residue-capacity 上界までつないだ theorem も追加する。

つまり

\[
\boxed{
\mathrm{ResidueCapacity}_w
<
\#\mathrm{Window}+P_{2,w}-P_{3,w}
\Longrightarrow
\mathrm{WindowSurvivor.Nonempty}
}
\]

という provider-facing endpoint を作る。

さらに既存 CGE-003 の anchor 条件

\[
w\le n,
\qquad
P<n-w,
\qquad
n+w\le squareBody(P)
\]

まで渡せるなら、条件付き `GoldbachPairAt n` corollary を追加してよい。

重要:

- `P_2-P_3` が必ず正とは主張しない。
- pair-minus-triple criterion が universal に成立するとは主張しない。
- これは supplied finite inequality から survivor を返す interface である。

---

## CGE-005-D: relation to existing full-fiber PairOverlap

簡単に取れるなら、`S = goldbachSmallPrimes n` かつ window が full fiber まで広がる場合に、
新しい pair count が既存 `goldbachPrimePairOverlapCount` / seat-side pair multiplicity sum と一致することを audit または theorem で確認してよい。

ただし今回は必須ではない。
既存 full-fiber `PairOverlap.lean` を rewrite のためだけに大きく変更しないこと。

---

## target-30 audit

CGE-004 と同じ

```text
n = 15
w = 8
S = primeScalesUpTo 5 = {2,3,5}
```

を監査する。

既存 kernel-checked 値:

```text
Window    = 9
Covered   = 6
Incidence = 9
Overlap   = 3
Capacity  = 10
```

今回、新たに以下を計算する。

期待:

```text
PairOverlap   = 3
TripleOverlap = 0
Pair-Triple   = 3
```

従って

```text
Pair-Triple = Overlap = 3
```

となり、CGE-004 の overlap lower bound `e=3` を Pascal pair/triple layer が実際に供給できることを確認する。

その結果

```text
Capacity = 10 < Window + (Pair-Triple) = 9 + 3 = 12
```

から conditional survivor theorem が replay できることを監査する。

---

## local arithmetic firewall audit

少なくとも pure arithmetic で以下を確認する。

### support size 3

```text
choose 3 2 = 3
choose 3 3 = 1
local excess = 2
```

pair-only `3 ≤ 2` は偽だが、

```text
3 ≤ 2 + 1
```

は真。

したがって triple correction が必要であることを明示する。

### support size 4

```text
choose 4 2 = 6
choose 4 3 = 4
local excess = 3
```

pair-minus-triple は `2` で、exact overlap `3` より小さい。
つまり CGE-005 は exact identity ではなく **lower bound** であることを firewall とする。

---

## この段階でやらないこと

1. Strong Goldbach の証明。
2. universal balanced-window survivor existence。
3. `PairOverlap - TripleOverlap` が常に十分大きいという無条件 theorem。
4. CRT を用いた pair overlap の universal lower bound。
5. CRT を用いた triple overlap の universal upper bound。
6. 4-fold 以上を含む完全 Inclusion–Exclusion 展開。
7. Möbius inversion / sieve asymptotics / analytic density。
8. RH / CFBRC / AKS の接続。
9. pair count 単独を overlap excess と誤認すること。
10. `Coprime` を primality として使うこと。
11. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom`。

CGE-005 は **Pascal combinatorics から overlap lower bound を一段だけ供給する**ことに限定する。

---

## 判定基準

実装後 `report-005.md` を作り、以下の Outcome から判定する。

### Outcome A — PASCAL OVERLAP PAYMENT

window-local pair/triple layerから

\[
P_2-P_3\le E
\]

が kernel-checked され、CGE-004 provider に実際の overlap payment として接続できた。
Target-30 で `3-0=3` が exact overlap を再現する。

### Outcome B — VALID BUT TOO WEAK

pair-minus-triple lower bound は正しいが、多くの window で truncated subtraction が 0 になり provider strength がほぼ増えない。
それでも theorem 自体は保持可能。

### Outcome C — COLLAPSE / NO USEFUL NAT FORM

Nat subtraction や combinatorial inequality のため、pair/triple layer が CGE-004 の overlap lower boundとして実用的に接続できない。
この場合は無理に framework を増やさず、report で signed / higher-order formulation の必要性を記録する。

---

## report-005.md に書くこと

- 追加・変更ファイル
- production theorem 一覧
- local `choose k 2 ≤ (k-1)+choose k 3` の exact proof route
- window pair / triple 定義
- global pair-triple lower bound の statement
- CGE-004 provider への接続 theorem
- target-30 の Pair / Triple / Pair-Triple / Overlap 値
- support size 3 / 4 firewall
- focused build / facade build
- `#print axioms`
- 禁止構文 grep
- Outcome A/B/C
- 次段階で必要なものを一文で記す

次段階候補は、

```text
pair overlap の非自明 lower bound と triple overlap の upper bound を
CRT / residue geometry から供給すること
```

である。

---

## CGE-005 完了条件

以下を満たしたら停止する。

- arbitrary finite world `S` に対する window-local pair / triple multiplicity が定義された。
- local theorem `pair ≤ excess + triple` が証明された。
- global theorem `PairOverlap ≤ OverlapExcess + TripleOverlap` が証明された。
- 可能なら `PairOverlap - TripleOverlap ≤ OverlapExcess` corollary がある。
- pair-minus-triple lower bound を CGE-004 survivor provider に接続した。
- target-30 で Pair=3, Triple=0, Pair-Triple=3 を監査した。
- support size 3 / 4 firewall を監査した。
- universal survivor existence を主張していない。
- focused build 成功。
- axiom audit で `sorryAx` / 新規 axiom がない。
- `report-005.md` を残した。
