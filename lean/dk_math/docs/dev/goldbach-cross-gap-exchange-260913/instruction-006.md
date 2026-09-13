# CGE-006: CRT Pair Witness と Center-Aligned Triple Control 実装指示

## 目的

CGE-005 までで、balanced window 上の first-overlap excess `E` に対して

\[
PairOverlap - TripleOverlap \le E
\]

という Pascal payment が kernel-check された。

したがって次に必要なのは、外から `PairOverlap` / `TripleOverlap` の値を仮定することではなく、
**residue / CRT geometry から pair overlap の下界と triple overlap の上界を供給すること**である。

ただし、いきなり一般の ± residue 8 通りを完全実装して巨大化しない。
CGE-006 では二段階に分ける。

1. 一般有限 prime world に対して、左側 endpoint `n-t` の同時可除性から得られる
   **canonical pair witness** を使い、pair overlap の非自明な下界を作る。
2. triple 側はまず、各 world prime が `2*n` を割るため forbidden residue が 1 class に collapse する
   **center-aligned world** に限定し、canonical CRT residue による exact / upper control を作る。

これは universal Goldbach provider ではない。
`n=15`, `w=8`, `S={2,3,5}` の primorial-like target-30 world を、
CRT provider の最初の非自明な kernel-checked模型として固定することが目的である。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 現在の production endpoint

既存 `BalancedPascalOverlap.lean` には

```text
goldbachWindowPairOverlap_sub_triple_le_overlap
```

があり、概念的に

\[
P_2-P_3\le E
\]

を与える。

さらに

```text
goldbachPairAt_of_goldbachWindow_residue_capacity_of_pairMinusTriple_budget
```

により、anchor-local 条件の下で

\[
Capacity < Window + (P_2-P_3)
\]

なら `GoldbachPairAt n` が得られる。

CGE-006 は、この `P_2` と `P_3` に CRT 由来の arithmetic provider を入れる。

---

# Part A: canonical left-pair witness

## 基本観測

異なる prime `p,q` に対し

\[
t_{p,q}:=n\bmod(pq)
\]

と置けば

\[
pq\mid n-t_{p,q}.
\]

したがって

\[
p\mid n-t_{p,q},\qquad q\mid n-t_{p,q}.
\]

balanced window と anchor 条件によって

\[
p,q\le P<n-w\le n-t_{p,q}
\]

が取れれば、`p,q` は left endpoint の **proper** obstruction になる。

これは ± CRT 全体を使わない、最も単純な同側 overlap provider である。

## A1. canonical witness

候補名:

```lean
goldbachLeftPairWitness (n p q : ℕ) : ℕ := n % (p * q)
```

必要なら product zero の境界を theorem hypothesis で処理する。
prime hypothesis がある場合は自動的に nonzero なので、定義を過剰に defensive にしなくてよい。

最低限、distinct primes `p ≠ q` の下で

```text
p ∣ n - goldbachLeftPairWitness n p q
q ∣ n - goldbachLeftPairWitness n p q
```

を証明する。

`Nat.mod_add_div`, `Nat.mod_lt`, prime coprimality など既存 Mathlib theorem を repository-first で確認すること。

## A2. eligible unordered pair set

window と finite world `S` に対して、canonical witness が実際に window 内に入る prime pair を Finset 化する。

候補概念:

```text
GoldbachWindowEligibleLeftPair n w S (p,q)
```

または Finset:

```text
goldbachWindowEligibleLeftPrimePairs n w S
```

条件は最低限

```text
p ∈ S
q ∈ S
p < q
n % (p*q) ∈ goldbachBalancedOffsets n w
```

とする。

`S` 自体の primality は theorem hypothesis `KnownPrimeScales S` 等で与える。
既存 full-fiber `goldbachPrimePairs` が再利用できるなら、そこから filter すること。
同型の unordered-pair framework を別に大量実装しない。

## A3. eligible pair -> pair obstruction

anchor-local world を主用途とし、少なくとも次の意味を theorem 化する。

仮定:

```text
KnownPrimeScales S
p,q ∈ S
p < q
P あるいは world upper bound により p,q ≤ P
w ≤ n
P < n-w
canonical witness t ∈ goldbachBalancedOffsets n w
```

結論:

```text
p ∈ goldbachObstructionSupportIn n t S
q ∈ goldbachObstructionSupportIn n t S
```

すなわち `t` の local pair multiplicity が少なくとも 1 である。

endpoint equality exception を無視しないこと。
`P < n-w` と `p,q ≤ P` を使って `n-t ≠ p,q` を明示的に閉じる。

## A4. pair-overlap lower bound

window pair overlap が seat-local `choose support.card 2` の和として定義されていることを使い、
eligible unordered pair 一つにつき少なくとも一つ pair incidence が存在することから

\[
\boxed{
\#EligibleLeftPairs\le P_{2,w}
}
\]

を証明する。

必要なら window-local version の pair double-count lemma を一つ追加してよい。
ただし full-fiber `PairOverlap.lean` の巨大コピーは作らない。

候補 theorem:

```lean
goldbachWindowEligibleLeftPrimePairs_card_le_pairOverlap
```

exact theorem 名は既存 API と整合するよう調整可。

---

# Part B: center-aligned world

## B1. predicate

有限 world `S` の全 prime direction が target center に整列していることを表す軽量 predicate を置く。

候補:

```lean
def GoldbachCenterAlignedWorld (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ r ∈ S, r ∣ 2*n
```

このとき既存

```text
goldbach_residue_eq_neg_iff
goldbach_card_forbidden
```

から、各 `r ∈ S` の forbidden residue は 1 class に collapse する。

この predicate は primorial-like special world の観測用であり、一般 `primeScalesUpTo P` が常に満たすとは主張しない。

## B2. collapsed residue = center residue

`r ∈ S` かつ `r ∣ 2*n` の下で、raw obstruction residue は一意であり、概念的には

\[
t\equiv n\pmod r.
\]

であることを theorem 化する。

可能なら既存 `goldbachForbiddenResidues` をそのまま使い、別の residue encoding を増やさない。

---

# Part C: center-aligned triple geometry

## C1. canonical triple residue

異なる prime `p<q<r` に対して

\[
t_{p,q,r}:=n\bmod(pqr)
\]

を canonical triple residue とする。

候補:

```lean
goldbachTripleWitness n p q r := n % (p*q*r)
```

center-aligned 条件の下では、`p,q,r` の三つ全てに raw obstructed な `t` は

\[
t\equiv n\pmod{pqr}
\]

へ collapse することを証明する。

prime pairwise coprime 性を明示して使うこと。

## C2. triple overlap seats are one arithmetic progression

balanced window 内の triple-overlap seat は

\[
t=t_0+k(pqr),\qquad t_0=n\bmod(pqr)
\]

の形に限られる。

最低限、次の upper bound を得る。

`M := p*q*r`, `t0 := n % M` として

\[
\#TripleSeats(p,q,r)
\le
\begin{cases}
0,& w<t_0,\\
\lfloor (w-t_0)/M\rfloor+1,& t_0\le w.
\end{cases}
\]

Lean 実装が重ければ、まず安全な

\[
\#TripleSeats(p,q,r)
\le
\begin{cases}
0,& w<t_0,\\
w/M+1,& t_0\le w
\end{cases}
\]

でもよい。

ただし target-30 で `0` を検出できる theorem shape を必ず残す。
単なる常時 `≤ w/M+1` だけでは今回の目的を満たさない。

## C3. window unordered prime triples

`S` 内の `p<q<r` を表す Finset を最小限で導入する。
既存 pair framework と同じ思想でよい。

候補:

```lean
goldbachWindowPrimeTriples S
```

ただし window に依存しないなら `goldbachPrimeTriples S` の方がよい。

## C4. global triple upper bound

center-aligned finite prime world の下で、各 unordered triple の upper bound を足し合わせて

\[
P_{3,w}\le T_{CRT}(n,w,S)
\]

を得る。

`T_CRT` は Finset sum として明示的・実行可能であること。

例えば概念的には

```text
∑ (p,q,r) in primeTriples S,
  if n % (p*q*r) ≤ w then w / (p*q*r) + 1 else 0
```

を候補とする。

exact floor `(w-t0)/M+1` が無理なく証明できるならそちらを優先してよい。

---

# Part D: CRT payment provider

Part A と C を CGE-005 に接続する。

定義/略記として

```text
PairLower := card eligibleLeftPairs
TripleUpper := centerAlignedTripleCRTSum
```

を置いてもよい。

証明済み bounds

```text
PairLower ≤ PairOverlap
TripleOverlap ≤ TripleUpper
```

から、Nat subtraction の向きに注意して

\[
PairLower-TripleUpper
\le
PairOverlap-TripleOverlap
\]

を得られる条件を正確に整理する。

`Nat.sub` の単調性だけで不正確な theorem を作らないこと。
必要なら hypothesis `TripleUpper ≤ PairLower` や、`ℤ` 版 budget を導入する。

安全第一で、次のどちらかを実装すればよい。

### Option 1: Nat safe budget

明示的な sufficient hypotheses を置いて

```text
PairLower - TripleUpper ≤ PairOverlap - TripleOverlap
```

を導く。

### Option 2: supplied payment theorem

pair lower / triple upper から直接

```text
PairLower ≤ PairOverlap
TripleOverlap ≤ TripleUpper
C < Window + (PairLower - TripleUpper)
```

を使い、必要な arithmetic side condition を加えて survivor / Goldbach へ閉じる。

最終的に anchor-local special-world theorem として

```text
GoldbachCenterAlignedWorld n (primeScalesUpTo P)
...
CRT budget
-> GoldbachPairAt n
```

が得られればよい。

**これは Strong Goldbach ではない。**
center-aligned hypothesis を theorem 名/docstring から隠さないこと。

---

# target-30 regression

必須監査:

```text
n = 15
w = 8
P = 5
S = primeScalesUpTo 5 = {2,3,5}
```

既存値:

```text
Window        = 9
Capacity      = 10
PairOverlap   = 3
TripleOverlap = 0
```

CGE-006 では arithmetic provider 側から次を再現することを狙う。

## pair witness

canonical left witnesses:

```text
(2,3): 15 % 6  = 3
(2,5): 15 % 10 = 5
(3,5): 15 % 15 = 0
```

全て `≤ 8` なので

```text
EligibleLeftPairs.card = 3
```

を期待する。

## triple witness

```text
15 % (2*3*5) = 15 > 8
```

かつ `{2,3,5}` は center-aligned (`2,3,5 ∣ 30`) なので

```text
TripleCRTUpper = 0
```

を期待する。

したがって

```text
PairLower - TripleUpper = 3
```

となり、既存 budget

```text
10 < 9 + 3
```

を **外部 overlap 値を直接仮定せず** CRT provider から replay できることが理想。

もし最終 Goldbach replay まで Lean engineering が膨らむ場合でも、
`PairLower=3`, `TripleUpper=0`, それぞれの正しい bound theorem までを必須到達点とする。

---

# arithmetic firewalls

最低限、次を audit する。

1. `n % (p*q)` が window 外なら、その pair を lower bound に数えない。
2. canonical left witness は pair overlap の**一部**しか拾わない。
   `PairLower = PairOverlap` と一般には主張しない。
3. center-aligned 条件が無ければ triple forbidden residues は最大 8 orientation class になり得る。
   `t ≡ n mod pqr` 一本に collapse すると主張しない。
4. `p=q` や `q=r` を triple CRT に混ぜない。必ず strict order / distinct primes。
5. raw obstruction と proper obstruction の endpoint exception を anchor 条件で閉じる。
6. `Nat.Coprime` だけで prime を主張しない。

---

# 非目標

CGE-006 では以下を行わない。

1. general signed CRT (`±n` の全 4 / 8 class) の完全一般化。
2. universal `PairLower` / `TripleUpper` inequality の証明。
3. universal survivor existence。
4. Strong Goldbach。
5. RH / CFBRC / analytic density。
6. AKS。
7. 新しい primality criterion。
8. 大規模 generic inclusion-exclusion framework。
9. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom`。

まず center-aligned special world と canonical left-pair witness で、CRT provider が実際に Pascal payment を供給できるかを見る。

---

# 推奨 production owner

候補:

`DkMath/NumberTheory/Goldbach/BalancedCRTOverlap.lean`

import は必要最小限とし、少なくとも

- `BalancedPascalOverlap`
- `PrimeWorld`

を確認する。

必要に応じて facade `DkMath/NumberTheory/Goldbach.lean` に追加。

---

# report-006.md

実装後、同じ docs directory に `report-006.md` を作り、以下を記す。

- 追加/変更ファイル
- canonical pair witness theorem
- eligible pair set と pair lower bound
- `GoldbachCenterAlignedWorld` の exact definition
- triple canonical residue / progression theorem
- triple CRT upper bound
- target-30 の PairLower / TripleUpper 数値
- CGE-005 budget への接続可否
- focused build / facade build
- `#print axioms`
- 禁止構文 grep / `git diff --check`
- Outcome

Outcome は次の分類を使う。

## Outcome A — CRT OVERLAP PAYMENT PROVIDER

CRT geometry から pair lower と triple upper が production theorem として得られ、
少なくとも target-30 で Pascal payment を外部 overlap 値なしに再生できた。

## Outcome B — PAIR WITNESS ONLY

canonical pair lower bound は得られたが、triple CRT control が production theorem として閉じない。
この場合、pair 側だけ保持し、triple は report に engineering gap を明記する。

## Outcome C — CENTER-ALIGNED SPECIALIZATION TOO WEAK

special-world theorem は成立するが payment provider として新しい情報をほぼ供給せず、
target-30 replay にもつながらない。

Outcome を無理に A にしないこと。

---

# CGE-006 完了条件

最低限以下を満たしたら停止する。

- `t = n % (p*q)` の canonical left-pair witness theorem がある。
- eligible pair set が window 内の実 witness を数える。
- eligible pair card が window pair overlap の lower bound になる。
- center-aligned world predicate が明示されている。
- center-aligned triple overlap の canonical residue / progression control がある。
- target-30 で PairLower=3 を kernel-check する。
- 可能なら TripleUpper=0 まで kernel-check する。
- universal Goldbach を主張していない。
- build / axiom / forbidden construct audit を通す。
