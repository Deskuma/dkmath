# PRIM-L029 — Old-Support Capacity / Exact Difference Criterion Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-044 に従い、L028 の complete-point coprimality family を、有限 capacity
proof が実際に消費する actual bounded old-prime support disjointness へ弱めた。

新規 module:

```text
DkMath/NumberTheory/Legendre/OldSupportCapacity.lean
```

を追加し、`DkMath/NumberTheory/Legendre.lean` に facade import を追加した。
L025--L028 の public theorem statements は変更していない。L028 の末尾にあった
example-only K4 declarations は production surface から除去し、今回の module にも
再導入していない。graph / coloring / matching abstraction、growing-family search、
analytic prime-counting、Legendre conjecture の証明は行っていない。

## 1. Executive outcome

**Outcome A — STRICTLY WEAKER CAPACITY FRONTIER BRIDGE** と判定する。

次の全てを Lean で証明した。

1. complete-point pairwise coprimality から old-support pairwise disjointness への
   thin bridge;
2. `n=3`、offsets `{1,6}` による strictness witness;
3. ordered offsets の actual support disjointness と offset-gap divisibility の
   exact criterion;
4. weaker old-support family に対する finite capacity theorem;
5. strict capacity excess から Frontier 経由での local prime-square-cell witness。

従って、complete coprimality は capacity accounting には十分だが必要ではない。
ただし、任意の `n>0` に threshold 超過 family を供給する universal provider は
未証明であり、Legendre conjecture は主張しない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `PairwiseOldSupportDisjointSquareSeatFamily` | shell membership と actual old-support pairwise disjointness |
| `pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily` | L028 family から weaker family への bridge |
| `squareOffset_oldSupportCapacity_strictness_left` | `SquareOffset 3 1` |
| `squareOffset_oldSupportCapacity_strictness_right` | `SquareOffset 3 6` |
| `not_coprime_oldSupportCapacity_strictness_points` | `¬ Nat.Coprime 10 15` |
| `disjoint_oldSupportCapacity_strictness_supports` | supports at `n=3`, offsets `1,6` are disjoint |
| `exists_oldSupportDisjoint_not_completeCoprime_family` | strictness witness package |
| `disjoint_squareOffsetPrimeSupport_iff_no_bounded_prime_dividing_offset_gap` | exact ordered difference criterion |
| `card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered` | weaker finite capacity bound |
| `not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies` | weaker strict capacity obstruction |
| `exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies` | weaker local Frontier consumer |
| `legendreConjecture_of_universal_oldSupportCapacityProvider` | optional one-way sufficient provider theorem |

Module docstring と public theorem docstring には、old-support input が exact capacity
interface であること、fresh common primes の strictness、local-only boundary を記載した。

## 3. L029-1 and L029-2 — exact family interface

新しい predicate は structure ではなく、次の minimal conjunction とした。

```lean
PairwiseOldSupportDisjointSquareSeatFamily n R :=
  (∀ r ∈ R, SquareOffset n r) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetPrimeSupport n r)
```

L028 の

```lean
PairwiseCoprimeSquareSeatFamily n R
```

からの bridge は、既存の
`pairwiseDisjoint_squareOffsetPrimeSupport_of_family` をそのまま再利用した。
complete-point divisor separation を再証明していない。

## 4. L029-3 — strictness witness at `n=3`

`n=3`、`r=1`、`s=6` について、Lean は次を証明した。

```text
SquareOffset 3 1
SquareOffset 3 6
¬ Nat.Coprime 10 15
Disjoint
  (squareOffsetPrimeSupport 3 1)
  (squareOffsetPrimeSupport 3 6)
```

complete points は `10` と `15` であり、共通素数 `5` を持つ。しかし `5>3` なので
old-prime world `primeScalesUpTo 3` には属さない。実際の old supports に共通要素が
あると仮定すると、最初の support の prime divisor は `10` を割るため `2` または
`5`、かつ `q≤3` であり、`2` の場合は `15` を割れず、`5` の場合は bound に反する。

したがって、これは単なる predicate の rename ではなく、

```text
complete-point coprimality  =>  old-support disjointness
```

が strict であることを Lean が固定した witness である。

## 5. L029-4 — exact ordered difference criterion

`r≤s` のもとで、次を証明した。

```lean
Disjoint (squareOffsetPrimeSupport n r)
    (squareOffsetPrimeSupport n s) ↔
  ∀ q, Nat.Prime q → q ≤ n → q ∣ n ^ 2 + r →
    ¬ q ∣ s - r
```

証明の中心は自然数上の identity

```text
n^2+s = (n^2+r) + (s-r)
```

である。順方向では、bounded prime `q` が第一 complete point と gap の双方を
割るなら第二 support にも入るため disjointness と矛盾する。逆方向では、両 support
membership から第二 complete point の divisibility を取り出し、`Nat.dvd_add_iff_right`
で gap divisibility を得て criterion に反する。

定理は complete-point gcd = 1 に置き換えず、actual support membership、prime 性、
`q≤n` の bound を保持している。

## 6. L029-5 and L029-6 — weaker finite capacity

次の theorem を old-support family へ直接証明した。

```lean
card_pairwiseOldSupportDisjointSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
```

proof route は L028 と同じ finite union counting だが、complete-point coprimality は
仮定していない。

```text
R.card
  ≤ ∑ r∈R, (support r).card
  = (R.biUnion support).card
  ≤ (primeScalesUpTo n).card
```

各 support の nonempty 性は full cover と
`squareOffsetCovered_iff_primeSupport_nonempty` から得た。union の cardinality は
old-support family 自身の pairwise disjointness と `Finset.card_biUnion` で数え、
containment は L028 の support containment theorem を再利用した。choice function は
導入していない。

その contrapositive として、

```lean
not_fullyCovered_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
```

も証明した。これは weaker family を直接受け取り、complete-coprime family へ戻して
いない。

## 7. L029-7 — weaker local prime-square-cell consumer

`hn : 0 < n` と strict capacity excess のもとで、

```lean
exists_prime_squareCell_of_primeWorld_card_lt_pairwiseOldSupportDisjointSquareSeatFamilies
```

を証明した。L029-6 から full-cover failure を得て、既存の
`not_squareOffsetsFullyCovered_iff_escaping_nonempty` で escaping offset を取り出す。
その non-cover condition を
`supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` で support escape に
変換し、`prime_of_squareAnchoredSupportEscape` から actual prime square-cell witness
を得た。

## 8. L029-8 — optional provider theorem

次の一方向 theorem を追加した。

```lean
legendreConjecture_of_universal_oldSupportCapacityProvider
```

仮定は任意の `n>0` に対して、old-support-disjoint family `R` と
`(primeScalesUpTo n).card < R.card` を供給する provider である。この provider を
local prime consumer に渡して Legendre witness を得るだけであり、逆向き implication、
provider の存在、Legendre conjecture の証明は含まない。

## 9. Stronger-beam judgment and remaining provider problem

今回、capacity input は次のように明確に弱められた。

```text
complete-point pairwise coprimality
        ↓ strictly stronger
pairwise old-support disjointness
        ↓ exact capacity input
strict capacity excess
        ↓
local prime square-cell witness
```

ordered difference criterion により、将来の provider construction は各 old prime
`q≤n` について「第一 point を割る q が seat gap を割らない」という有限 divisibility
条件として検討できる。ただし、今回その条件を使った growing family の構成は行って
いない。

## 10. Validation

次を実行し、成功を確認した。

```text
lake build DkMath.NumberTheory.Legendre.OldSupportCapacity
-- Build completed successfully (8686 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8689 jobs).
```

`git diff --check`、trailing-whitespace audit、forbidden-placeholder audit を対象
source/report に対して実行する。Lean / Mathlib は v4.32.2 のまま変更していない。

## 11. Stop boundary

old-support exact family predicate、strictness witness、ordered difference criterion、
weaker capacity/frontier bridge、optional sufficient provider theorem までを実装した。
L027 の `k=1` counterexample と `2≤k` repaired theorem surface は保持し、L028 の
production module から example-only K4 declarations は除去した。

ここで停止し、universal provider search、growing family construction、analytic estimates、
graph abstraction、PRIM-L030 は開始しない。
