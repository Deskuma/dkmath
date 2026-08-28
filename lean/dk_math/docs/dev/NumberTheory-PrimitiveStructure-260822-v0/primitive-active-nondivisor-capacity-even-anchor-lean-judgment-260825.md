# PRIM-L033 — Active Nondivisor-Prime Capacity / Even-Anchor Knife-Edge Elimination Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-048 に従い、anchor-coprime seats に対する有限 capacity world を
`primeScalesUpTo n` から exact な `squareAnchorNondivisorPrimes n` へ縮小した。
さらに L032 の prime-`2` ownership を even anchor に合成し、fresh-collision exception が
消えることを証明した。

L025--L032 の public theorem statements は変更していない。analytic prime counting、
general graph library、universal provider、cofactor descent、Legendre 予想の証明は
導入していない。

## 1. Executive outcome

**Outcome A — STRICT ACTIVE-WORLD CAPACITY SHRINK / EVEN-ANCHOR EXCEPTION ELIMINATION**
と判定する。

Lean は次を証明した。

```text
anchor-coprime active family
  -> capacity is bounded by nondivisor prime world
  -> this world is strictly smaller than the full old-prime world for 1<n

even anchor + active old-support separation
  -> no endpoint can own old prime 2
  -> L032 fresh collision is impossible
  -> complete-point pairwise coprimality
```

これは L032 の `+1` repair を even anchors では loss `0` にする構造圧縮である。ただし、
arbitrary `n` に対する active family provider は構成していないため、Legendre 予想は
主張しない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `PairwiseActiveOldSupportDisjointSquareSeatFamily` | anchor-coprime seats と nondivisor support の pairwise disjointness |
| `pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseActiveOldSupportDisjointSquareSeatFamily` | active family から L029 family への bridge |
| `pairwiseActiveOldSupportDisjointSquareSeatFamily_of_pairwiseOldSupportDisjointSquareSeatFamily` | coprime membership 下の逆 bridge |
| `card_pairwiseActiveOldSupportDisjointSquareSeatFamily_le_nondivisorPrimes_of_fullyCovered` | active world capacity bound |
| `not_fullyCovered_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily` | active threshold の strict obstruction |
| `exists_prime_squareCell_of_nondivisorPrimes_card_lt_pairwiseActiveOldSupportDisjointSquareSeatFamily` | active threshold の Frontier consumer |
| `card_squareAnchorDivisorPrimes_add_nondivisorPrimes` | exact old-world card decomposition |
| `squareAnchorDivisorPrimes_nonempty_of_one_lt` | `1<n` で anchor-divisor world が nonempty |
| `squareAnchorNondivisorPrimes_card_lt_primeScalesUpTo_of_one_lt` | active world の strict shrink |
| `pairwiseCoprimeSquareSeatFamily_of_even_pairwiseActiveOldSupportDisjointSquareSeatFamily` | even anchor の fresh exception elimination |
| `exists_prime_squareCell_of_even_pairwiseActiveOldSupportDisjointSquareSeatFamily_card_excess` | even-anchor active threshold consumer |
| `odd_anchor_thirteen_freshCollision_falseBeam` | odd-anchor false-beam witness |

module docstring と public theorem docstring に、active finite world の意味、even-anchor
composition、odd-anchor witness、provider 非構成の境界を記載した。

## 3. L033-1 — exact active-family interface

新 predicate は次である。

```lean
def PairwiseActiveOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, r ∈ squareAnchorCoprimeOffsets n) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetAnchorNondivisorSupport n r)
```

anchor-coprime membership から
`squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime` を再利用し、
L029 の actual old-support family と相互に移せる thin bridge を実装した。

## 4. L033-2 — localized capacity

full cover の下で active family の各 support は nonempty になる。support union は
`squareAnchorNondivisorPrimes n` に含まれ、pairwise disjointness により cardinality を
足し上げられる。従って次を得た。

```text
R.card ≤ (squareAnchorNondivisorPrimes n).card
```

この strict inequality から full cover の否定を得て、既存 Frontier API を通じて
`∃ p, Nat.Prime p ∧ SquareCell n p` を返す consumer も追加した。threshold は全
old-prime world の card へ戻していない。

## 5. L033-3 — strict shrink of the finite world

既存の exact partition

```text
squareAnchorDivisorPrimes n ∪ squareAnchorNondivisorPrimes n
  = primeScalesUpTo n
```

と disjointness から

```text
card(divisor world) + card(nondivisor world)
  = card(primeScalesUpTo n)
```

を証明した。`1<n` なら `Nat.exists_prime_and_dvd` で anchor の prime divisor を取り、
divisor world が nonempty であることを示せる。従って

```text
(squareAnchorNondivisorPrimes n).card < (primeScalesUpTo n).card
```

が得られる。これは API の rename ではなく、有限 threshold の material な縮小である。

## 6. L033-4 — even-anchor elimination

even anchor `n` では `2 ∣ n` である。anchor-coprime seat `r` の active support は
nondivisor support と一致するため、`2` はその support に入れない。

一方、L032 の `freshCollision_primeTwo_owner` は、fresh collision の exactly one
endpoint が support prime `2` を持つことを証明済みである。従って active family 内に
non-coprime pair があれば fresh collision に戻した時点で矛盾する。

主定理は次である。

```text
PairwiseActiveOldSupportDisjointSquareSeatFamily n R
  -> Even n
  -> PairwiseCoprimeSquareSeatFamily n R
```

full cover はこの elimination theorem に不要である。

## 7. L033-5 — even-anchor capacity consumer

even anchor の active family が

```text
card(nondivisor world) < R.card
```

を満たせば local square-cell prime を返す consumer を追加した。これは localized active
threshold を使う。even anchor では active family 自体が complete-coprime familyになるため、
L032 の `+1` repair loss は `0` である。

## 8. L033-6 — odd-anchor false beam

even-anchor elimination を奇数 anchor に一般化していない。次の witness を Lean で確認した。

```text
n = 13, r = 1, s = 18
13^2 + 1  = 170
13^2 + 18 = 187
gcd(170,187) = 17 > 13
```

`1` と `18` は `squareAnchorCoprimeOffsets 13` に属し、nondivisor supports は
disjoint だが、complete points は coprime ではない。共通 fresh prime は `17` である。

これは active localizationだけから global な complete coprimalityを主張できないことを示す。

## 9. Stronger-beam / provider judgment

1. **Yes**。`1<n` では active threshold は full old-prime threshold より厳密に小さい。
2. **Yes**。even anchor では active old-support separation が fresh exception を完全に排除する。
3. **Yes**。odd anchor `(13,1,18)` は同じ排除が一般には偽であることを示す。
4. **No provider**。任意の `n` で active threshold を超える family は構成していない。
5. **No descent / Legendre proof**。active localizationは有限 capacity を強化するが、普遍 provider や直接矛盾は与えない。

従って Outcome A は strict active-world shrink と even-anchor exception elimination の
意味での structural outcome であり、Legendre 予想の解決を意味しない。

## 10. Validation

指定 target を Lean / Mathlib v4.32.2 のまま実行する。

```text
lake build DkMath.NumberTheory.Legendre.ActivePrimeCapacity
-- Build completed successfully (8691 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8694 jobs).
```

追加で `git diff --check`、trailing-whitespace audit、forbidden-placeholder audit を
実行する。full repository build、commit、push、CI はこの指示書の範囲外である。

## 11. Stop boundary

ここで停止する。active finite capacity、strict world shrink、even-anchor fresh-collision
elimination、odd-anchor false beam、localized Frontier consumer までを実装・記録した。

次段階として未実施なのは、任意 anchor の active provider、odd-anchor `+1` knife-edge の
排除、descent、analytic estimates、および Legendre 予想の形式化である。
