# PRIM-L031 — Fresh-Collision Matching / Consecutive Small-Cofactor Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-046 に従い、L030 の exact fresh-collision gcd classification を再証明せず、
その fresh branch の内部形状を Lean で正規化した。新規 module
`DkMath/NumberTheory/Legendre/FreshCollisionMatching.lean` を追加し、公開 facade
`DkMath/NumberTheory/Legendre.lean` から import した。

L022、L025--L030 の public statement は変更していない。一般 graph/matching library、
analytic prime distribution、PNT 系の評価、Legendre 予想の証明は導入していない。

## 1. Executive outcome

**Outcome B — EXACT FRESH-COLLISION MATCHING STRUCTURE** と判定する。

Lean は、L030 の非自明 branch について次を証明した。

```text
old-support disjoint + gcd ≠ 1
  -> q := gcd は prime かつ n < q
  -> seat gap = q
  -> n^2+r = q*k, n^2+s = q*(k+1), 0 < k, k+1 ≤ n
  -> 各 shell point の fresh prime q は一意
  -> lower/upper endpoint はそれぞれ一意で、同じ seat の lower/upper 兼用も不可
  -> bounded old support は k と k+1 に移る
```

ただし、full-cover の仮定から得られるのは consecutive bounded cofactors の old prime
content までであり、`k<n` を使って `SquareOffsetsFullyCovered k` や Legendre obstruction
を再構成する theorem は得られていない。従って新しい descent や L029 を超える capacity
breaker は主張しない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `freshCollision_gcd_eq_orderedOffsetGap` | 非自明 fresh gcd が ordered offset gap と一致 |
| `freshCollision_crosses_anchor` | `r < n < s` の midpoint crossing |
| `freshCollision_consecutive_smallCofactor` | `q*k` と `q*(k+1)`、`0<k`、`k+1≤n` |
| `unique_fresh_prime_divisor_of_squareOffset` | 一つの shell point に対する fresh prime divisor の一意性 |
| `FreshCollisionPair` | 最小限の ordered fresh-collision pair predicate |
| `freshCollision_lower_endpoint_unique` | lower endpoint の partner 一意性 |
| `freshCollision_upper_endpoint_unique` | upper endpoint の partner 一意性 |
| `not_freshCollision_lower_and_upper` | 一つの seat が lower/upper を兼ねることの禁止 |
| `mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor` | bounded support と cofactor divisor の同値 |
| `primeScaleGeneratedBy_freshCollision_cofactors` | `k` と `k+1` の old-generated 性 |
| `freshCollision_cofactors_oldCovered_of_fullyCovered` | full cover から両 cofactor の old prime content |
| `freshCollision_three_one_six_consecutive_cofactor` | `n=3,r=1,s=6,q=5,k=2` の sanity witness |

module docstring と各 public theorem docstring は、fresh common prime を complete-point
coprimalityと混同しないこと、ここで得られるのが有限構造であること、Legendre 予想を
主張しないことを明記する程度に整備した。

## 3. L031-1 — exact gap theorem and location

`prime_and_fresh_of_disjoint_squareOffsetPrimeSupport_of_gcd_ne_one` から

```lean
q := Nat.gcd (n ^ 2 + r) (n ^ 2 + s)
Nat.Prime q
n < q
```

を再利用した。L030 の
`gcd_squarePoints_dvd_orderedOffsetGap` と shell bound
`s-r < 2*n` を合わせると、`q ∣ s-r` かつ `s-r < 2*q` になる。正の multiple を
`q*c` と置いた有限 divisibility argument で `c=1` を示し、次を証明した。

```lean
s - r = Nat.gcd (n ^ 2 + r) (n ^ 2 + s)
```

さらに gap が `q>n` であり、shell の `s≤2*n` を満たすため、

```lean
r < n ∧ n < s
```

も証明した。従って fresh collision は lower half から upper half へ canonical に
cross する。

## 4. L031-2 — consecutive small-cofactor factorization

gcd の左 divisibility から `n^2+r=q*k` を取り、gap theorem を使って
`n^2+s=(n^2+r)+q` とした。よって

```lean
q * k = n ^ 2 + r
q * (k + 1) = n ^ 2 + s
```

が得られる。`r` 側の正値から `0<k`、`s` 側の strict upper bound
`n^2+s<(n+1)^2` と `n+1≤q` から

```lean
k + 1 ≤ n
```

を自然数の積の単調性だけで証明した。実数除法、対数、素数分布は使っていない。

## 5. L031-3 — fresh prime uniqueness

既存の generic square-body theorem
`eq_of_large_primes_dvd_le_squareBody` を薄く specialize した。
`SquareOffset n r` から point positivity と `squareBody n` 上限を得て、同じ point を割る
二つの prime `q₁,q₂` がともに `n` より大きければ、二つの大きな prime の積が square-body
上限を超えることを用いて、

```lean
q₁ = q₂
```

を得た。これは全 prime divisor の一意性ではなく、`n` より大きい fresh prime divisor
に限定された statement である。

## 6. L031-4 — ordered matching

`FreshCollisionPair n r s` は `r<s` を含む最小の arithmetic predicate とした。
二つの pair `r--s` と `r--t` では、それぞれの fresh gcd が point `n^2+r` を割る。
前節の一意性で二つの gcd が一致し、各 gcd が対応する gap と一致することから
`s=t` を証明した。同様に共通 upper endpoint について `r=t` を証明した。

また、`r--s` が `r<n` を与え、`t--r` が `n<r` を与えるため、同じ seat が lower endpoint
と upper endpoint を兼ねることはない。従って「matching」は一般 graph structure ではなく、
この arithmetic relation の endpoint uniqueness と canonical orientation の意味である。

## 7. L031-5 — old-support / cofactor transfer

`q>n` なので bounded prime `p≤n` は `q` と異なる。したがって `p∣q*k` から prime
divisibility を分解すると、`p∣q` の branch は除かれ、`p∣k` が残る。逆向きは
`p∣k` から `p∣q*k` を戻した。

この有限 arithmetic argument により、fresh split `q*k=n^2+r` について

```lean
p ∈ squareOffsetPrimeSupport n r ↔
  Nat.Prime p ∧ p ≤ n ∧ p ∣ k
```

を得た。`s` 側には `k+1` を適用した。さらに既存の
`primeScaleGeneratedBy_div_of_large_prime_dvd_le_squareBody` を再利用し、

```lean
PrimeScaleGeneratedBy (primeScalesUpTo n) k
PrimeScaleGeneratedBy (primeScalesUpTo n) (k+1)
```

も証明した。cofactor が prime であるとは主張していない。

## 8. L031-6 — full-cover consequence

`SquareOffsetsFullyCovered n` と `FreshCollisionPair n r s` を仮定すると、両 seat の
support は nonempty である。support/cofactor equivalence により、実際に

```text
∃ p, Prime p ∧ p≤n ∧ p∣k
∃ p, Prime p ∧ p≤n ∧ p∣(k+1)
```

を得た。同時に既存の `two_le_smallCofactor_of_covered_fresh_split` を再利用して
`2≤k` を得ている。これが今回の full-cover 消費の正確な範囲であり、

```text
fresh q > n を二点が共有
  -> consecutive bounded cofactors
  -> 各 seat の old cover は対応 cofactor に現れる
```

までである。

## 9. Concrete witness

L029/L030 の witness は消去していない。次を Lean で保持した。

```text
n=3, r=1, s=6
n^2+r=10, n^2+s=15
q=gcd(10,15)=5
k=2
10=5*2, 15=5*(2+1)
```

また、`FreshCollisionPair 3 1 6` と `q=5`, `k=2` の factorization を
`freshCollision_three_one_six_consecutive_cofactor` で確認した。これは fresh branch が
空でないことの sanity theorem であり、complete-point coprimalityへの逆強化を意味しない。

## 10. Descent / stronger-beam judgment

具体的な Lean の消費として `freshCollision_cofactors_oldCovered_of_fullyCovered` を
実装し、full-cover state から `k`, `k+1` の bounded old prime content を取り出した。
これは「小さい cofactor が存在する」だけでなく、両 cofactor が cover の old content を
持つことを確認する一段進んだ normalization である。

一方、次の形の theorem は得られていない。

```text
SquareOffsetsFullyCovered n
  -> SquareOffsetsFullyCovered m   (m<n)
```

`k<n` は証明されているが、offset の shell、全 cover、あるいは Legendre obstruction
を cofactor 側へ transport する API は既存 surface に無く、今回の hypotheses からは
再構成できない。従って `k<n` を descent と呼ばない。

また endpoint uniqueness は pair を一般 matching として数える capacity inequality を
新たに与えない。L029 の old-support capacity bridge を強化する独立の cardinality breaker
も得られていない。

## 11. Validation

指定 target を Lean / Mathlib v4.32.2 のまま実行し、成功した。

```text
lake build DkMath.NumberTheory.Legendre.FreshCollisionMatching
-- Build completed successfully (8689 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8692 jobs).
```

追加で `git diff --check`、trailing-whitespace audit、forbidden-placeholder audit を
実行する。full repository build、commit、push、CI はこの指示書の範囲外である。

## 12. Stop boundary

ここで停止する。L031 の exact matching/cofactor structure、support transfer、full-cover
cofactor consequence とその descent judgment までを実装・記録した。

次段階として未実施なのは、独立 provider の構成、smaller full-cover state の再構成、
新しい capacity inequality、analytic estimates、一般 graph abstraction、および
Legendre 予想の形式化である。
