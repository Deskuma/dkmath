# PRIM-L032 — Two-Adic Fresh-Collision Uniqueness / One-Seat Repair Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-047 に従い、L031 の consecutive-cofactor theorem を利用して、fresh
collision が old prime `2` をどのように消費するかを形式化した。新規 module
`DkMath/NumberTheory/Legendre/FreshCollisionRepair.lean` を追加し、
`DkMath/NumberTheory/Legendre.lean` から import した。

L025--L031 の public theorem statements は変更していない。一般 graph/matching
library、analytic prime distribution、cofactor からの descent、Legendre 予想の証明は
導入していない。

## 1. Executive outcome

**Outcome A — EXACT ONE-SEAT REPAIR / PROVIDER COMPRESSION** と判定する。

Lean は次を証明した。

```text
fresh collision
  -> 2 ≤ n
  -> exactly one endpoint owns old prime 2

old-support-disjoint family
  -> at most one fresh-collision pair
  -> erase one endpoint
  -> complete-point pairwise-coprime family
```

従って L029 の actual old-support family は、L028 の complete-coprime familyから高々
一席だけ大きくなり得る。これは provider construction を圧縮する新しい構造結果だが、
それ自体は universal provider、descent、または Legendre 予想の証明ではない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `two_le_anchor_of_freshCollisionPair` | fresh collision から `2 ≤ n` |
| `freshCollision_primeTwo_owner` | exactly one endpoint の support に `2` |
| `freshCollisionPair_unique_in_oldSupportFamily` | old-support family 内の fresh pair 一意性 |
| `freshCollisionPair_of_not_coprime_of_oldSupportFamily` | 非 coprime ordered pair の fresh-collision 化 |
| `exists_pairwiseCoprimeSquareSeatFamily_subset_card_le_add_one` | erase による one-seat repair |
| `pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily_L032` | L028 から L029 への bridge |
| `exists_prime_squareCell_of_oldSupportFamily_card_excess_two` | `+2` margin の direct Frontier consumer |

module docstring と public theorem docstring には、prime `2` の finite ownership、
`+1` interface gap、そして Legendre 予想を主張しない境界を記載した。

## 3. L032-1 — prime `2` ownership

L031 の factorization

```text
n^2+r = q*k
n^2+s = q*(k+1)
0 < k
k+1 ≤ n
```

から `2≤n` を `two_le_anchor_of_freshCollisionPair` で得た。この theorem は full cover
を仮定していない。`k` と `k+1` の一方だけが偶数であり、既存の
`mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor` を `p=2` に specialize
すると、

```text
2 ∈ squareOffsetPrimeSupport n r ↔ 2 ∣ k
2 ∈ squareOffsetPrimeSupport n s ↔ 2 ∣ (k+1)
```

となる。従って `freshCollision_primeTwo_owner` は次を直接 endpoint support について
証明する。

```lean
(2 ∈ squareOffsetPrimeSupport n r ∧
  2 ∉ squareOffsetPrimeSupport n s) ∨
(2 ∉ squareOffsetPrimeSupport n r ∧
  2 ∈ squareOffsetPrimeSupport n s)
```

単に cofactor の偶奇を述べるだけでなく、actual support Finset の membership へ戻して
いる点がこの checkpoint の境界である。

## 4. L032-2 — one fresh collision in an old-support family

`freshCollisionPair_unique_in_oldSupportFamily` は、四 endpoint が
`PairwiseOldSupportDisjointSquareSeatFamily n R` に属する二つの ordered fresh pairs
`r--s` と `u--v` について、

```text
r = u ∧ s = v
```

を証明する。

各 pair の prime-`2` owner が異なるなら、old-support family の pairwise disjointnessに
反して両 support が `2` を共有する。同じ owner の場合は、
`freshCollision_lower_endpoint_unique`、`freshCollision_upper_endpoint_unique`、
`not_freshCollision_lower_and_upper` を使い、lower/lower、upper/upper、lower/upper の
四場合を処理した。一般 graph theorem は導入していない。

## 5. L032-3 — the unique non-coprime exception

`freshCollisionPair_of_not_coprime_of_oldSupportFamily` は、old-support family の
ordered distinct members `r<s` に対して、

```text
¬ Nat.Coprime (n^2+r) (n^2+s)
  -> FreshCollisionPair n r s
```

を証明する。support disjointness は family hypothesis から取り、`¬Coprime` は
`Nat.coprime_iff_gcd_eq_one` により gcd 非単位へ変換している。L030 の gcd classification
自体は再証明していない。

この結果と L032-2 により、old-support-disjoint family 内で complete point が non-coprime
になる ordered pair は高々一つである。

## 6. L032-4 — one-seat repair

主定理は次である。

```lean
∃ R' : Finset ℕ,
  R' ⊆ R ∧ PairwiseCoprimeSquareSeatFamily n R' ∧
    R.card ≤ R'.card + 1
```

`exists_pairwiseCoprimeSquareSeatFamily_subset_card_le_add_one` は二場合に分けた。

### fresh exception がない場合

`R'=R` とする。もし `R` 内に non-coprime pair があれば L032-3 により fresh collision
となり、fresh collision が存在しない仮定に反する。従って `R` 自体が complete-coprime
family である。

### fresh exception `r--s` がある場合

`R' = R.erase s` とする。erase 内の non-coprime pair は L032-3 で fresh collisionに
戻り、L032-2 により `r--s` と同じ pair でなければならない。しかし `s` は erase 後に
存在しないため矛盾する。cardinality は `Finset.card_erase_of_mem` から

```text
R.card = (R.erase s).card + 1
```

を得る。

## 7. L032-5 — exact L028/L029 relation

complete-coprime family から old-support-disjoint family への bridgeは既存の L029 theorem
を `pairwiseOldSupportDisjointSquareSeatFamily_of_pairwiseCoprimeSquareSeatFamily_L032`
として薄く公開した。逆向きの predicate equivalence は主張していない。L029 の
`n=3`, `{1,6}` strictness witness がその反例として残る。

今回の exact quantitative relation は、任意の old-support-disjoint family `R` に対して、
one-seat repair `R'` が存在し、

```text
R' ⊆ R
PairwiseCoprimeSquareSeatFamily n R'
R.card ≤ R'.card + 1
```

となることである。したがって L029 の weakening は arbitrarily large matching gain では
なく、高々一席の差に圧縮された。

## 8. L032-6 — capacity/frontier sanity consumer

`exists_prime_squareCell_of_oldSupportFamily_card_excess_two` は、

```text
(primeScalesUpTo n).card + 1 < R.card
```

を old-support family から受け、repair 後にも
`(primeScalesUpTo n).card < R'.card` が残ることを omega で確認し、既存の L028 Frontier
consumer を直接適用する。この theorem は L029 の直接 threshold より弱い sanity
comparison であり、stronger frontier theorem とは扱っていない。

従って knife-edge は明確になった。

```text
R.card = (primeScalesUpTo n).card + 1
```

の可能性に一つの fresh-collision exception がある場合、one-seat repair 後の L028
capacity excess は消える。ここから full cover の矛盾や universal provider はまだ得られない。

## 9. Stronger-beam judgment

1. **Yes**。prime `2` は every fresh collision の exactly one endpoint に現れる。
2. **Yes**。old-support-disjoint family は高々一席を削除すれば complete-coprime familyになる。
3. **Yes**。L028/L029 の差は unquantified weakening ではなく exact `+1` gap として形式化された。
4. **No new contradiction**。`+1` knife-edge を full cover だけから排除する theorem は得られていない。
5. **No provider/descent**。repair は provider を圧縮するが、growing family や cofactor descentは構成しない。

## 10. Validation

指定 target を Lean / Mathlib v4.32.2 のまま実行し、成功した。

```text
lake build DkMath.NumberTheory.Legendre.FreshCollisionRepair
-- Build completed successfully (8690 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8693 jobs).
```

追加で `git diff --check`、trailing-whitespace audit、forbidden-placeholder auditを
実行する。full repository build、commit、push、CI はこの指示書の範囲外である。

## 11. Stop boundary

ここで停止する。prime-2 ownership、old-support family 内の fresh pair uniqueness、
non-coprime exception characterization、one-seat repair、`+2` margin の Frontier sanity
consumer までを実装・記録した。

未実施なのは、knife-edge `+1` case の独立矛盾、universal provider、smaller full-cover
state の構成、analytic estimates、一般 graph abstraction、および Legendre 予想の形式化である。
