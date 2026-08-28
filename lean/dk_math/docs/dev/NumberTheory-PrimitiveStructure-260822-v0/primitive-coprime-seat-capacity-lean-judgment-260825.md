# PRIM-L028 — Finite Coprime-Seat Capacity Bridge Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-043 に従い、L025/L027 の個別 seat witness 議論を有限 family の
capacity theorem に抽出した。新規 module は

```text
DkMath/NumberTheory/Legendre/CoprimeSeatCapacity.lean
```

であり、`DkMath/NumberTheory/Legendre.lean` に public facade import を追加した。
L025/L026/L027 の既存 theorem statement は変更していない。graph / coloring
framework、analytic prime-counting、K5/K6 の手作業探索、Legendre conjecture の
証明は行っていない。

## 1. Executive outcome

**Outcome A — DIRECT CAPACITY FRONTIER BRIDGE** と判定する。

Lean は次の二段を証明した。

1. full cover のもとで、有限の pairwise-coprime actual seat family の cardinality
   は `(primeScalesUpTo n).card` 以下である。
2. family cardinality が old-prime world の cardinalityを超えるなら full cover が
   失敗し、既存 Frontier API により実際の prime square-cell witness が得られる。

これは直接的な local capacity frontier bridge である。ただし、任意の `n>0` に
対して threshold を超える family を供給する universal provider は未証明なので、
Legendre conjecture を主張しない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `PairwiseCoprimeSquareSeatFamily` | shell membership と complete-point pairwise coprimality の有限 predicate |
| `squareOffsetPrimeSupport_subset_primeScalesUpTo` | actual support の old-prime world containment |
| `pairwiseDisjoint_squareOffsetPrimeSupport_of_family` | family の distinct seat support disjointness |
| `squareOffsetPrimeSupport_nonempty_of_family_fullyCovered` | full cover 下の各 support nonempty |
| `card_pairwiseCoprimeSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered` | 有限 capacity bound |
| `not_fullyCovered_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats` | strict capacity obstruction |
| `exists_prime_squareCell_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats` | Frontier 経由の local prime-square-cell witness |
| `centeredPacketClique4Offsets` | L027 の四 offsets を表す Finset |
| `pairwiseCoprimeSquareSeatFamily_centeredPacketClique4` | repaired L027/K4 の generic family 化 |
| `four_le_primeScalesUpTo_card_of_centeredPacketClique4_fullyCovered` | L027 から `4 ≤ old-prime-world.card` の回収 |

module docstring と public theorem docstring には、actual supports、有限 capacity、
local Frontier consumer、および universal provider が未達である境界を記載した。

## 3. L028-1 and L028-2 — family predicate and support containment

新しい predicate は構造体ではなく、次の二つの proposition の conjunction とした。

```lean
PairwiseCoprimeSquareSeatFamily n R :=
  (∀ r ∈ R, SquareOffset n r) ∧
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Nat.Coprime (n ^ 2 + r) (n ^ 2 + s)
```

support containment は `mem_squareOffsetPrimeSupport` から prime 性と `q≤n` を
取り出し、`mem_primeScalesUpTo` に戻すだけの thin theorem として実装した。
対象は arbitrary divisors ではなく、`squareOffsetPrimeSupport` に実際に現れる
bounded old primes である。

## 4. L028-3 and L028-4 — disjoint and nonempty supports

distinct seats `r≠s` に対して、family の complete-point coprimalityを既存の

```lean
disjoint_squareOffsetPrimeSupport_of_coprime_points
```

へ直接渡し、

```lean
(R : Set ℕ).PairwiseDisjoint
  (fun r => squareOffsetPrimeSupport n r)
```

を証明した。prime-divisor separation を family の各 edge について再証明していない。

また、`hfull : SquareOffsetsFullyCovered n` と shell membership から、既存の

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

を使って各 actual support の nonempty 性を得た。

## 5. L028-5 — finite capacity theorem

主定理は次である。

```lean
card_pairwiseCoprimeSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
```

証明は choice を使わず、support union の cardinality を数える有限証明にした。

```text
R.card
  ≤ ∑ r∈R, (support r).card
  = (R.biUnion support).card
  ≤ (primeScalesUpTo n).card
```

第一の不等式は full cover による各 support の positive cardinality、等号は
pairwise-disjoint Finset union の `Finset.card_biUnion`、最後の不等式は
support containment と `Finset.card_le_card` から得た。このため、seat ごとの
prime witness を選ぶ public choice function は追加していない。

## 6. L028-6 — direct capacity obstruction

次の contrapositive を証明した。

```lean
not_fullyCovered_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
```

仮定は同じ family 条件と

```lean
(primeScalesUpTo n).card < R.card
```

であり、full cover を仮定すると L028-5 の逆向き不等式と矛盾する。結果は

```lean
¬ SquareOffsetsFullyCovered n
```

である。

## 7. L028-7 — local prime-square-cell consumer

`hn : 0 < n` を追加し、strict capacity obstruction を既存 Frontier chain に接続した。

```lean
exists_prime_squareCell_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
```

では、full-cover failure を

```lean
not_squareOffsetsFullyCovered_iff_escaping_nonempty
```

で escaping offset `r` に変換する。その non-cover condition を
`supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` で support
disjointness に直し、既存の

```lean
prime_of_squareAnchoredSupportEscape
```

から `Nat.Prime (n^2+r)` を得る。最後に
`squareCell_iff_exists_squareOffset` を使い、

```lean
∃ p, Nat.Prime p ∧ SquareCell n p
```

を得た。これは local theorem であり、universal large-family provider を仮定して
いない。

## 8. L028-8 — L027/K4 sanity consumer

L027 の offset

```text
{2*k, 2*k+1, 6*k+1, 6*k+3}
```

を `centeredPacketClique4Offsets k` として Finset 化した。
`2≤k` と `Nat.Coprime (4*k+3) 15` のもとで、既存の
`centeredPacketClique4_points_pairwise_coprime` の各 edge を再利用し、generic
family predicate を構成した。

full cover を generic capacity theorem に渡すことで、次を回収した。

```lean
four_le_primeScalesUpTo_card_of_centeredPacketClique4_fullyCovered
```

これは L027 の四 distinct witnesses を手作業で再選択していない。L027 の original
proposal `0<k → SquareOffset (4*k) (6*k+3)` は `k=1` で偽だったが、既存の
counterexample と `2≤k` の repaired theorem surface は保持し、その corrected
surface を generic capacity consumer として使用した。

## 9. Stronger-beam judgment and remaining threshold

今回の抽象化で、残る combinatorial target は正確に次である。

```text
R ⊆ square shell
complete points pairwise coprime
and
(primeScalesUpTo n).card < R.card.
```

L027/K4 は full cover のもとで `4 ≤ old-prime-world.card` を要求するだけであり、
現在の theorem surface は old-prime world の cardinality を超える growing family を
供給しない。PNT、Chebyshev、Rosser--Schoenfeld、Jacobsthal、analytic sieve bounds、
および新しい clique search は導入していない。

従って、capacity bridge は完成したが、global Legendre provider や universal
large-family construction には進まない。

## 10. Validation

次を実行し、成功を確認した。

```text
lake build DkMath.NumberTheory.Legendre.CoprimeSeatCapacity
-- Build completed successfully (8687 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8688 jobs).
```

`git diff --check`、trailing-whitespace audit、forbidden-placeholder audit を対象
source/report に対して実行する。Lean / Mathlib は v4.32.2 のまま変更していない。

## 11. Stop boundary

有限 capacity inequality と local prime-square-cell consumer、および L027/K4 sanity
consumer までを実装した。L027 の `k=1` counterexample は削除せず、repaired `2≤k`
surface も変更していない。

ここで停止し、Legendre conjecture の証明、universal threshold provider、growing
family search、graph abstraction、PRIM-L029 は開始しない。
