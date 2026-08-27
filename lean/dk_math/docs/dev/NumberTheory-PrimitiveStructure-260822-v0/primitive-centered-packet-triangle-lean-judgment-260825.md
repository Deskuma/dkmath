# PRIM-L025 — Centered/Packet Triangle Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-040 に従い、L020 packet-coprimality と L024 centered-pair の proved API を
anchor `n = 4*k` の三席へ合成した。変更対象は次の二つである。

* `DkMath/NumberTheory/Legendre/CenteredPacketTriangle.lean`
* `DkMath/NumberTheory/Legendre.lean` の public facade import

既存 L020/L024 theorem の文や Primitive semantics は変更していない。generic graph /
coloring framework、asymptotic prime-counting、Legendre conjecture の証明は追加して
いない。次 checkpoint の PRIM-L026 も開始していない。

## 1. Executive outcome

**Outcome B — PROVED TRIANGLE STRUCTURAL REFINEMENT** と判定する。

`0 < k` と `Nat.Prime (4*k+1)` のもとで、三つの actual square-shell seats

```text
A = 2*k
B = 2*k+1
C = 6*k+1
```

に対して、Lean は次を証明した。

1. A, B, C はすべて `SquareOffset (4*k)` に属する。
2. 完全な square points A/B、B/C、A/C は pairwise coprime である。
3. したがって三つの actual old-prime support Finset は pairwise disjoint である。
4. `SquareOffsetsFullyCovered (4*k)` なら、三つの seat は pairwise-distinct な old-prime
   witnesses を持つ。
5. optional な有限 world の帰結として、`3 ≤ (primeScalesUpTo (4*k)).card` も得られる。

これは三席 synthesis としては genuine な proof-backed refinement である。一方、三席
から座席数が `k` とともに増える family、strict incidence deficit、unbounded full-cover
obstruction、または四席以上への一般化は得られていない。従って Outcome A ではない。

## 2. Implemented declarations

新規 module `DkMath.NumberTheory.Legendre.CenteredPacketTriangle` に次を追加した。

| 宣言 | 内容 |
| --- | --- |
| `squareOffset_centeredPacketTriangle_A` | A=`2*k` の shell membership |
| `squareOffset_centeredPacketTriangle_B` | B=`2*k+1` の shell membership |
| `squareOffset_centeredPacketTriangle_C` | C=`6*k+1` の shell membership |
| `coprime_centeredPacketTriangle_AB` | consecutive complete points の coprimality |
| `coprime_four_mul_k_two_mul_k_add_one` | packet base `2*k+1` と anchor `4*k` の coprimality |
| `coprime_centeredPacketTriangle_BC` | existing packet theorem による B/C coprimality |
| `not_four_mul_k_add_one_dvd_centeredPacketTriangle_A` | centered prime gap が A を割らないこと |
| `coprime_centeredPacketTriangle_AC` | centered prime gap による A/C complete coprimality |
| `disjoint_squareOffsetPrimeSupport_of_coprime_points` | complete-point coprimalityから support disjointness |
| `centeredPacketTriangle_points_pairwise_coprime` | 三つの complete-point coprimality の conjunction |
| `disjoint_centeredPacketTriangle_support_AB` | A/B support disjointness |
| `disjoint_centeredPacketTriangle_support_BC` | B/C support disjointness |
| `disjoint_centeredPacketTriangle_support_AC` | A/C support disjointness |
| `exists_three_distinct_centeredPacketTriangle_witnesses_of_fullyCovered` | full-cover の三 witness consumer |
| `three_le_primeScalesUpTo_card_of_centeredPacketTriangle_fullyCovered` | old prime world の cardinality lower bound |

module docstring と各 public declaration に、有限 structural refinement であり予想の
証明ではないことを含む簡潔な数学的説明を付けた。

## 3. L025-1 — shell membership

`0 < k` から、`n=4*k` に対して

```text
1 ≤ 2*k       and 2*k ≤ 8*k
1 ≤ 2*k+1     and 2*k+1 ≤ 8*k
1 ≤ 6*k+1     and 6*k+1 ≤ 8*k
```

を自然数上で `omega` により証明した。最後の上界だけは `0 < k` を必要とする。

該当宣言:

* `squareOffset_centeredPacketTriangle_A`
* `squareOffset_centeredPacketTriangle_B`
* `squareOffset_centeredPacketTriangle_C`

## 4. L025-2 — consecutive pair A/B

完全な点を

```text
Apoint = (4*k)^2 + 2*k
Bpoint = (4*k)^2 + (2*k+1)
```

とすると、自然数等式

```text
Bpoint = Apoint + 1
```

が成立する。既存の `Nat.coprime_self_add_right` を使い、

```lean
Nat.Coprime Apoint Bpoint
```

を証明した。因数分解や support API はこの pair の証明には使用していない。

該当宣言: `coprime_centeredPacketTriangle_AB`

## 5. L025-3 — packet pair B/C

まず任意の `k` について

```lean
Nat.Coprime (4*k) (2*k+1)
```

を証明した。証明は `2*k+1` と `2*k`、および `2` の coprimality を
`Nat.coprime_mul_iff_right` で組み合わせる薄い Euclidean composition である。

次に既存の

```lean
coprime_squarePacketPoints_of_coprime_offset
```

へ `n=4*k`, `r=2*k+1` を渡した。右 packet offset は

```text
4*k + (2*k+1) = 6*k+1
```

なので、次を得る。

```lean
Nat.Coprime ((4*k)^2 + (2*k+1))
            ((4*k)^2 + (6*k+1))
```

該当宣言:

* `coprime_four_mul_k_two_mul_k_add_one`
* `coprime_centeredPacketTriangle_BC`

packet Euclidean argument は再実装していない。

## 6. L025-4 — centered pair A/C

L024 の centered index `j=2*k` に対応し、gap は

```text
4*k+1
```

である。`hprime : Nat.Prime (4*k+1)` のもとで、まず

```text
¬ (4*k+1) ∣ ((4*k)^2 + 2*k)
```

を証明した。

核心となる自然数 identity は

```text
2 * ((4*k)^2 + 2*k) + (4*k+1)
  = (4*k+1) * (8*k) + 1.
```

もし prime gap が Apoint を割れば、左辺を割る。右辺は
`Nat.dvd_add_iff_right` によって gap が `1` を割ることを意味し、prime の
`not_dvd_one` と矛盾する。

さらに

```text
Cpoint = Apoint + (4*k+1)
```

と `Nat.coprime_self_add_right` を組み合わせ、要求されていた stronger statement

```lean
Nat.Coprime ((4*k)^2 + 2*k)
            ((4*k)^2 + (6*k+1))
```

を Lean で証明した。したがって L025-4 は old-support disjointness に留まらず、
complete-point coprimality まで成功している。

該当宣言:

* `not_four_mul_k_add_one_dvd_centeredPacketTriangle_A`
* `coprime_centeredPacketTriangle_AC`

## 7. L025-5 — pairwise support separation

一般補題

```lean
disjoint_squareOffsetPrimeSupport_of_coprime_points
```

を追加した。support membership から各 prime が両 complete point を割ることを取り出し、
`Nat.Prime.not_coprime_iff_dvd` で complete-point coprimality に反することを示す。

これを A/B、B/C、A/C の三つへ適用し、

```lean
centeredPacketTriangle_points_pairwise_coprime
```

および次の三つの Finset disjointness theorem を得た。

* `disjoint_centeredPacketTriangle_support_AB`
* `disjoint_centeredPacketTriangle_support_BC`
* `disjoint_centeredPacketTriangle_support_AC`

これは単に三つの Finset の cardinality を比較したものではなく、actual old-prime
support の pairwise disjointness である。

## 8. L025-6 — full-cover three-witness consumer

既存の

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

を三席へ適用し、各 support が nonempty であることを得た。三つの support disjointness
を使って、次を証明した。

```lean
∃ p q ℓ,
  p ≠ q ∧ p ≠ ℓ ∧ q ≠ ℓ ∧
  p ∈ squareOffsetPrimeSupport (4*k) (2*k) ∧
  q ∈ squareOffsetPrimeSupport (4*k) (2*k+1) ∧
  ℓ ∈ squareOffsetPrimeSupport (4*k) (6*k+1)
```

該当宣言:
`exists_three_distinct_centeredPacketTriangle_witnesses_of_fullyCovered`

これは三つの arbitrary divisor ではなく、既存の bounded prime support Finset に属する
三つの pairwise-distinct witnesses である。

## 9. L025-7 — finite-world cardinality

optional target も実装した。

```lean
3 ≤ (primeScalesUpTo (4*k)).card
```

三 witness を `primeScalesUpTo (4*k)` の membership へ変換し、三要素 Finset の
cardinality を比較しただけである。これは必要条件の restatement であり、prime-counting
estimate や growing lower bound ではない。

該当宣言:
`three_le_primeScalesUpTo_card_of_centeredPacketTriangle_fullyCovered`

## 10. Stronger-beam judgment

### 証明できた beam

今回の Lean theorem surface は、L024 の局所 centered separation と L020 の packet
coprimalityを同じ三席に接続する。特に A/C については support disjointness より強い
complete-point coprimalityが成立するため、三 witness theorem は単なる三つの独立した
pair theorem の列挙ではない。

### 得られなかった beam

次のいずれも、今回の仮定と既存 API からは得ていない。

1. `k` とともに増える pairwise-disjoint seat family。
2. `3 ≤ card` を超える strict incidence deficit。
3. 任意に多くの k に対する `SquareOffsetsFullyCovered (4*k)` の矛盾。
4. 同じ mechanism だけで四席以上を pairwise separate する reusable construction。

今回の三席は、A/B の consecutive relation、B/C の packet relation、A/C の一つの
prime centered gapという、固定された三種類の relation の同時成立に依存する。これを
そのまま複数の k や追加 seat へ繰り返せる theorem は実装していない。従って、三 witness
と cardinality 3 は local structural consequence であり、unbounded obstruction では
ない。

特に `k=1` の数値ケースを使って全称的な Legendre statement を作ることもしていない。

## 11. Outcome and stop boundary

**Outcome B — PROVED TRIANGLE STRUCTURAL REFINEMENT**。

三つの complete points と supports の pairwise separation、および full-cover からの
三つの pairwise-distinct old-prime witnessesは Lean で確立した。しかし、これ以上の
growing family、strict deficit、contradiction は未取得である。

この checkpoint の停止点は次の通り。

* `CenteredPacketTriangle.lean` の L025-1〜L025-7 を保持する。
* facade import を保持する。
* report に記録した weaker/stronger boundary を越えて新しい framework を追加しない。
* PRIM-L026 は自動開始しない。

## 12. Validation

次を実行し、成功した。

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketTriangle
lake build DkMath.NumberTheory.Legendre
```

対象 module build は 8678 jobs、facade build は 8685 jobs を完了した。`git diff --check`、
trailing whitespace 検査、禁止 placeholder 検査も clean である。全 repository build、
commit、push、CI はこの checkpoint の範囲外であり、実施していない。
