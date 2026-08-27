# PRIM-L027 — Repaired Four-Seat Clique Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-042 に従い、L026 の第四席 `6*k+2` を

```text
D' = 6*k+3
```

へ移し、A/B/C/D' の complete-point coprimality を Lean で判定した。既存の
L025/L026 module と theorem statement は変更せず、新規 module と public facade
import だけを追加した。graph / coloring framework、analytic number theory、
Legendre conjecture の証明、PRIM-L028 の開始は行っていない。

## 1. Executive outcome

**Outcome C — REPAIR FAILS** と判定する。

理由は、指示書が L027-1 に要求する `0 < k` での shell membership が `k=1` で偽
だからである。実際、anchor `4` の shell は offset `1` 以上 `8` 以下だが、修正版
第四席は `6*1+3=9` であり、Lean は次を証明した。

```lean
¬ SquareOffset 4 9
```

ただし、正しい最小条件 `2 ≤ k` に修正すれば、L027-2 から L027-8 の arithmetic
部分は成立した。従って、修正版四席 clique の局所結果は source に保存し、偽の
`0 < k` shell claim は明示的反例として残した。

## 2. Implemented declarations

追加 module:

```text
DkMath/NumberTheory/Legendre/CenteredPacketClique4.lean
```

public facade:

```text
DkMath/NumberTheory/Legendre.lean
```

主要な追加宣言は次のとおりである。

| 宣言 | 内容 |
| --- | --- |
| `not_squareOffset_centeredPacketClique4_at_one` | `k=1` の L027-1 反例 |
| `squareOffset_centeredPacketClique4_D` | `2≤k` で D' の shell membership |
| `coprime_centeredPacketClique4_AC` | A/C の prime 仮定なし coprimality |
| `coprime_centeredPacketClique4_CD` | C/D' coprimality |
| `coprime_centeredPacketClique4_BD` | B/D' coprimality。実際は全 `k` |
| `common_centeredPacketClique4_AD_dvd_fifteen` | A/D' 共通素因子の `g` と `15` への reduction |
| `coprime_centeredPacketClique4_AD` | `Coprime (4*k+3) 15` から A/D' coprimality |
| `centeredPacketClique4_points_pairwise_coprime` | 四 complete points の全六辺 |
| `centeredPacketClique4_supports_pairwise_disjoint` | 四 actual support の全六組 disjointness |
| `exists_four_distinct_centeredPacketClique4_witnesses_of_fullyCovered` | `2≤k` と full cover から四 distinct witnesses |
| `coprime_four_mul_periodicClique4_family` | `k=15*t+16` の unbounded periodic subfamily |

module docstring と各 public theorem docstring に、`0<k` の失敗、`2≤k` の salvage、
および Legendre conjecture へは到達しない境界を記載した。

## 3. L027-1 — shell membership obstruction and salvage

要求された命題

```lean
0 < k → SquareOffset (4*k) (6*k+3)
```

は成立しない。`k=1` で `SquareOffset 4 9` が偽であることを
`not_squareOffset_centeredPacketClique4_at_one` として固定した。

一方、`2≤k` なら

```lean
SquareOffset (4*k) (6*k+3)
```

を `omega` で証明した。従って、以後の four-seat witness theorem はこの正しい
shell 条件を明示的に仮定する。

## 4. L027-2 — unconditional A/C

L025 の `Nat.Prime (4*k+1)` 仮定を用いず、任意の `k` について次を証明した。

```lean
Nat.Coprime
  ((4*k)^2 + 2*k)
  ((4*k)^2 + (6*k+1))
```

共通素数 `q` があると仮定すると、差分から `q ∣ 4*k+1` を得る。さらに

```text
2*Apoint + (4*k+1) = (4*k+1)*(8*k) + 1
```

により `q ∣ 1` となり、素数が `1` を割れないことと矛盾する。

## 5. L027-3 and L027-4 — C/D' and B/D'

C/D' は

```text
D'point = Cpoint + 2
```

であり、Cpoint は奇数なので `Nat.coprime_self_add_right` により coprime である。

B/D' では差分

```text
D'point - Bpoint = 4*k+2 = 2*(2*k+1)
```

を用いた。共通素数 `q` を仮定すると、`q=2` の場合は Bpoint の奇性と矛盾する。
`q ∣ 2*k+1` の場合は

```text
Bpoint + 3*(2*k+1) = (2*k+1)*(8*k) + 4
```

から `q ∣ 4`、従って `q=2` を得て同じ矛盾になる。この定理は実際には `k` の
正値条件を必要とせず、全 `k` で成立する形にした。

## 6. L027-5 — A/D' constant-15 reduction

```text
Apoint  = (4*k)^2 + 2*k
D'point = (4*k)^2 + (6*k+3)
g       = 4*k+3
```

とおく。`q` が Apoint と D'point の共通素因子なら、差分から `q ∣ g` を得る。
さらに

```text
2*Apoint + 5*g = g*(8*k) + 15
```

を使うと `q ∣ 15` となる。source の thin theorem はこれをより強く

```lean
q ∣ 4*k+3 ∧ q ∣ 15
```

として公開している。

したがって

```lean
Nat.Coprime (4*k+3) 15
```

のもとでは、共通素数 `q` が `4*k+3` と `15` を同時に割ることができず、次を
得る。

```lean
Nat.Coprime
  ((4*k)^2 + 2*k)
  ((4*k)^2 + (6*k+3))
```

この `15` 条件は `Nat.Prime (4*k+3)` に置換していない。

## 7. L027-6 — four complete points and supports

`Nat.Coprime (4*k+3) 15` のもとで、A/B/C/D' の全六辺を conjunctive theorem
として公開した。

```text
A/B   existing consecutive edge
B/C   existing packet edge
A/C   unconditional strengthened edge
C/D'  difference-2 edge
B/D'  difference-2*(2*k+1) reduction
A/D'  fixed-15 reduction
```

この complete-point theorem 自体は `2≤k` を必要としない。`2≤k` が必要なのは、
D' が実際に対象 shell に属すること、および full-cover witness consumer である。

既存の

```lean
disjoint_squareOffsetPrimeSupport_of_coprime_points
```

を六辺に適用し、四 actual `squareOffsetPrimeSupport` Finsets の pairwise disjointness
も証明した。

## 8. L027-7 — full-cover four-distinct-witness consumer

`2≤k`、`Nat.Coprime (4*k+3) 15`、および

```lean
hfull : SquareOffsetsFullyCovered (4*k)
```

から、次の内容を証明した。

```lean
∃ pA pB pC pD,
  all six pairwise inequalities among pA,pB,pC,pD
  ∧ pA ∈ support A
  ∧ pB ∈ support B
  ∧ pC ∈ support C
  ∧ pD ∈ support D'
```

各 support の nonempty 性は既存の
`squareOffsetCovered_iff_primeSupport_nonempty` から取り出し、distinctness は
support disjointness から得た。`4 ≤ (primeScalesUpTo (4*k)).card` の二次的定理は
追加していない。今回の required witness consumer に必要な範囲で停止した。

## 9. L027-8 — periodic subfamily

`k=15*t+16` と置くと

```text
4*k+3 = 67 + (4*t)*15
```

であり、`Coprime 67 15` と `Nat.coprime_add_mul_right_left` から

```lean
Nat.Coprime (4 * (15*t + 16) + 3) 15
```

を任意の `t` について証明した。従って `2≤k` も満たす unbounded elementary
subfamily である。これは条件の periodic availability を示すだけであり、full cover
や Legendre conjecture を導くものではない。

## 10. Mandatory stronger-beam judgment

今回の四席構成から得られる要求 witness 数は四で一定である。source では graph /
coloring abstraction を導入していない。追加の fifth seat、席数が parameter と共に
増える pairwise-coprime family、available old-prime directions に対する growing
deficit、または strict incidence deficit は証明していない。

従って、この checkpoint の四席 theorem は有効な局所 refinement だが、growing
multi-seat leverage ではない。`0<k` の shell claim が偽であるため、指示書の分類規則に
従い Outcome B+ ではなく Outcome C とする。

## 11. Validation

次を実行し、成功を確認した。

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketClique4
-- Build completed successfully (8680 jobs).

lake build DkMath.NumberTheory.Legendre
-- Build completed successfully (8687 jobs).
```

四席 module の最終 build log に warning はなく、証明 placeholder や新規公理は追加して
いない。`git diff --check`、trailing-whitespace audit、
forbidden-placeholder audit も実行範囲として確認した。

## 12. Stop boundary

L026 の exceptional collision module は保持した。L027 では、偽の `0<k` shell claim を
反例として固定し、`2≤k` へ修正した場合の four-seat arithmetic と periodic family
までを実装した。四 distinct witnesses は full-cover 仮定の下でのみ得られる。

ここで停止し、PRIM-L028、Legendre conjecture の証明、analytic prime distribution、
および growing clique search は開始しない。
