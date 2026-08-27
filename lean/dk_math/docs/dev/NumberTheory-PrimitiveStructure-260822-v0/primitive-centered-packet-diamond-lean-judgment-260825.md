# PRIM-L026 — Centered/Packet Diamond Obstruction Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-041 に従い、L025 の三席

```text
A = 2*k,  B = 2*k+1,  C = 6*k+1
```

へ第四席 `D = 6*k+2` を追加し、四席の complete-point 関係を Lean で判定した。
変更対象は次の二つである。

* `DkMath/NumberTheory/Legendre/CenteredPacketDiamond.lean`
* `DkMath/NumberTheory/Legendre.lean` の public facade import

既存 L020/L024/L025 の theorem statement や Primitive semantics は変更していない。
graph / coloring / matching framework、Legendre conjecture の証明、PRIM-L027 の開始は
行っていない。

## 1. Executive outcome

**Outcome B — PROVED DIAMOND OBSTRUCTION / EXCEPTIONAL COLLISION** と判定する。

`0 < k` と `Nat.Prime (4*k+1)` のもとで、Lean は次を証明した。

* D は `SquareOffset (4*k)` に属する。
* C/D は consecutive complete points なので coprime。
* B/D は prime gap `4*k+1` を用いて complete-point coprime。
* A/D は disjoint ではない。実際、prime `2` が両 support に属する。
* A/D の共通 old-prime support は正確に `{2,3}` に局所化できる。
* A/B, A/C, B/C, B/D, C/D の五つの complete-point edges は coprime。
* full cover から四つの support witnesses が得られ、五つの forced inequalities と
  A/D collision classifier が成立する。

ただし A/D の `2` collision を除去する独立条件は得られず、四つの witnesses が
pairwise distinct であるとも主張していない。従って direct four-seat leverage や
growing family には到達していない。

## 2. Implemented declarations

| 宣言 | 内容 |
| --- | --- |
| `squareOffset_centeredPacketDiamond_D` | D の shell membership |
| `coprime_centeredPacketDiamond_CD` | C/D complete-point coprimality |
| `not_four_mul_k_add_one_dvd_centeredPacketTriangle_B` | prime gap が B point を割らないこと |
| `coprime_centeredPacketDiamond_BD` | B/D complete-point coprimality |
| `two_mem_centeredPacketDiamond_support_A` | `2` が A support に属すること |
| `two_mem_centeredPacketDiamond_support_D` | `2` が D support に属すること |
| `not_disjoint_centeredPacketDiamond_support_AD` | A/D support の非 disjointness |
| `common_centeredPacketDiamond_support_AD_eq_two_or_three` | A/D common support の `{2,3}` localization |
| `centeredPacketDiamond_five_edges_and_AD_obstruction` | 五つの good edges と A/D obstruction |
| `exists_centeredPacketDiamond_four_witnesses_of_fullyCovered` | full-cover four-seat witness package |

module docstring と public theorem docstring には、五つの good edgesと例外的な A/D
collisionを記載し、四 distinct witnesses や Legendre conjectureを主張しない境界を
明示した。

## 3. L026-1 — fourth seat

`0 < k` から

```text
1 ≤ 6*k+2
6*k+2 ≤ 8*k
```

を `omega` で証明し、次を得た。

```lean
SquareOffset (4*k) (6*k+2)
```

該当宣言: `squareOffset_centeredPacketDiamond_D`

## 4. L026-2 — C/D consecutive coprimality

完全な点

```text
Cpoint = (4*k)^2 + (6*k+1)
Dpoint = (4*k)^2 + (6*k+2)
```

について

```text
Dpoint = Cpoint + 1
```

を自然数上で証明し、`Nat.coprime_self_add_right` を適用した。

該当宣言: `coprime_centeredPacketDiamond_CD`

## 5. L026-3 — B/D prime-gap coprimality

`P = 4*k+1` とおく。B/D の差は P であり、もし P が Bpoint を割れば、次の identity

```text
2 * Bpoint + P = P * (8*k) + 3
```

から `P ∣ 3` が得られる。しかし `0 < k` なら `P ≥ 5` であり、`P ≤ 3` と矛盾する。
この arithmetic argument を Lean で証明した。

`hprime : Nat.Prime P` と `Nat.Prime.coprime_iff_not_dvd`、さらに
`Dpoint = Bpoint + P` を組み合わせ、次を得た。

```lean
Nat.Coprime Bpoint Dpoint
```

該当宣言:

* `not_four_mul_k_add_one_dvd_centeredPacketTriangle_B`
* `coprime_centeredPacketDiamond_BD`

この edge の complete coprimality は成功している。

## 6. L026-4 — A/D false beam

A/D の complete points は

```text
Apoint = (4*k)^2 + 2*k
Dpoint = (4*k)^2 + 6*k + 2
```

である。Lean は明示的な factorization

```text
Apoint = 2 * (8*k^2 + k)
Dpoint = 2 * (8*k^2 + 3*k + 1)
```

を証明し、`2 ≤ 4*k` と `mem_squareOffsetPrimeSupport` を通じて

```lean
2 ∈ squareOffsetPrimeSupport (4*k) (2*k)
2 ∈ squareOffsetPrimeSupport (4*k) (6*k+2)
```

を得た。

従って次の negative structural theorem も証明した。

```lean
¬ Disjoint
  (squareOffsetPrimeSupport (4*k) (2*k))
  (squareOffsetPrimeSupport (4*k) (6*k+2))
```

これは四席が存在することから四つの pairwise-disjoint support、または四 distinct
witnessesを推論してはいけないことを示す Lean-certified false beam である。ただし、
support の非 disjointnessだけから四 distinct witnessesが不可能だとは主張していない。

該当宣言:

* `two_mem_centeredPacketDiamond_support_A`
* `two_mem_centeredPacketDiamond_support_D`
* `not_disjoint_centeredPacketDiamond_support_AD`

## 7. L026-5 — A/D common support localization

q が A/D の actual old-prime support に共通するとする。support membershipから q が
primeであり、両 pointを割ることを取り出す。

まず差分

```text
Dpoint = Apoint + (4*k+2)
4*k+2 = 2*(2*k+1)
```

により、q は `2*(2*k+1)` を割る。`Nat.Prime.dvd_mul` によって二つの場合に分かれる。

1. `q ∣ 2` なら、q の prime 性から `q = 2`。
2. `q ∣ 2*k+1` なら、次の identity を使う。

```text
Apoint + 3*(2*k+1) = (2*k+1)*(8*k) + 3
```

q は左辺を割るので q は 3 を割り、prime 性から `q = 3`。

よって次を証明した。

```lean
q ∈ squareOffsetPrimeSupport (4*k) (2*k) →
q ∈ squareOffsetPrimeSupport (4*k) (6*k+2) →
q = 2 ∨ q = 3
```

該当宣言: `common_centeredPacketDiamond_support_AD_eq_two_or_three`

これは単なる parity observation より強い、A/D common old-prime support の有限分類で
ある。`3` が実際に common になる条件の追加 modular subsystem は導入していない。

## 8. L026-6 — five good edges and exceptional edge

次の五つの complete-point coprimality は Lean で成立した。

```text
A/B  consecutive       -- L025
B/C  packet             -- L025
A/C  centered prime gap -- L025
C/D  consecutive        -- L026
B/D  prime gap          -- L026
```

A/D については coprimality の代わりに、A/D support に `2` が共通することを package
した。

該当宣言:
`centeredPacketDiamond_five_edges_and_AD_obstruction`

public API に K4、graph、clique などの名称や抽象化は追加していない。

## 9. L026-7 — full-cover four-seat witness package

`SquareOffsetsFullyCovered (4*k)` を仮定し、既存の

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

を A/B/C/D の各 seat に適用した。次の four-seat package を証明した。

```lean
∃ pA pB pC pD,
  pA ≠ pB ∧
  pA ≠ pC ∧
  pB ≠ pC ∧
  pB ≠ pD ∧
  pC ≠ pD ∧
  pA ∈ squareOffsetPrimeSupport (4*k) (2*k) ∧
  pB ∈ squareOffsetPrimeSupport (4*k) (2*k+1) ∧
  pC ∈ squareOffsetPrimeSupport (4*k) (6*k+1) ∧
  pD ∈ squareOffsetPrimeSupport (4*k) (6*k+2) ∧
  (pA = pD → pA = 2 ∨ pA = 3)
```

五つの inequality は対応する five good edges の support disjointnessから得た。A/D
については `pA ≠ pD` を主張せず、衝突した場合の `{2,3}` classifierだけを付けた。

該当宣言:
`exists_centeredPacketDiamond_four_witnesses_of_fullyCovered`

## 10. Stronger-beam judgment

### 成功したこと

* D の追加により C/D と B/D の complete coprimality が増えた。
* A/D の単純な K4 edge は prime `2` によって実際に失敗する。
* 失敗 edge の common old-prime directions は `{2,3}` に完全局所化できる。
* full cover は四つの witness と五つの forced inequalitiesを与える。

### 得られなかったこと

* A/D の `2` または `3` collisionを full-cover 仮定だけで除去する theorem。
* 四つの pairwise-distinct witnesses。
* `{2,3}` を除いた support が両 A/D seat で nonempty になる theorem。
* 五席以上へ増加する family、strict incidence deficit、unbounded full-cover obstruction。

従って、四席の存在だけから四 distinct witnessesを推論する false step は採用して
いない。今回得られた強化は「四席 package + 一本の有限 exceptional collision edge」
までである。

## 11. Outcome and stop boundary

**Outcome B — PROVED DIAMOND OBSTRUCTION / EXCEPTIONAL COLLISION**。

L026 は、五つの良い edge と A/D の `{2,3}` exceptional collision を Lean で確立
した。これは Outcome C の単なる parity restatement より強いが、Outcome A の direct
four-seat leverage には届かない。

この checkpoint の停止点は次の通り。

* `CenteredPacketDiamond.lean` の L026-1〜L026-7 を保持する。
* A/D collisionを除く追加 frameworkを導入しない。
* 四 distinct witness、増加 family、または contradictionを仮定で補わない。
* PRIM-L027 は自動開始しない。

## 12. Validation

次を実行し、成功した。

```text
lake build DkMath.NumberTheory.Legendre.CenteredPacketDiamond
lake build DkMath.NumberTheory.Legendre
```

対象 module build は 8679 jobs、facade build は 8686 jobs を完了した。`git diff --check`、
trailing whitespace 検査、禁止 placeholder 検査も clean である。全 repository build、
commit、push、CI はこの checkpoint の範囲外であり、実施していない。
