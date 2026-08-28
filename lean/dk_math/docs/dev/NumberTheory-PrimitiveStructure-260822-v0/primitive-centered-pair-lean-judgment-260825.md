# PRIM-L024 — Centered-Pair Common-Support Lean Judgment

日付: 2026-08-25
対象 branch: `wip/number-theory-primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 作業境界

instruction-039 に従い、`n-j` と `n+1+j` の centered pair を Lean で定式化し、
既存の square-shell full-cover API まで接続した。変更対象は次の二つである。

* `DkMath/NumberTheory/Legendre/CenteredPair.lean`
* `DkMath/NumberTheory/Legendre.lean` の public facade import

既存の Legendre theorem や packet / wave 定義は移動・変更していない。Legendre の
証明、未知の consumer theorem、追加の仮定は導入していない。今回の対象外である
PRIM-L025 も開始していない。

## 1. Executive outcome

**Outcome B — PROVED STRUCTURAL REFINEMENT** と判定する。

Lean は次を完全に証明した。

1. `j < n` なら `n-j` と `n+1+j` はともに `SquareOffset n` に属する。
2. 対応する square points の差は正確に `2*j+1` である。
3. 両方の point を割る任意の q は、左 point を割ることに加えて `2*j+1` を割る。
4. その事実は `squareOffsetPrimeSupport` の共通 support characterization にできる。
5. `2*j+1` が prime で `n < 2*j+1` なら、二つの old-prime support Finset は disjoint。
6. `SquareOffsetsFullyCovered n` の下では、二つの centered seats は distinct な
   old-prime support witness を持つ。

これは static packet pairing `r` と `n+r` とは異なる、odd-gap による exact support
制約である。一方、現状の full-cover consumer は distinct witness の再構成に留まり、
packet/wave ledger を超える三席・四席条件、strict count deficit、または Legendre
conjecture の矛盾は Lean から得られなかった。

## 2. 実装した public API

新規 module `DkMath.NumberTheory.Legendre.CenteredPair` に、次を追加した。

| 宣言 | 内容 |
| --- | --- |
| `centeredLeftOffset` | `n - j` |
| `centeredRightOffset` | `n + 1 + j` |
| `squareOffset_centeredLeftOffset` | `j < n` から左 offset の shell membership |
| `squareOffset_centeredRightOffset` | `j < n` から右 offset の shell membership |
| `centeredPoint_difference` | 右 point = 左 point + `2*j+1` |
| `centeredCommonDivisor_iff` | common divisibility と gap divisibility の同値 |
| `mem_common_squareOffsetPrimeSupport_iff` | common old-prime support の exact characterization |
| `disjoint_squareOffsetPrimeSupport_centeredPair` | prime gap が anchor より大きい場合の disjointness |
| `exists_distinct_centeredPair_primeSupport_of_fullyCovered` | full-cover 下の distinct witness |

module docstring には、finite arithmetic と full-cover witness までが形式化境界であり、
contradiction や Legendre conjecture の証明ではないことを明記した。各 public declaration
にも役割を示す短い Lean docstring を付けた。

## 3. L024-1 — centered offsets are in the shell

`j < n` のみを仮定して、自然数減算を整数へ移さずに `omega` で次を証明した。

```lean
SquareOffset n (centeredLeftOffset n j)
SquareOffset n (centeredRightOffset n j)
```

右側については `j < n` から `n+1+j ≤ 2*n` が得られ、左側については
`1 ≤ n-j` と `n-j ≤ 2*n` が得られる。したがって両 offset は同一 shell 内にある。

該当宣言:

* `squareOffset_centeredLeftOffset`
* `squareOffset_centeredRightOffset`

## 4. L024-2 — exact centered point difference

自然数上で直接、次を証明した。

```lean
n^2 + centeredRightOffset n j
  = (n^2 + centeredLeftOffset n j) + (2*j+1)
```

`centeredLeftOffset` の減算は `j < n` によって安全に処理され、`omega` が
`n-j+2*j+1 = n+1+j` を確認する。別の整数 subtraction API や modular wave theory
は導入していない。

該当宣言: `centeredPoint_difference`

## 5. L024-3 — common-divisor reduction

任意の自然数 q について、次の同値を証明した。

```lean
q ∣ n^2 + centeredLeftOffset n j ∧
q ∣ n^2 + centeredRightOffset n j
  ↔
q ∣ n^2 + centeredLeftOffset n j ∧ q ∣ 2*j+1
```

証明は L024-2 の point equality と `Nat.dvd_add_iff_right` のみを使う。q の正値性、
prime 性、coprimality はこの arithmetic lemma には不要である。

該当宣言: `centeredCommonDivisor_iff`

この定理は「共通 prime divisor は odd gap を割る」という数学的内容を、既存の
forbidden-residue wave を再構築せずに表している。

## 6. L024-4 — old-prime common-support characterization

既存の simp theorem `mem_squareOffsetPrimeSupport` と L024-3 を組み合わせ、次を
証明した。

```lean
q ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
q ∈ squareOffsetPrimeSupport n (centeredRightOffset n j)
  ↔
Nat.Prime q ∧ q ≤ n ∧
q ∣ n^2 + centeredLeftOffset n j ∧ q ∣ 2*j+1
```

ここで support の定義が保持する `Nat.Prime q` と `q ≤ n` を明示的に残している。
従って、この定理は arbitrary divisor の gcd statement ではなく、Legendre の actual
old-prime support に対する exact API である。

該当宣言: `mem_common_squareOffsetPrimeSupport_iff`

## 7. L024-5 — prime-gap disjointness

さらに

```lean
Nat.Prime (2*j+1)
n < 2*j+1
```

を仮定した。共通 support の q が存在すると L024-4 により `q ∣ 2*j+1` となる。
prime の divisor theorem `Nat.dvd_prime` と q の prime 性から `q = 2*j+1`。しかし
support membership は `q ≤ n` も与えるため、`n < 2*j+1` と矛盾する。よって

```lean
Disjoint
  (squareOffsetPrimeSupport n (centeredLeftOffset n j))
  (squareOffsetPrimeSupport n (centeredRightOffset n j))
```

を証明した。

該当宣言: `disjoint_squareOffsetPrimeSupport_centeredPair`

これは単なる cardinality equality ではなく、actual old-prime support の disjointness
である。ただし prime-gap 仮定が必要であり、すべての `j` に一様に適用できる定理では
ない。

## 8. L024-6 — full-cover consumer

`SquareOffsetsFullyCovered n` を仮定し、L024-1 で得た二つの shell membership へ
既存の

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

を適用した。各 seat の support が nonempty であることと、L024-5 の disjointness
を組み合わせ、次を証明した。

```lean
∃ p q,
  p ≠ q ∧
  p ∈ squareOffsetPrimeSupport n (centeredLeftOffset n j) ∧
  q ∈ squareOffsetPrimeSupport n (centeredRightOffset n j)
```

該当宣言: `exists_distinct_centeredPair_primeSupport_of_fullyCovered`

これは要求された actual full-cover consumer である。coverage semantics の再証明は
行わず、既存の support nonemptiness API を利用した。

## 9. True beam / insufficient beam

### True beam

Lean で証明済みの新しい構造は次の通りである。

* centered pair は実際の同一 shell の二 seat である。
* 二点の共通 old-prime support は odd gap の prime divisor に制限される。
* gap が prime で anchor より大きい場合、二つの support は disjoint である。
* full cover の下で、対応する二 seat には distinct old-prime witnesses が存在する。

### Insufficient beam

次の stronger consumer は実装していない。現行 API からはその premise が足りない
ためである。

1. `PacketCoprimality` の `r` と `n+r` の pairing と centered pairing を組み合わせた
   three-seat / four-seat witness theorem。
2. 全ての centered pair を summation した、新しい strict incidence inequality。
3. prime-gap pair の disjointness から、full-cover の不可能性を導く theorem。
4. centered pair の witness から、より小さい fully-covered shell を再構成する descent。

特に L024-6 の二 distinct witnessesは、既存 packet layer の「同じ pair の両 seat を
同一 nondivisor prime が cover できない」という制約と同じ witness cardinality の
形を持つ。centered pair では gap が新しい制御量だが、現状は pair ごとの局所条件に
留まり、全 pair の重なりを数える consumer がない。

これは false theorem として符号化したのではなく、証明済み core の後で止めた
semantic boundary である。

## 10. Existing API との差分

| 観点 | 既存 packet pairing | 今回の centered pairing |
| --- | --- | --- |
| offsets | `r`, `n+r` | `n-j`, `n+1+j` |
| point gap | `n` | `2*j+1` |
| support restriction | anchor nondivisor prime は同時に割れない | 共通 prime は odd gap を割る |
| global condition | `Nat.Coprime n r` と packet geometry | `j<n` と prime gap `2*j+1>n` |
| full-cover consumer | distinct nondivisor witnesses | distinct old-prime witnesses |
| current leverage | finite packet incidence ledger | 新しい局所 disjointness、追加 deficit は未取得 |

したがって centered theorem は C（完全な重複）ではなく、proof-backed structural
refinement である。しかし A（direct full-cover leverage）に必要な stronger inequality
や contradiction はまだない。

## 11. Validation

次を実行し、成功した。

```text
lake build DkMath.NumberTheory.Legendre.CenteredPair
lake build DkMath.NumberTheory.Legendre
```

対象 module build は 8677 jobs、facade build は 8684 jobs を完了した。`git diff --check`
も clean である。全 repository build、commit、push、CI はこの checkpoint の範囲外で
あり、実施していない。

## 12. Final recommendation

**Outcome B — PROVED STRUCTURAL REFINEMENT**。

`CenteredPair.lean` と facade import は保持する価値がある。odd-gap common-support
theorem は exact で再利用可能なためである。ただし現時点での推奨は、これ以上の
full-cover consumer を仮定で補わず、PRIM-L024 をここで close すること。次の checkpoint
は、今回の proved theorem を入力に、全 centered pair の incidence を実際に数える
独立した Lean target が明確になった場合にのみ開始する。

PRIM-L025 は開始していない。
