# instruction-085 — PRIM-L065 Full-Cover Capacity Frontier / High-Support Bottleneck Isolation

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `e956929de03e617cf85282eddb275693fb41ba4f`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L064` は **Outcome A+ — FOURTH GATED DUAL-BASE CAPACITY COMPLETE** として受理する。

現在、低コスト三枝はすべて finite upper-control を持つ。

```text
LowCostResidual
  = Near + NonCollisionDepth + Fourth

Near.card
  <= NearFirstPrimeWaveBudget

NonCollisionDepth.card
  <= L018 prime-square depth budget

Fourth.card
  <= FourthGateDualBase.card

LowCostResidual
  <= LowCostResidualCapacity
```

一方、L058 には既に

```text
ResidualPairMass
  <= Near
   + Terminal
   + L018DepthBudget
   + DepthResidualPairCapacityExcess
   + Fourth
```

がある。

L060V では

```text
2 * Terminal.card + 3 * CollisionSeats.card
  <= SupportExcess
```

も確定している。

今回の bounded target は、これらを合成して **pair-overlap 全体の controlled upper frontier を作り、full cover の下で `SupportExcess` を `IncidenceCount - Candidate.card` 相当の exact balance へ消去すること**だけである。

新しい branch counting、第五方向、DepthResidualCapacity の新上界、Near の解析評価、descent、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean
```

import は少なくとも

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFourthDualBaseCapacity
import DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
```

を使ってよい。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L065.1 — residual pair mass を LowCost capacity へ圧縮

既存 L058 theorem:

```lean
paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthResidualCapacity_add_fourth
```

L063/L064:

```lean
paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget
paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase
paritySafeLowCostResidualCapacity
```

を使い、次を閉じる。

```lean
theorem paritySafeResidualPairMass_le_lowCostCapacity_add_terminal_add_depthResidualCapacity
    (n : ℕ) :
    paritySafeResidualPairMass n ≤
      paritySafeLowCostResidualCapacity n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

`paritySafeLowCostResidualCapacity` を unfold して `omega` で合成してよい。

ここでは `Terminal` を LowCost に入れない。

---

## 3. L065.2 — support charge を保った doubled pair-overlap upper frontier

既存 exact identity:

```lean
paritySafePrimePairOverlapCount_eq_supportExcess_add_residual
```

L060V:

```lean
two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
```

L065.1 を合成する。

必須 target:

```lean
theorem two_mul_pairOverlap_add_threeCollision_le_threeSupportExcess_add_twoLowCostCapacity_add_twoDepthResidualCapacity
    (n : ℕ) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

数学は単純である。

```text
P = S + R
R <= L + T + D
2*T + 3*C <= S
```

より

```text
2*P + 3*C
<= 3*S + 2*L + 2*D.
```

Nat subtraction は不要。`omega` でよい。

### 禁止

`3*C` を捨ててから証明を始めない。

collision charge を残した theorem を primary API にする。

必要なら consumer として

```lean
2 * PairOverlap <= 3 * SupportExcess + 2 * LowCostCapacity + 2 * DepthResidualCapacity
```

を追加してよいが、primary ではない。

---

## 4. L065.3 — full cover で parity-safe uncovered candidate は空

既存:

```lean
mem_paritySafeUncoveredCandidates_iff
paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card
paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence
```

を使う。

必須:

```lean
theorem paritySafeUncoveredCandidates_eq_empty_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    paritySafeUncoveredCandidates n = ∅ := by
  ...
```

`hr : r ∈ paritySafeUncoveredCandidates n` なら

```text
r is parity-safe candidate
¬ SquareOffsetCovered n r
```

だが、candidate membership から `SquareOffset n r` を取り、`hfull` と矛盾させればよい。

次に exact card balance:

```lean
theorem paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (squareAnchorOddPointCoprimeOffsets n).card +
      paritySafeSupportExcess n =
        paritySafeIncidenceCount n := by
  ...
```

推奨:

1. `paritySafeUncoveredCandidates_eq_empty_of_fullyCovered`。
2. `paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card` から covered card = candidate card。
3. `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence`。
4. `omega`。

グローバル Nat subtraction は定義しない。

---

## 5. L065.4 — full-cover necessary capacity frontier

L065.2 と L065.3 を合成し、`SupportExcess` を theorem statement から消す。

必須:

```lean
theorem two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

理由:

```text
Candidate + SupportExcess = IncidenceCount
```

なので

```text
3*SupportExcess + 3*Candidate = 3*IncidenceCount.
```

L065.2 の両辺へ `3*Candidate` を足すだけでよい。

---

## 6. L065.5 — totient(2*n) 形式

L037:

```lean
card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul
```

を使い、candidate card を exact に `Nat.totient (2*n)` へ置換する。

必須:

```lean
theorem two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

これは L065.4 の readable arithmetic form である。

---

## 7. L065.6 — reduced quotient interval 形式

L037:

```lean
paritySafeIncidenceCount_eq_reducedQuotientInterval_sum
```

を使い、RHS の incidence count を finite quotient-interval sum へ rewrite する consumer を追加する。

推奨 target:

```lean
theorem two_mul_pairOverlap_add_threeCollision_add_threeTotient_le_reducedQuotient_fullCoverCapacity
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n +
        2 * paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

これは新しい estimate ではなく exact rewrite consumer である。

---

## 8. この checkpoint の意味

L065 が閉じると full cover の下で

```text
PairOverlap
Candidate/totient
Collision charge
```

の必要量が、

```text
IncidenceCount / reduced quotient intervals
LowCostResidualCapacity
DepthResidualPairCapacityExcess
```

だけで支配される形になる。

`SupportExcess` と raw `Terminal` は theorem statement から消える。

この時点で、構造 branch として未精錬の主要項は

```text
DepthResidualPairCapacityExcess
```

である。

ただし `NearFirstPrimeWaveBudget`、L018 depth budget、FourthGateDualBase、reduced quotient intervals は finite capacity であって、まだ数値的・漸近的に十分小さいとは証明していない。

**「L065 が閉じたから contradiction が近い」とは書かない。**

---

## 9. STOP

今回は以下へ進まない。

- `DepthResidualPairCapacityExcess` の新上界
- fifth direction
- generic 5-hypergraph
- `Nat.minFac` injectivity
- Near harmonic/asymptotic evaluation
- prime-counting estimate
- descent
- full-cover contradiction
- Legendre's conjecture
- RH

---

## 10. Outcome

### Outcome A+

以下すべて成立:

1. residual upper compression。
2. collision credit を保持した doubled pair-overlap upper frontier。
3. full-cover uncovered=empty。
4. `Candidate.card + SupportExcess = IncidenceCount`。
5. full-cover support-free frontier。
6. `totient(2*n)` form。
7. reduced quotient interval form。

### Outcome A

1--5 は閉じ、6 または 7 が単なる rewrite/elaboration 上の問題で未完。

### Outcome E

full-cover candidate/support balance または L065.2 の algebra composition に engineering blocker。数学的 counterexample がない限り STOP して report。

### Outcome C

既存 accepted theorem 群から上記 frontier のいずれかが数学的に導けない concrete reason / counterexample を確認。

---

## 11. report

推奨:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-full-cover-capacity-frontier-260827.md
```

必須記録:

- Outcome。
- 実装 theorem 一覧。
- `2*P + 3*C <= 3*S + 2*L + 2*D` の algebra spine。
- full cover で uncovered candidate が消える proof spine。
- candidate/support/incidence exact balance。
- totient / reduced quotient rewrite。
- remaining raw structural term が `DepthResidualPairCapacityExcess` であること。
- finite capacity と numerical/asymptotic smallness を混同していないこと。
- STOP 範囲を越えていないこと。
