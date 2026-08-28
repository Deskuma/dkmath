# instruction-089 — PRIM-L069 LowCost Capacity Slack Decomposition / Overpayment Frontier

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `9377e1a7d9a8098ab65be6ec13f439c2082c38ec`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L068` は **Outcome A+ — COLLISION PAIR-OVERLAP CANCELLATION / DEPTH-RESIDUAL CAPACITY ELIMINATION COMPLETE** として受理する。

L068 により full-cover 仮定の下で

```text
2 * PairOverlapOutsideDepthCollision
+ 11 * Collision.card
+ 2 * FiveDirection.card
+ 3 * totient(2*n)
<=
3 * IncidenceCount
+ 2 * LowCostResidualCapacity
```

が確定し、RHS から

```text
DepthResidualPairCapacityExcess
HigherSupportResidualExcess
```

は完全に消えた。

現在 RHS に残る唯一の branch-capacity aggregate は

```lean
paritySafeLowCostResidualCapacity
```

である。

しかしこの量は actual LowCost mass ではなく、L063/L064 で導入した三つの upper capacity の和である。

```text
LowCostResidualMass
= NearResidual.card
+ NonCollisionDepth.card
+ ExactFourth.card

LowCostResidualCapacity
= NearFirstPrimeWaveBudget
+ L018PrimeSquareDepthBudget
+ FourthGateDualBase.card
```

既に Lean では各成分について

```text
NearResidual.card <= NearFirstPrimeWaveBudget
NonCollisionDepth.card <= L018PrimeSquareDepthBudget
ExactFourth.card <= FourthGateDualBase.card
```

が証明済みである。

今回の bounded target は、**この三つの upper-bound overpayment を名前付き Nat slack として exact に分解し、L068 frontier が必要とする余裕を Near / Depth / Fourth の三枝へ完全に帰属させること**である。

Near の新しい wave counting、Fourth injectivity、fifth/sixth direction、解析的 estimate、descent、full-cover contradiction、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeLowCostCapacitySlack.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeCollisionPairOverlapCancellation
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L069.1 — three named component slacks

Nat subtraction により、三枝の overpayment を定義する。

```lean
noncomputable def paritySafeNearWaveCapacitySlack (n : ℕ) : ℕ :=
  paritySafeNearFirstPrimeWaveBudget n -
    (paritySafeCanonicalNearResidualTripleIncidences n).card

noncomputable def paritySafeNonCollisionDepthCapacitySlack (n : ℕ) : ℕ :=
  squareAnchorCoprimePrimeSquareDepthBudget n -
    (paritySafeRechargeExactDepthNonCollisionSeats n).card

noncomputable def paritySafeFourthGateCapacitySlack (n : ℕ) : ℕ :=
  (paritySafeFourthGateDualBasePairs n).card -
    (paritySafeRechargeExactFourthDirectionPairs n).card
```

既存 upper bounds を使い、各 branch で exact identity を固定する。

```lean
theorem paritySafeNearFirstPrimeWaveBudget_eq_nearResidual_add_slack
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      paritySafeNearWaveCapacitySlack n := by
  ...

theorem squareAnchorCoprimePrimeSquareDepthBudget_eq_nonCollisionDepth_add_slack
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      paritySafeNonCollisionDepthCapacitySlack n := by
  ...

theorem paritySafeFourthGateDualBase_card_eq_exactFourth_add_slack
    (n : ℕ) :
    (paritySafeFourthGateDualBasePairs n).card =
      (paritySafeRechargeExactFourthDirectionPairs n).card +
      paritySafeFourthGateCapacitySlack n := by
  ...
```

使う upper bounds:

```lean
paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget
paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget
paritySafeRechargeExactFourthDirectionPairs_card_le_fourthGateDualBase
```

`Nat.add_sub_of_le` / `Nat.sub_add_cancel` / `omega` のいずれかでよい。

---

## 3. L069.2 — total LowCost capacity slack

```lean
noncomputable def paritySafeLowCostResidualCapacitySlack (n : ℕ) : ℕ :=
  paritySafeNearWaveCapacitySlack n +
  paritySafeNonCollisionDepthCapacitySlack n +
  paritySafeFourthGateCapacitySlack n
```

必須主定理その1:

```lean
theorem paritySafeLowCostResidualCapacity_eq_mass_add_slack
    (n : ℕ) :
    paritySafeLowCostResidualCapacity n =
      paritySafeLowCostResidualMass n +
      paritySafeLowCostResidualCapacitySlack n := by
  ...
```

これは **exact equality** とする。

proof は三つの branch identity と

```lean
paritySafeLowCostResidualMass
paritySafeLowCostResidualCapacity
```

の定義展開だけで閉じること。

---

## 4. L069.3 — zero slack iff all three upper bounds are tight

まず component zero criteria を public theorem にしてよい。

例:

```lean
theorem paritySafeNearWaveCapacitySlack_eq_zero_iff
    (n : ℕ) :
    paritySafeNearWaveCapacitySlack n = 0 ↔
      paritySafeNearFirstPrimeWaveBudget n =
        (paritySafeCanonicalNearResidualTripleIncidences n).card := by
  ...
```

Depth / Fourth も同様。

必須主定理その2:

```lean
theorem paritySafeLowCostResidualCapacitySlack_eq_zero_iff_all_tight
    (n : ℕ) :
    paritySafeLowCostResidualCapacitySlack n = 0 ↔
      paritySafeNearFirstPrimeWaveBudget n =
          (paritySafeCanonicalNearResidualTripleIncidences n).card ∧
      squareAnchorCoprimePrimeSquareDepthBudget n =
          (paritySafeRechargeExactDepthNonCollisionSeats n).card ∧
      (paritySafeFourthGateDualBasePairs n).card =
          (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

ここで「tight」は equality の意味だけであり、各 branch の injectivity や set equality を新たに主張しない。

---

## 5. L069.4 — L068 frontier rewritten by actual LowCost + explicit slack

L068 の totient frontier

```lean
two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostCapacity
```

へ L069.2 exact identity を rewrite する。

必須:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_add_slack
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n +
        2 * paritySafeLowCostResidualCapacitySlack n := by
  ...
```

これは新しい estimate ではなく **L068 の exact slack normal form** である。

reduced quotient interval rewrite も追加する。

---

## 6. L069.5 — required LowCost slack frontier

full cover が成立するために、actual LowCost mass を超えて最低どれだけ capacity slack が必要かを名前付き quantity として分離する。

候補:

```lean
noncomputable def paritySafeFullCoverRequiredLowCostSlack (n : ℕ) : ℕ :=
  (2 * paritySafePairOverlapOutsideDepthCollision n +
    11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
    2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
    3 * Nat.totient (2 * n)) -
  (3 * paritySafeIncidenceCount n +
    2 * paritySafeLowCostResidualMass n)
```

必須主定理その3:

```lean
theorem paritySafeFullCoverRequiredLowCostSlack_le_two_capacitySlack
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    paritySafeFullCoverRequiredLowCostSlack n ≤
      2 * paritySafeLowCostResidualCapacitySlack n := by
  ...
```

L069.4 と Nat subtraction arithmetic だけで証明する。

この theorem の意味は、full cover を維持するなら、L063/L064 の三つの upper universe の overpayment が合計で required gap の半分以上を供給しなければならない、という有限 necessary condition である。

### no-overpayment corollary

```lean
theorem two_mul_outsideCollisionPairOverlap_add_elevenCollision_add_twoFiveDirection_add_threeTotient_le_fullCoverLowCostMass_of_capacitySlack_eq_zero
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hslack : paritySafeLowCostResidualCapacitySlack n = 0) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      11 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      2 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

これは容易なら追加する。

---

## 7. Optional — structural Near complement only if cheap

L063 には

```lean
paritySafeNearFirstPrimeWaveUpperIncidences
```

が既にあり、actual Near residual は

```text
triple ↦ ((canonicalPrime, pair), seat)
```

としてこの upper incidence Finset に inject されている。

もし engineering が軽ければ、actual image を public Finset として名前付けし、

```text
NearUpperIncidences \ ActualNearWaveImage
```

の card が `paritySafeNearWaveCapacitySlack` に一致することを追加してよい。

ただし **optional**。このために L063 を大きく refactor したり、generic incidence library を作らない。

Depth / Fourth について同様の structural complement を今回要求しない。

---

## 8. False-beam / 境界

今回証明してはいけないもの:

```text
LowCostCapacitySlack = 0          -- 一般には未証明
NearWaveSlack = 0                 -- 未証明
DepthSlack = 0                    -- 未証明
FourthSlack = 0                   -- 未証明
LowCostCapacity <= IncidenceCount -- 根拠なし
LowCostMass <= OutsideCollisionPairOverlap -- 根拠なし
```

特に actual LowCost branches がすべて outside-collision pair-overlap に載るとは仮定しない。
Near residual と Fourth branch は seat sharing の可能性を今回排除していない。

---

## 9. 非目標

- Near product-wave の新評価
- L018 prime-square budget の新評価
- FourthGate injectivity / equality
- fifth-wave / sixth direction
- higher-support recursion
- generic hypergraph
- PNT / Mertens / sieve / harmonic asymptotics
- descent
- full-cover contradiction
- Legendre / RH conclusion

---

## 10. Outcome rubric

### Outcome A+

以下が全部閉じる:

1. three component slack defs
2. three exact branch capacity identities
3. total `LowCostCapacity = LowCostMass + Slack`
4. zero-slack iff all three component bounds tight
5. L068 full-cover frontier の actual-mass + slack normal form
6. required slack `<= 2 * capacitySlack`
7. reduced quotient consumer
8. facade import / report / public docstrings

### Outcome A

1–5 が閉じ、required-slack subtraction normalization のみ engineering minor。

### Outcome E

component identities は閉じるが、巨大式の `omega` / rewrite normalization が blocker。
その場合は exact LowCost capacity decomposition を成果として止め、無理に式を展開しない。

### Outcome C

既存 component inequality の向きが想定と異なる、または `LowCostResidualCapacity` が三 component upper bound の和ではないことが判明した場合。
その事実を report して停止する。

---

## 11. 実装レポート

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-low-cost-capacity-slack-260827.md
```

最低限:

1. Outcome
2. 三 component slack の意味
3. exact total decomposition
4. zero/tight criterion
5. L068 slack normal form
6. required slack theorem
7. 次 checkpoint でどの slack が structural bottleneck かを比較できるようになったこと
8. 非目標

を記録する。
