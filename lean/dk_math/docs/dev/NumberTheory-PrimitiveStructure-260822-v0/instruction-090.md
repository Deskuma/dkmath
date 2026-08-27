# instruction-090 — PRIM-L070 Actual Depth-Fiber Cancellation / Capacity-Free Full-Cover Frontier

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `700b2d553f16b56ee21c27adb9a012b04e655a60`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L069` は **Outcome A+ — LOWCOST CAPACITY SLACK DECOMPOSITION / OVERPAYMENT FRONTIER COMPLETE** として受理する。

L069 により

```text
LowCostResidualCapacity
= LowCostResidualMass
+ NearSlack + DepthSlack + FourthSlack
```

が exact に確定した。

ただし、今回 main route を一段戻して再整理する。

L057 には upper capacity を使う前の exact residual ledger

```text
ResidualPairMass
= Near
+ Terminal
+ DepthSeats
+ DepthFiberExcess
+ Fourth
```

があり、L062 には

```text
DepthSeats = NonCollisionDepth + Collision
LowCostResidualMass = Near + NonCollisionDepth + Fourth
```

がある。

したがって exact に

```text
ResidualPairMass
= LowCostResidualMass
+ Terminal
+ Collision
+ DepthFiberExcess
```

へ戻せる。

さらに L058 では

```text
DepthFiberExcess <= DepthResidualPairCapacityExcess
```

L068 では

```text
CollisionPairOverlapMass
= CollisionSupportCost
+ Collision
+ DepthResidualPairCapacityExcess
```

が確定している。

よって差

```text
CollisionResidualPairSlack
:= DepthResidualPairCapacityExcess - DepthFiberExcess
```

を導入すれば、collision pair-overlap mass 自身を

```text
CollisionPairOverlapMass
= CollisionSupportCost
+ Collision
+ DepthFiberExcess
+ CollisionResidualPairSlack
```

と exact に書ける。

今回の bounded target は、**この actual fiber excess を collision pair-overlap 内部へ exact に回収し、L063/L064 の Near/Depth/Fourth upper capacitiesを一切使わない capacity-free frontier を作ること**である。

Near wave counting、L018 の新 estimate、Fourth injectivity、fifth/sixth direction の追加、descent、full-cover contradiction、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeActualFiberCancellation.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeLowCostCapacitySlack
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L070.1 — exact actual residual normal form

必須:

```lean
theorem paritySafeResidualPairMass_eq_lowCostMass_add_terminal_add_collision_add_depthFiberExcess
    (n : ℕ) :
    paritySafeResidualPairMass n =
      paritySafeLowCostResidualMass n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

推奨 proof spine:

1. `paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth`。
2. `paritySafeRechargeExactDepthSeats_card_eq_nonCollision_add_collision`。
3. `paritySafeLowCostResidualMass` を unfold。
4. `omega` / associativity normalization。

これは **exact equality** とする。

次に pair-overlap level も必要なら public theorem にしてよい:

```lean
theorem paritySafePrimePairOverlapCount_eq_supportExcess_add_lowCostMass_add_terminal_add_collision_add_depthFiberExcess
    (n : ℕ) :
    paritySafePrimePairOverlapCount n =
      paritySafeSupportExcess n +
      paritySafeLowCostResidualMass n +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

使用:

```lean
paritySafePrimePairOverlapCount_eq_supportExcess_add_residual
```

---

## 3. L070.2 — actual fiber charged support frontier

L067 の strengthened support charge

```lean
2 * Terminal.card
+ 3 * Collision.card
+ FiveDirection.card
<= SupportExcess
```

を exact pair-overlap normal form に適用する。

必須:

```lean
theorem two_mul_pairOverlap_add_collision_add_fiveDirection_le_threeSupportExcess_add_twoLowCostMass_add_twoDepthFiberExcess
    (n : ℕ) :
    2 * paritySafePrimePairOverlapCount n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n +
        2 * paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

数学は

```text
P = S + L + T + C + E
2T + 3C + F <= S
--------------------------------
2P + C + F <= 3S + 2L + 2E
```

のみ。

ここでは **LowCostResidualCapacity を絶対に使わない**。

---

## 4. L070.3 — collision residual-pair slack

actual fiber と residual pair upper universe の差を局所名ではなく global finite slack として定義する。

```lean
noncomputable def paritySafeDepthCollisionResidualPairSlack
    (n : ℕ) : ℕ :=
  paritySafeRechargeExactDepthResidualPairCapacityExcess n -
    paritySafeRechargeExactDepthFiberExcess n
```

既存 theorem:

```lean
paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess
```

を使い、exact identity:

```lean
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_collisionResidualPairSlack
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionResidualPairSlack n := by
  ...
```

zero criterion も容易なら public:

```lean
theorem paritySafeDepthCollisionResidualPairSlack_eq_zero_iff (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n = 0 ↔
      paritySafeRechargeExactDepthResidualPairCapacityExcess n =
        paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

これは tightness criterion のみ。slack=0 は主張しない。

---

## 5. L070.4 — collision pair-overlap exact actual-fiber decomposition

L068 の

```lean
paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_depthResidualCapacity
```

と L070.3 を組み、必須 exact theorem:

```lean
theorem paritySafeDepthCollisionPairOverlapMass_eq_supportCost_add_collision_add_fiberExcess_add_residualSlack
    (n : ℕ) :
    paritySafeDepthCollisionPairOverlapMass n =
      paritySafeDepthCollisionLocalSupportCost n +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      paritySafeDepthCollisionResidualPairSlack n := by
  ...
```

意味:

```text
Collision pair mass
= local support cost
+ one occupied collision copy
+ actual multiplicity excess
+ unused residual-pair room
```

ここで `DepthResidualPairCapacityExcess` は theorem conclusion から消える。

---

## 6. L070.5 — actual depth-fiber cancellation

L070.2 と、L068 の exact split

```lean
PairOverlap = OutsideCollisionPairOverlap + CollisionPairOverlapMass
```

および L070.4 を組み合わせる。

必須主定理:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_twoCollisionSupportCost_add_threeCollision_add_fiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      2 * paritySafeDepthCollisionLocalSupportCost n +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

係数を必ず確認すること。

代数は

```text
2P + C + F <= 3S + 2L + 2E
P = Pout + Pcoll
Pcoll = Scoll + C + E + Q
--------------------------------
2Pout + 2Scoll + 3C + F + 2Q
  <= 3S + 2L
```

である。

**ここで `E = DepthFiberExcess` が両辺から exact cancellation する。**

---

## 7. L070.6 — readable capacity-free frontier

L067/L068 の existing charge

```lean
3 * Collision.card + FiveDirection.card
<= paritySafeDepthCollisionLocalSupportCost n
```

を **一度だけ**使う。

L070.5 の `2 * CollisionSupportCost` に doubled charge を入れることで、必須:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

係数:

```text
2*Scoll + 3C + F
>= 2*(3C+F) + 3C + F
 = 9C + 3F
```

である。

この theorem の RHS には以下を出さない:

```text
LowCostResidualCapacity
LowCostResidualCapacitySlack
DepthResidualPairCapacityExcess
DepthFiberExcess
HigherSupportResidualExcess
```

---

## 8. L070.7 — full-cover consumers

full cover exact balance

```text
Candidate.card + SupportExcess = IncidenceCount
```

を使い、candidate form:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoResidualSlack_add_threeCandidate_le_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionResidualPairSlack n +
      3 * (squareAnchorOddPointCoprimeOffsets n).card ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

次に totient form:

```text
3 * Nat.totient (2*n)
```

へ exact rewrite。

さらに reduced quotient interval form:

```text
IncidenceCount
= sum q in squareAnchorOddActivePrimes n,
    (paritySafeReducedQuotientInterval n q).card
```

も追加する。

### A+ の最終 readable target

```text
2*OutsideCollisionPairOverlap
+ 9*Collision
+ 3*FiveDirection
+ 2*CollisionResidualPairSlack
+ 3*totient(2*n)
<=
3*ReducedQuotientIncidenceSum
+ 2*LowCostResidualMass
```

これは **upper capacity-free** である。

---

## 9. optional — relation to L069

安価なら、L069 frontier と L070 frontier が別の valid necessary condition であることを docstring/report に明記する。

- L069: stronger collision coefficient `11C + 2F` だが `+2*LowCostCapacitySlack` を RHS に持つ。
- L070: collision coefficient `9C + 3F + 2Q` で、RHS は actual LowCost mass のみ。

ここから両 frontier の大小比較は **まだ行わない**。`Q` と LowCost slack の間に関係を仮定しない。

---

## 10. Non-goals / 禁止

今回やらない:

- `LowCostResidualCapacitySlack = 0` の証明
- `CollisionResidualPairSlack = 0` の証明
- Near wave の新 counting / injectivity
- L018 depth budget の新 estimate
- FourthGate slack の set-theoretic解析
- fifth/sixth direction の追加
- residual recursion / descent
- asymptotic / analytic sieve
- full-cover contradiction
- Legendre conjecture / RH conclusion
- generic hypergraph / generic binomial-capacity library

特に `LowCostResidualCapacity` を使って L070 main theorem を証明しないこと。

---

## 11. レポート

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-actual-fiber-cancellation-260827.md
```

最低限:

1. exact actual residual normal form
2. collision residual-pair slack の意味
3. collision mass exact decomposition
4. `DepthFiberExcess` cancellation
5. capacity-free readable frontier
6. full-cover / totient / reduced quotient form
7. L069 との役割差
8. formal boundary

---

## 12. Outcome rubric

### Outcome A+

すべて成立:

- exact actual residual normal form
- `CollisionResidualPairSlack` exact identity
- collision pair mass = support + collision + fiber excess + slack
- `DepthFiberExcess` cancellation theorem
- readable `9C + 3F + 2Q` frontier
- full-cover totient/reduced quotient consumer
- final RHS に upper capacity/slack が残らない

### Outcome A

actual-fiber cancellation theorem までは閉じ、full-cover consumer のみ engineering 残り。

### Outcome B

residual normal form / collision slack decomposition まで。

### Outcome E

既存 theorem の elaboration / Nat arithmetic engineering blocker。数学反例とは扱わない。

### Outcome C

上記 exact ledger のどれかに実際の反例・包含破綻がある場合のみ。

---

## STOP

capacity-free full-cover frontier を得たところで止める。

次 checkpoint では初めて、

1. L069 overpayment frontier
2. L070 capacity-free actual-mass frontier

の二つを比較し、どの有限 gap が真の bottleneck かを判定する。
