# instruction-082 — PRIM-L062 Low-Cost Residual Split / Explicit Collision Weight Five

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `e3eebd2a6ae09397366e79e9aa95bd5ab2833280`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L061` は **Outcome A+ — CHARGED RESIDUAL NORMAL FORM / WEIGHTED PAIR-OVERLAP FRONTIER** として受理する。

現在 Lean で次が確定している。

```text
Near
+ 3 * Terminal
+ DepthSeats
+ 4 * CollisionSeats
+ Fourth
<= PrimePairOverlap
<= CoprimePrimePairOverlapCapacity
```

ここで `CollisionSeats ⊆ DepthSeats` は定義上成立しており、`DepthSeats` の一単位の中に collision seat 自身の base cost が既に含まれている。

今回の bounded target は **DepthSeats を collision / noncollision に exact split し、collision の実効 weight 5 を theorem statement 上に露出すること**だけである。

Near の新 counting、Fourth の injective counting、新しい descent には進まない。

---

## 1. 数学的核

記号:

```text
N := Near.card
T := TerminalKeys.card
D := DepthSeats.card
C := CollisionSeats.card
F := Fourth.card
```

L061:

```text
N + 3*T + D + 4*C + F <= PairOverlap.
```

`CollisionSeats ⊆ DepthSeats` なので

```text
DepthSeats = NonCollisionDepthSeats ⊔ CollisionSeats
```

と exact に分割できる。

従って

```text
D = NC + C
```

を代入すると

```text
N + 3*T + NC + 5*C + F <= PairOverlap.
```

これが今回の main frontier。

さらに

```text
LowCostResidual := N + NC + F
```

という readable な Nat quantity を定義してよい。

すると

```text
LowCostResidual + 3*T + 5*C <= PairOverlap
```

および coprime pair capacity への transport を得る。

---

## 2. 新規 module

推奨:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeLowCostResidualSplit.lean
```

import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger
```

facade `DkMath.NumberTheory.Legendre` に import を追加する。

既存 module の large rewrite は行わない。

---

## 3. L062.1 — noncollision depth seats

定義:

```lean
noncomputable def paritySafeRechargeExactDepthNonCollisionSeats
    (n : ℕ) : Finset ℕ :=
  paritySafeRechargeExactDepthSeats n \
    paritySafeRechargeExactDepthFiberCollisionSeats n
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeRechargeExactDepthNonCollisionSeats
    {n r : ℕ} :
    r ∈ paritySafeRechargeExactDepthNonCollisionSeats n ↔
      r ∈ paritySafeRechargeExactDepthSeats n ∧
      r ∉ paritySafeRechargeExactDepthFiberCollisionSeats n := by
  ...
```

必須 subset:

```lean
theorem paritySafeRechargeExactDepthFiberCollisionSeats_subset_depthSeats
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
      paritySafeRechargeExactDepthSeats n := by
  ...
```

これは `mem_paritySafeRechargeExactDepthFiberCollisionSeats` の第一成分だけで閉じる。

---

## 4. L062.2 — exact disjoint partition

必須:

```lean
theorem paritySafeRechargeExactDepthNonCollision_collision_disjoint
    (n : ℕ) :
    Disjoint
      (paritySafeRechargeExactDepthNonCollisionSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  ...
```

```lean
theorem paritySafeRechargeExactDepthNonCollision_collision_union
    (n : ℕ) :
    paritySafeRechargeExactDepthNonCollisionSeats n ∪
        paritySafeRechargeExactDepthFiberCollisionSeats n =
      paritySafeRechargeExactDepthSeats n := by
  ...
```

必須 card split:

```lean
theorem paritySafeRechargeExactDepthSeats_card_eq_nonCollision_add_collision
    (n : ℕ) :
    (paritySafeRechargeExactDepthSeats n).card =
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
  ...
```

`Finset.card_union_of_disjoint` を使う。

Nat subtraction による card formula は public API に出さない。

---

## 5. L062.3 — noncollision fiber is exactly singleton

この branch の意味を theorem として固定する。

必須:

```lean
theorem paritySafeRechargeExactDepthPairsAtSeat_card_eq_one_of_mem_nonCollision
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthNonCollisionSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).card = 1 := by
  ...
```

proof spine:

- noncollision membership から `r ∈ DepthSeats`。
- L057 `...card_pos_of_mem_depthSeats` で `0 < fiber.card`。
- collision でないことから `¬ 2 ≤ fiber.card`。
- `omega`。

この theorem は新 counting ではなく branch semantics の固定。

---

## 6. L062.4 — noncollision depth remains inside L018 budget

既存

```lean
paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget
```

から subset/card で consumer を追加する。

必須:

```lean
theorem paritySafeRechargeExactDepthNonCollisionSeats_card_le_primeSquareDepthBudget
    (n : ℕ) :
    (paritySafeRechargeExactDepthNonCollisionSeats n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  ...
```

これは upper-control surface の再掲であり、L061/L062 lower frontier の左辺に DepthBudget を代入してはならない。

---

## 7. L062.5 — explicit collision weight five frontier

L061 theorem

```lean
paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount
```

と card split を組み合わせる。

必須 main theorem:

```lean
theorem paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthNonCollisionSeats n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card ≤
        paritySafePrimePairOverlapCount n := by
  ...
```

proof は card split rewrite + `omega` で閉じることを優先する。

次に capacity transport:

```lean
theorem paritySafeNear_add_threeTerminal_add_nonCollisionDepth_add_fiveCollision_add_fourth_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    ... ≤ squareAnchorCoprimePrimePairOverlapCount n := by
  exact (...).trans
    (paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount n)
```

---

## 8. L062.6 — readable low-cost residual quantity

推奨定義:

```lean
noncomputable def paritySafeLowCostResidualMass (n : ℕ) : ℕ :=
  (paritySafeCanonicalNearResidualTripleIncidences n).card +
  (paritySafeRechargeExactDepthNonCollisionSeats n).card +
  (paritySafeRechargeExactFourthDirectionPairs n).card
```

必須 theorem:

```lean
theorem paritySafeLowCostResidualMass_add_threeTerminal_add_fiveCollision_le_pairOverlap
    (n : ℕ) :
    paritySafeLowCostResidualMass n +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      5 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafePrimePairOverlapCount n := by
  ...
```

および capacity version。

加法順序は theorem proof を軽くする形でよい。statement は readable を優先する。

---

## 9. selector interpretation

この checkpoint が閉じた時点で Lean 上の branch 状態は次になる。

```text
High-cost / already charged:
  Terminal       weight >= 3
  CollisionDepth weight >= 5

Low-cost residual:
  Near
  NonCollisionDepth
  Fourth
```

さらに既存 API の強さは:

```text
NonCollisionDepth:
  singleton depth fiber
  card <= L018 prime-square depth budget

Fourth:
  canonical fourth-prime packet
  first prime enters FourDirectionGate
  but no global injective count

Near:
  exact near/far partition only
  no independent upper capacity yet
```

このため **次 checkpoint の第一候補は Near branch** とする。

ただし L062 自体では Near counting を始めない。

---

## 10. heartbeat / engineering policy

- global `set_option maxHeartbeats 0` 禁止。
- large `simp` で residual/depth 定義を全 unfold しない。
- split は `Finset.sdiff`, subset, disjoint, union, card theorem で処理する。
- L061 main theorem を再証明しない。consumer として rewrite する。
- timeout した場合は最小 failing theorem を report する。

---

## 11. Non-goals

今回やらない:

- Near product-wave の新 counting
- Fourth key/prime の injectivity
- ExactFourth の追加方向
- fifth direction
- residual recursion
- generic hypergraph
- analytic sieve / PNT / Mertens
- descent / induction
- global contradiction
- Legendre / RH claim

---

## 12. Outcome rubric

### Outcome A+ — LOW-COST RESIDUAL SPLIT COMPLETE

以下すべて:

1. noncollision depth seats 定義
2. collision subset depth seats
3. exact disjoint union
4. depth card = noncollision + collision
5. noncollision fiber card = 1
6. noncollision card <= L018 depth budget
7. explicit weight-5 pair-overlap frontier
8. coprime capacity transport
9. low-cost residual quantity
10. low-cost residual weighted frontier
11. facade import / docs / report

### Outcome A — WEIGHT-FIVE FRONTIER COMPLETE

1–8 が閉じる。low-cost quantity は未完でも可。

### Outcome B — EXACT DEPTH SPLIT COMPLETE

1–5 が閉じるが weighted frontier 未完。

### Outcome C — FALSE

具体的 counterexample により上記 structural statement のどれかが偽。

### Outcome E — ENGINEERING BLOCK

数学的反例なしで bounded theorem が heartbeat/elaboration obstruction。最小 failing theorem を報告。

---

## 13. STOP

以下で停止する。

```text
DepthSeats
  = NonCollisionDepthSeats ⊔ CollisionSeats

NonCollisionDepth fiber.card = 1
CollisionDepth effective weight >= 5

LowCostResidual
  = Near + NonCollisionDepth + Fourth

LowCostResidual
+ 3*Terminal
+ 5*Collision
<= PairOverlap
<= CoprimePairCapacity
```

**ここから Near counting へは進めない。**
