# instruction-072 — PRIM-L057 Exact Depth Fiber Excess / Paid-vs-Unpaid Ledger

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `5343e4f3eed1016664dc243b650a2e635810ecab`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L056` は **Outcome A — DEPTH SEAT RETURN** として受理する。

L056 までで exact depth branch は

```text
ExactDepth pair
  -> exact shell seat r
  -> some L018 prime-square witness at r
```

へ戻り、distinct seat について

```text
DepthSeats.card <= L018 DepthBudget
```

が閉じた。

一方 pair mass は

```text
ExactDepth.card
  = sum_r DepthPairsAtSeat(r).card
```

という fiber ledger のまま残っている。

今回の bounded target は、この差を **DepthFiberExcess** として exact に分離し、
Depth branch を

```text
L018 が直接支払う seat mass
+
まだ未払いの fiber multiplicity
```

へ書き換えることだけである。

第四方向を fifth direction へ進めない。generic hypergraph / valuation tower も導入しない。

---

## 1. 数学的核

occupied depth seat `r` では fiber は nonempty なので

```text
1 <= (DepthPairsAtSeat n r).card.
```

従って各 seat で

```text
fiber.card = 1 + (fiber.card - 1).
```

これを occupied seats 全体で足せば

```text
ExactDepth.card
  = DepthSeats.card
  + sum_r (fiber.card - 1).
```

右端を

```text
DepthFiberExcess n
```

と定義する。

これにより L056 の global identity

```text
ResidualPairMass
  = Near + Terminal + ExactDepth + Fourth
```

は

```text
ResidualPairMass
  = Near
  + Terminal
  + DepthSeats
  + DepthFiberExcess
  + Fourth
```

へ変わる。

さらに L056 の

```text
DepthSeats.card <= squareAnchorCoprimePrimeSquareDepthBudget n
```

を代入すれば

```text
ResidualPairMass
  <= Near
   + Terminal
   + L018 DepthBudget
   + DepthFiberExcess
   + Fourth
```

となる。

つまり Depth branch で本当に未払いなのは `DepthFiberExcess` だけである。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeDepthFiberExcess.lean
```

import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber
```

完成後 facade `DkMath.NumberTheory.Legendre` へ import を追加する。

---

## 3. L057.1 — occupied fiber nonempty

L056 image 定義から薄い API を公開する。

必須:

```lean
theorem paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).Nonempty := by
  ...
```

推奨 spine:

- `Finset.mem_image.mp hr` から depth pair `bt` を取る。
- `bt` 自身が `DepthPairsAtSeat n r` に属する。

必要なら card positivity も追加してよい。

```lean
theorem paritySafeRechargeExactDepthPairsAtSeat_card_pos_of_mem_depthSeats ...
```

---

## 4. L057.2 — exact fiber excess

定義:

```lean
noncomputable def paritySafeRechargeExactDepthFiberExcess
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthSeats n,
    (paritySafeRechargeExactDepthPairsAtSeat n r).card - 1
```

必須 exact identity:

```lean
theorem paritySafeRechargeExactDepthPairs_card_eq_seats_add_fiberExcess
    (n : ℕ) :
    (paritySafeRechargeExactDepthDualBasePairs n).card =
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

proof spine:

1. L056 `paritySafeRechargeExactDepthPairs_card_eq_sum_seat_fibers`。
2. 各 occupied fiber は nonempty なので card > 0。
3. 各 term で `card = 1 + (card - 1)`。
4. `Finset.card_eq_sum_ones` / `Finset.sum_add_distrib` で分離。

Nat subtraction は fiber ごとに local に置く。global subtraction は導入しない。

---

## 5. L057.3 — collision seats / excess support

fiber multiplicity が本当にどこにあるかを Finset として露出する。

```lean
noncomputable def paritySafeRechargeExactDepthFiberCollisionSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthSeats n).filter
    (fun r => 2 <= (paritySafeRechargeExactDepthPairsAtSeat n r).card)
```

membership theorem を付ける。

必須:

```lean
theorem paritySafeRechargeExactDepthFiberExcess_eq_collision_sum
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n =
      ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card - 1 := by
  ...
```

理由:

- occupied seat の fiber card は少なくとも 1。
- collision でなければ card = 1。
- よって `card - 1 = 0`。

strongly preferred:

```lean
theorem paritySafeRechargeExactDepthFiberExcess_eq_zero_iff
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n = 0 ↔
      ∀ r ∈ paritySafeRechargeExactDepthSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card = 1 := by
  ...
```

または collision seats empty との iff でもよい。

---

## 6. L057.4 — global paid/unpaid residual ledger

L056 の residual identity と L057.2 を合成する。

必須 exact theorem:

```lean
theorem paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

association は Lean が扱いやすい形に調整可。

次に L018 budget を使う。

必須 upper consumer:

```lean
theorem paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n <=
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

これは今回の main capacity surface。

さらに strongly preferred:

```lean
theorem paritySafePrimePairOverlapCount_le_supportExcess_add_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth
    (n : ℕ) :
    paritySafePrimePairOverlapCount n <=
      paritySafeSupportExcess n +
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

L041

```text
PrimePairOverlapCount = SupportExcess + ResidualPairMass
```

を使うだけでよい。

---

## 7. L057.5 — zero-excess consumer

fiber collision が無ければ Depth pair mass 全体が L018 で払えることを公開する。

必須:

```lean
theorem paritySafeRechargeExactDepthPairs_card_le_L018Depth_of_fiberExcess_eq_zero
    {n : ℕ}
    (hzero : paritySafeRechargeExactDepthFiberExcess n = 0) :
    (paritySafeRechargeExactDepthDualBasePairs n).card <=
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  ...
```

proof:

- L057.2 exact identity
- `hzero`
- L056 seat capacity

この theorem は「何を倒せば Depth branch が完全消費されるか」を明示する frontier。

---

## 8. L057.6 — n=58 actual collision closure

L056 の arithmetic beam は product equality だけで止まった。
今回は可能なら actual exact-depth membership まで閉じる。

数学的には次が成立する。

```text
n = 58
pair A = (b,t) = (15,21)
p=3, q=5, s=11

pair B = (b,t) = (21,15)
p=3, q=7, s=11

ExactSeat(58,15,21) = 101
ExactSeat(58,21,15) = 101
```

両方で

```text
OddShellQuotient = 11
p=3 divides t
```

なので actual selected-depth pair である。

strongly preferred theorem:

```lean
theorem paritySafeRechargeExactDepthFiber_collision_witness_58 :
    (15, 21) ∈ paritySafeRechargeExactDepthDualBasePairs 58 ∧
      (21, 15) ∈ paritySafeRechargeExactDepthDualBasePairs 58 ∧
      paritySafeRechargeExactSeat 58 15 21 = 101 ∧
      paritySafeRechargeExactSeat 58 21 15 = 101 ∧
      2 <= (paritySafeRechargeExactDepthPairsAtSeat 58 101).card := by
  ...
```

Lean unfolding が重い場合、最後の card `>=2` だけを別 theorem に分けてよい。

ここは L056 Outcome A の未回収部分を閉じる target でもある。

---

## 9. A+ target — collision forces richer support

実装が自然に閉じる場合のみ、一般 theorem を追加する。

直観:

同じ seat に二つの distinct exact depth pairs があるなら、それぞれ対応する actual far residual triple は同一 canonical first prime `p` を持つ。
二つの pair が異なる以上、残りの `(q,s)` pair も異なる。
従って erased co-support には少なくとも 3 directions、active support 全体には少なくとも 4 directions が必要である。

候補:

```lean
theorem paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    4 <= (paritySafeActiveSupport n r).card := by
  ...
```

この theorem のために大きな reconstruction layer が必要なら **実装しない**。
その場合 report に obstacle を書いて Outcome A とする。

今回これを無理に通すため generic graph/hypergraph API を作ってはならない。

---

## 10. 禁止事項 / 非目標

今回は以下を行わない。

- `DepthFiberExcess = 0` を全 n で主張
- fiber card `<=1`
- `ExactDepth.card <= L018 DepthBudget` を無条件に主張
- collision seat 数だけで fiber excess 全体を払ったことにする
- generic graph / hypergraph
- generic higher-tail hierarchy
- valuation tower
- fourth direction を fifth direction へ展開
- smaller anchor / descent / induction
- analytic sieve / PNT / Mertens / asymptotic density
- terminal / near / fourth の新しい counting estimate
- global contradiction
- Legendre conjecture / RH proof claim

今回の目的は **Depth branch の paid mass と unpaid multiplicity を exact に分離すること**。

---

## 11. Outcome 判定

### Outcome A+ — PAID/UNPAID DEPTH LEDGER + COLLISION SUPPORT

1. occupied fiber nonempty
2. `DepthFiberExcess`
3. `ExactDepth.card = DepthSeats.card + FiberExcess`
4. collision-seat exact sum
5. global residual paid/unpaid identity
6. L018 depth-budget upper consumer
7. zero-excess frontier consumer
8. n=58 actual depth-fiber collision witness
9. collision seat -> active support card >= 4

### Outcome A — PAID/UNPAID DEPTH LEDGER

1–8 を完成。
9 の general collision-support theorem は reconstruction cost が大きければ未実装可。

### Outcome B — EXCESS IDENTITY ONLY

1–4 は閉じるが global ledger transport に API obstacle がある。
obstacle を report して停止。

### Outcome C — FALSE

n=58 actual membership が数学的に false、または occupied fiber decomposition が成立しない concrete counterexample が出た場合。

---

## 12. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

---

## 13. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-depth-fiber-excess-260826.md
```

最低限:

1. Outcome
2. occupied fiber packet
3. DepthFiberExcess definition
4. exact pair = seat + excess identity
5. collision-seat ledger
6. residual paid/unpaid identity
7. L018 upper consumer
8. n=58 actual collision result
9. collision-support theorem の成否
10. non-goals / validation

---

## STOP

今回の終了地点は次。

```text
ExactDepth.card
  = DepthSeats.card
  + DepthFiberExcess

DepthSeats.card <= L018 DepthBudget

ResidualPairMass
  <= Near
   + Terminal
   + L018 DepthBudget
   + DepthFiberExcess
   + Fourth
```

ここで停止する。

次 checkpoint で初めて、

```text
DepthFiberExcess を residual-support combinatorics で削る
or
ExactFourth を canonical fourth-direction capacity へ送る
```

を、実装結果に基づいて比較する。