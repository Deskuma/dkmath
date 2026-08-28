# instruction-086 — PRIM-L066 Depth Residual Baseline / Fifth-Direction Trigger Isolation

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `6b41210863e6e96f4f53e33d0feb23061f36703b`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L065` は **Outcome A+ — FULL-COVER CAPACITY FRONTIER COMPLETE** として受理する。

現在 full-cover 仮定の下で、

```text
2*PairOverlap
+ 3*Collision
+ 3*totient(2*n)
<=
3*IncidenceCount
+ 2*LowCostResidualCapacity
+ 2*DepthResidualPairCapacityExcess
```

および reduced quotient interval 形式まで Lean で確定している。

現在唯一 raw structural term として残っているのは

```lean
paritySafeRechargeExactDepthResidualPairCapacityExcess
```

である。

ただし、この term をそのまま「第五方向 residual」と解釈してはならない。

L058 の定義は collision seat ごとに

```text
choose(support.card - 1, 2) - 1
```

を足している。collision seat では既に

```text
4 <= support.card
```

なので、最小の四方向状態 `support.card = 4` でも

```text
choose(3,2) - 1 = 2
```

が残る。

したがって今回の bounded target は、**DepthResidualPairCapacityExcess を「四方向 collision だけでも必要な baseline 2/seat」と「support.card >= 5 で初めて現れる higher-support excess」に exact 分解し、第五方向が必要になる条件を Lean 上で分離すること**である。

fifth-direction descent、新しい residual recursion、Near/Fourth の追加評価、解析的 sieve、Legendre contradiction には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeDepthResidualFifthTrigger.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L066.1 — collision local residual capacity has baseline two

まず局所 combinatorial fact を public helper として固定する。

候補:

```lean
theorem paritySafeDepthResidualLocalCapacity_ge_two_of_collision
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    2 ≤ Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1 := by
  ...
```

使用してよい既存 theorem:

```lean
paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
```

数学的には `k := support.card`, `4 <= k` から

```text
3 <= choose(k-1,2)
```

を示せばよい。

Mathlib の choose monotonicityが素直なら使ってよい。elaboration が重い場合は、この module 内だけの小さな combinatorial helper を induction / `Nat.choose_succ_succ` で証明してよい。

**このために generic binomial library を新設しない。**

---

## 3. L066.2 — higher-support residual excess

四方向 baseline 2 を除いた residual を定義する。

```lean
noncomputable def paritySafeRechargeExactDepthHigherSupportResidualExcess
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3)
```

local identity:

```lean
theorem paritySafeDepthResidualLocalCapacity_eq_two_add_higher
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1 =
      2 +
        (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3) := by
  ...
```

`L066.1` の lower bound を使い、Nat subtraction の truncation に注意する。

---

## 4. L066.3 — exact global baseline decomposition

必須主定理その1:

```lean
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_twoCollision_add_higherSupport
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      2 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  ...
```

推奨 proof architecture:

1. `paritySafeRechargeExactDepthResidualPairCapacityExcess` を unfold。
2. 各 collision seat で L066.2 local identity。
3. `Finset.sum_add_distrib`。
4. constant `2` sum を `2 * card` に normalize。

この theorem は **exact equality** とする。

---

## 5. L066.4 — genuine five-direction collision seats

support が 5 以上の collision seat を明示する。

```lean
noncomputable def paritySafeRechargeExactDepthFiveDirectionCollisionSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthFiberCollisionSeats n).filter
    (fun r => 5 ≤ (paritySafeActiveSupport n r).card)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats
    {n r : ℕ} :
    r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ↔
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      5 ≤ (paritySafeActiveSupport n r).card := by
  ...
```

subset collision:

```lean
theorem paritySafeRechargeExactDepthFiveDirectionCollisionSeats_subset_collision
    (n : ℕ) :
    paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ⊆
      paritySafeRechargeExactDepthFiberCollisionSeats n := by
  ...
```

---

## 6. L066.5 — local higher excess vanishes exactly at support four

collision seat 上で、higher term の意味を固定する。

必須:

```lean
theorem paritySafeDepthHigherResidual_eq_zero_iff_support_card_eq_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3 = 0 ↔
      (paritySafeActiveSupport n r).card = 4 := by
  ...
```

同値に、positive form も可:

```lean
theorem paritySafeDepthHigherResidual_pos_iff_support_card_ge_five
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    0 < Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3 ↔
      5 ≤ (paritySafeActiveSupport n r).card := by
  ...
```

少なくともどちらか一方を public theorem とし、もう一方は容易なら corollary にする。

ここでも generic asymptotic/binomial API は不要。

---

## 7. L066.6 — higher-support residual is supported exactly on five-direction seats

推奨:

```lean
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_fiveDirection_sum
    (n : ℕ) :
    paritySafeRechargeExactDepthHigherSupportResidualExcess n =
      ∑ r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n,
        (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 3) := by
  ...
```

必要なら `Finset.sum_subset` または collision Finset の filter partition を使う。

さらに global zero criterion を閉じる。

```lean
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision
    (n : ℕ) :
    paritySafeRechargeExactDepthHigherSupportResidualExcess n = 0 ↔
      paritySafeRechargeExactDepthFiveDirectionCollisionSeats n = ∅ := by
  ...
```

または RHS を `.card = 0` / `¬ Nonempty` としてもよい。

**これが今回の fifth-direction trigger 判定 theorem である。**

---

## 8. L066.7 — optional structural fifth-prime packet

これは Outcome A+ の bonus。主 ledger が先。

既存 L059:

```lean
paritySafeRechargeDepthFiberCollision_fourDirection_packet
```

は collision seat から canonical `p` と distinct `q,s,u` を与える。

five-direction collision seat では support.card >= 5 なので、さらに

```lean
∃ v,
  v ∈ paritySafeActiveSupport n r ∧
  v ≠ p ∧ v ≠ q ∧ v ≠ s ∧ v ≠ u
```

を取れる。

余裕があれば public theorem:

```lean
theorem paritySafeRechargeExactDepthFiveDirectionCollision_fifthPrime_packet ...
```

として、少なくとも fifth active direction の存在まで固定する。

`p*q*s*u*v ∣ n^2+r` までの五素数積 divisibility は **optional**。そこを証明するために proof が膨らむなら今回は止める。

---

## 9. L066.8 — sharpen L065 frontier

L066.3 の exact identity を L065 frontier に代入する。

L065:

```text
2*PairOverlap + 3*Collision + 3*totient(2*n)
<=
3*IncidenceCount + 2*LowCostCapacity + 2*DepthResidualCapacity
```

と

```text
DepthResidualCapacity = 2*Collision + HigherSupportResidual
```

から `omega` で 3*Collision を両側から消し、次を得る。

必須主定理その2:

```lean
theorem two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  ...
```

reduced quotient interval consumer も作る。

```lean
theorem two_mul_pairOverlap_add_threeTotient_le_reducedQuotient_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  ...
```

---

## 10. L066.9 — no-fifth-direction corollary

five-direction collision が無ければ HigherSupportResidual は 0 になる。

必須:

```lean
theorem two_mul_pairOverlap_add_threeTotient_le_fullCoverCapacity_add_collision_of_no_fiveDirectionCollision
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hfive : paritySafeRechargeExactDepthFiveDirectionCollisionSeats n = ∅) :
    2 * paritySafePrimePairOverlapCount n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card := by
  ...
```

RHS reduced quotient interval versionは容易なら追加してよい。

この corollary により、

```text
HigherSupportResidual = 0
```

なら第五方向へ進まずとも full-cover frontier は minimal four-direction collision tax `+Collision.card` だけで閉じることが分かる。

逆に HigherSupportResidual > 0 なら、support.card >= 5 の collision seat が存在し、初めて fifth-direction branch が実在する。

---

## 11. 今回の禁止事項

今回やらない:

- fifth direction の recursive descent
- fifth-prime product-wave counting
- generic 5-hypergraph
- `Nat.minFac` の新 injectivity
- NearWaveBudget の解析的評価
- FourthGate の新 fiber counting
- prime counting / sieve / asymptotic estimate
- `SquareOffsetsFullyCovered` contradiction
- Legendre theorem
- RH

**目的は第五方向を作ることではなく、第五方向が必要となる residual を exact に隔離すること。**

---

## 12. Outcome 判定

### Outcome A+

以下が閉じる:

1. collision local residual capacity >= 2
2. HigherSupportResidualExcess 定義
3. exact decomposition
   `DepthResidualCapacity = 2*Collision + HigherSupportResidual`
4. FiveDirectionCollisionSeats 定義/membership
5. local higher residual zero/positive criterion
6. global HigherSupportResidual zero iff no five-direction collision
7. sharpened full-cover frontier
8. no-fifth-direction corollary
9. report/docstrings/facade import

### Outcome A

exact decomposition と sharpened frontier は閉じるが、global zero iff theorem の Finset normalization が awkward。

### Outcome B

`choose(k-1,2) >= 3` の Lean combinatorics のみ engineering block。数学的 counterexample は無し。

この場合は generic library を作らず、局所 binomial helper を別 checkpoint に切る。

### Outcome C

collision support >=4 にもかかわらず local baseline 2 decomposition が反例を持つ。

これは数学的に想定しない。発生したら即停止して具体例を報告する。

---

## 13. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger
lake build DkMath.NumberTheory.Legendre
git diff --check
```

changed Lean source に新規

```text
sorry
admit
axiom
native_decide
```

を入れない。

global `maxHeartbeats` を追加しない。

checkpoint report 推奨:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-depth-residual-fifth-trigger-260827.md
```
