# instruction-091 — PRIM-L071 Collision Residual-Pair Slack Realization / Unused Pair Incidence

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `de10e963dfc35de70c07e31359e64d91cb4626a1`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L070` は **Outcome A+ — ACTUAL DEPTH-FIBER CANCELLATION / CAPACITY-FREE FULL-COVER FRONTIER COMPLETE** として受理する。

L070 により、full-cover 下の主要 frontier は upper capacity を経由せず

```text
2 * PairOverlapOutsideDepthCollision
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 2 * CollisionResidualPairSlack
+ 3 * totient(2*n)
<=
3 * IncidenceCount
+ 2 * LowCostResidualMass
```

まで exact finite ledger として整理された。

ここで残る

```lean
paritySafeDepthCollisionResidualPairSlack
```

は現在

```text
DepthResidualPairCapacityExcess - DepthFiberExcess
```

という global Nat subtraction として命名されている。しかし L058 には fixed-seat injection

```text
ExactDepthPairsAtSeat
  -> CanonicalResidualPairsAtSeat
```

が既にあり、collision seat `r` では

```text
fiber.card <= choose(support.card - 1, 2)
```

が確定している。

したがって今回の bounded target は、**`CollisionResidualPairSlack` を各 collision seat の「canonical residual-pair universe のうち、実際の exact-depth fiber image に使われていない residual pairs」の cardinality sum として exact realization すること**である。

これにより

```text
Q = 0
```

を単なる数値 tightness ではなく

```text
全 collision seat で depth-fiber residual-pair map が target を飽和する
```

という finite structural statement に変換する。

また

```text
Q > 0
```

から実際の unused residual-pair witness を取り出す。

unused pair から新 prime direction、fifth/sixth wave、descent、full-cover contradiction へは進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeCollisionResidualPairSlackIncidence
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeCollisionResidualPairSlackIncidence.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L071.1 — fixed-seat realized residual-pair image

L058 の既存 map を Finset image として名前付けする。

候補:

```lean
noncomputable def paritySafeRechargeExactDepthResidualPairImageAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDepthPairsAtSeat n r).image
    (fun bt => (paritySafeRechargeExactKeyOfPair n bt).2)
```

必須 subset theorem:

```lean
theorem paritySafeRechargeExactDepthResidualPairImageAtSeat_subset_canonicalResidualPairs
    {n r : ℕ} :
    paritySafeRechargeExactDepthResidualPairImageAtSeat n r ⊆
      paritySafeCanonicalResidualPairsAtSeat n r := by
  ...
```

これは L058 の

```lean
paritySafeRechargeExactDepthPair_residualPair_mem
```

を使う。

必須 card theorem:

```lean
theorem paritySafeRechargeExactDepthResidualPairImageAtSeat_card_eq_fiber
    (n r : ℕ) :
    (paritySafeRechargeExactDepthResidualPairImageAtSeat n r).card =
      (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  ...
```

L058 の

```lean
paritySafeRechargeExactDepthPair_residualPair_injectiveOn
```

をそのまま使う。

`Finset.card_image_of_injOn` / `Finset.card_image_iff` の whichever elaborates cleanly でよい。

---

## 3. L071.2 — unused residual pairs at a collision seat

定義:

```lean
noncomputable def paritySafeDepthCollisionUnusedResidualPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  paritySafeCanonicalResidualPairsAtSeat n r \
    paritySafeRechargeExactDepthResidualPairImageAtSeat n r
```

collision seat は depth seat なので occupied fiber から covered candidate を得られる。
必要なら helper:

```lean
theorem paritySafeDepthFiberCollisionSeat_mem_covered
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    r ∈ paritySafeCoveredCandidates n := by
  ...
```

proof は collision -> depth seat -> nonempty fiber -> choose `bt` ->

```lean
paritySafeRechargeExactDepthPair_mem_covered
```

を使う。

必須 local cardinality theorem:

```lean
theorem paritySafeDepthCollisionUnusedResidualPairsAtSeat_card_eq_capacity_sub_fiber
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).card =
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 -
        (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  ...
```

使用:

- image subset target
- image card = fiber card
- `paritySafeCanonicalResidualPairsAtSeat_card_eq_choose`
- `Finset.card_sdiff_of_subset` 相当

この theorem は **exact equality** とする。

---

## 4. L071.3 — global unused residual-pair mass

新しい global finite mass:

```lean
noncomputable def paritySafeDepthCollisionUnusedResidualPairMass
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).card
```

局所 arithmetic の意味は、collision seat で

```text
m := fiber.card
K := choose(support.card - 1, 2)
2 <= m <= K

(K - 1) = (m - 1) + (K - m)
```

である。

必要なら private helper を module 内だけで置いてよい。

global exact identity をまず閉じる:

```lean
theorem paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_unusedResidualPairMass
    (n : ℕ) :
    paritySafeRechargeExactDepthResidualPairCapacityExcess n =
      paritySafeRechargeExactDepthFiberExcess n +
        paritySafeDepthCollisionUnusedResidualPairMass n := by
  ...
```

推奨 architecture:

1. L058 `DepthResidualPairCapacityExcess` の collision sum を unfold / rw。
2. L057 `DepthFiberExcess_eq_collision_sum` を rw。
3. L071.2 local card theorem。
4. collision 上の `fiber.card <= choose(...)` と `2 <= fiber.card` を使って local identity。
5. `Finset.sum_add_distrib`。

その後、L070 の既存 exact identity

```lean
paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_collisionResidualPairSlack
```

と比較し、必須主定理:

```lean
theorem paritySafeDepthCollisionResidualPairSlack_eq_unusedResidualPairMass
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n =
      paritySafeDepthCollisionUnusedResidualPairMass n := by
  ...
```

を閉じる。

これは今回の最重要 theorem。

---

## 5. L071.4 — zero slack = every collision target is saturated

まず local unused empty と image equality の同値:

```lean
theorem paritySafeDepthCollisionUnusedResidualPairsAtSeat_eq_empty_iff_image_eq_target
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    paritySafeDepthCollisionUnusedResidualPairsAtSeat n r = ∅ ↔
      paritySafeRechargeExactDepthResidualPairImageAtSeat n r =
        paritySafeCanonicalResidualPairsAtSeat n r := by
  ...
```

image subset target は既に L071.1。

次に global criterion:

```lean
theorem paritySafeDepthCollisionResidualPairSlack_eq_zero_iff_all_collision_images_saturate
    (n : ℕ) :
    paritySafeDepthCollisionResidualPairSlack n = 0 ↔
      ∀ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        paritySafeRechargeExactDepthResidualPairImageAtSeat n r =
          paritySafeCanonicalResidualPairsAtSeat n r := by
  ...
```

これは `Q=0` を structural saturation statement へ変換する theorem。

さらに direct surjectivity consumer を推奨:

```lean
theorem paritySafeDepthCollision_residualPair_surjective_of_slack_eq_zero
    {n r : ℕ}
    (hzero : paritySafeDepthCollisionResidualPairSlack n = 0)
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n)
    {qs : ℕ × ℕ}
    (hqs : qs ∈ paritySafeCanonicalResidualPairsAtSeat n r) :
    ∃ bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r,
      (paritySafeRechargeExactKeyOfPair n bt).2 = qs := by
  ...
```

image equalityから回収する。

---

## 6. L071.5 — positive slack gives an actual unused pair witness

必須:

```lean
theorem exists_unused_collisionResidualPair_of_residualPairSlack_pos
    {n : ℕ}
    (hpos : 0 < paritySafeDepthCollisionResidualPairSlack n) :
    ∃ r,
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).Nonempty := by
  ...
```

さらに witness を pair まで開く consumer を推奨:

```lean
theorem exists_unrealized_collisionResidualPair_of_residualPairSlack_pos
    {n : ℕ}
    (hpos : 0 < paritySafeDepthCollisionResidualPairSlack n) :
    ∃ r qs,
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      qs ∈ paritySafeCanonicalResidualPairsAtSeat n r ∧
      qs ∉ paritySafeRechargeExactDepthResidualPairImageAtSeat n r := by
  ...
```

**この unused `qs` を新しい prime direction / fifth-wave / descent と解釈してはいけない。**
今回証明するのは image に未使用な residual pair が存在することだけ。

---

## 7. L071.6 — L070 frontier in realized unused-pair form

L070 の abstract slack を actual finite mass に rewrite する。

必須:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_le_threeSupportExcess_add_twoLowCostMass
    (n : ℕ) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionUnusedResidualPairMass n ≤
        3 * paritySafeSupportExcess n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

L070 theorem + `Q = unused mass` の rewrite でよい。

full-cover / totient consumer:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_add_threeTotient_le_fullCoverActualMass
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      2 * paritySafeDepthCollisionUnusedResidualPairMass n +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMass n := by
  ...
```

reduced quotient interval formも同様に追加する。

---

## 8. optional — global incidence Finset

実装が軽い場合のみ、unused pair を `(seat, pair)` にタグ付けした Finset を作ってよい。

例:

```lean
paritySafeDepthCollisionUnusedResidualPairIncidences
```

そして

```text
Incidences.card = UnusedResidualPairMass = CollisionResidualPairSlack
```

まで閉じられれば A+ bonus。

ただし dependent Finset / `biUnion` 周りで elaboration が重くなる場合は **実装しない**。L071.3 の sum-of-cards realization で今回の目的は達成される。

---

## 9. regression / witness

既存 `n = 58`, `r = 101` collision を使って、今回の API が軽く回帰できるなら追加してよい。

ただし具体的に local fiber が residual-pair target を saturate する／しないことが既存 arithmetic だけで即決できない場合は、数値探索を始めない。

---

## 10. STOP 条件

今回やらない:

- unused residual pair から fresh/fifth/sixth prime を作ること
- fifth-wave capacity
- sixth direction
- `Nat.minFac` injectivity
- residual recursion / descent
- Near の新 counting
- L018 budget の新 estimate
- Fourth injectivity
- L069 capacity slack との大小比較
- analytic / asymptotic estimate
- full-cover contradiction
- Legendre / RH conclusion
- generic hypergraph abstraction

今回の目的は **L070 の最後の abstract Nat slack `Q` を、既存 L058 injection の target に実際に残っている unused finite residual pairs として realization することだけ**。

---

## 11. Outcome 判定

### Outcome A+

以下がすべて閉じる:

1. fixed-seat residual-pair image Finset。
2. image subset canonical residual pairs。
3. image card = depth fiber card。
4. unused residual-pairs-at-seat と exact local card formula。
5. global unused residual-pair mass。
6. `DepthResidualCapacity = FiberExcess + UnusedMass` exact equality。
7. `CollisionResidualPairSlack = UnusedMass` exact equality。
8. `Q=0` iff every collision image saturates its target。
9. `Q>0` -> actual unused pair witness。
10. L070 frontier の unused-mass / totient / reduced-quotient forms。

### Outcome A

6–7 と frontier rewrite までは閉じたが、global saturation / positive witness API が一部未完。

### Outcome E

fixed-seat image/card realization に Mathlib/Finset engineering 障害がある。
その場合は generic abstraction を増設せず、最小 blocker と既存 theorem mismatch を report する。

---

## 12. report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/primitive-parity-safe-collision-residual-pair-slack-incidence-260827.md
```

最低限:

- Outcome
- fixed-seat image / unused pair 定義
- local card formula
- `Q = UnusedResidualPairMass`
- zero saturation criterion
- positive unused-pair witness
- L070 frontier rewrite
- STOP boundary
- changed files / validation

を記録する。