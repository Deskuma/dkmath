# instruction-092 — PRIM-L072 Unused Residual-Pair Routing / LowCost Reabsorption

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `b84d179b25e505d9279e13e6db3192c31e4e7f76`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L071` は **Outcome A+ — COLLISION RESIDUAL-PAIR SLACK REALIZATION / UNUSED PAIR INCIDENCE COMPLETE** として受理する。

L071 により、L070 の abstract slack

```text
Q := paritySafeDepthCollisionResidualPairSlack n
```

は exact に

```text
Q = paritySafeDepthCollisionUnusedResidualPairMass n
```

へ realization されている。

各 collision seat `r` では

```text
UnusedResidualPairsAtSeat
= CanonicalResidualPairsAtSeat \ DepthResidualPairImageAtSeat
```

であり、`Q = 0` は全 collision seat の image saturation、`Q > 0` は actual unused residual-pair witness の存在と同値になった。

今回の bounded target は、**unused residual pair を新しい prime direction と解釈せず、既存 residual decomposition に戻し、Near または ExactFourth branch へ route すること**である。

その結果、unused mass `Q` が既存 `LowCostResidualMass` の内部 mass であることを示し、L071 full-cover frontier の左右にある `2 * Q` をもう一度 cancellation する。

fifth/sixth direction、新 wave capacity、descent、analytic estimate、full-cover contradiction、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeUnusedResidualPairRouting.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeCollisionResidualPairSlackIncidence
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. L072.1 — local unused pair lifts back to an actual residual triple

L071 の local unused pair は `paritySafeCanonicalResidualPairsAtSeat` の要素なので、まず canonical residual triple へ戻す。

必須候補:

```lean
theorem paritySafeDepthCollisionUnusedResidualPair_mem_canonicalResidualTriple
    {n r q s : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n)
    (hqs : (q, s) ∈ paritySafeDepthCollisionUnusedResidualPairsAtSeat n r) :
    (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n := by
  ...
```

証明は新しい factorization を作らず、既存 definition/API から行う。

利用してよいもの:

```text
paritySafeDepthFiberCollisionSeat_mem_covered
paritySafeCanonicalResidualPairsAtSeat
paritySafeCanonicalResidualTripleIncidences
paritySafeCanonicalSupportPrime_packet
squareQuotientAnchorNondivisorSupport_subset_offsetSupport
squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
```

この theorem から既存

```lean
paritySafeCanonicalResidualTripleIncidence_packet
```

をそのまま適用できる consumer も推奨する。

例えば:

```lean
theorem paritySafeDepthCollisionUnusedResidualPair_packet ... :
  let p := paritySafeCanonicalSupportPrime n r
  p ∈ squareAnchorOddActivePrimes n ∧
  q ∈ squareAnchorOddActivePrimes n ∧
  s ∈ squareAnchorOddActivePrimes n ∧
  p ≠ q ∧ p ≠ s ∧ q ≠ s ∧
  p * q * s ∣ n ^ 2 + r := by
  ...
```

**unused pair 自体は新 prime direction ではない。**

---

## 3. L072.2 — global unused triple incidence

L071 では不要だった global incidence Finset を、今回は routing/cardinality のために導入してよい。

最も簡単な推奨形は、既存 canonical residual incidence の filter:

```lean
noncomputable def paritySafeDepthCollisionUnusedResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeCanonicalResidualTripleIncidences n).filter
    (fun triple =>
      triple.1 ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
      triple.2 ∉ paritySafeRechargeExactDepthResidualPairImageAtSeat n triple.1)
```

membership theorem を付ける。

```lean
@[simp] theorem mem_paritySafeDepthCollisionUnusedResidualTripleIncidences ...
```

可能なら local unused membership と直接同値化する。

必須 cardinal realization:

```lean
theorem paritySafeDepthCollisionUnusedResidualTripleIncidences_card_eq_unusedMass
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedResidualTripleIncidences n).card =
      paritySafeDepthCollisionUnusedResidualPairMass n := by
  ...
```

`Finset.card_filter`, `Finset.sum_product'`, `Finset.sum_boole` などで重い場合は、同じ finite set をより elaboration-safe な定義に変更してよい。

ただし generic dependent hypergraph abstraction は作らない。

---

## 4. L072.3 — exact Near/Far split of unused triples

既存 L046 の exact partition:

```text
CanonicalResidualTripleIncidences
= NearResidualTripleIncidences ⊔ FarResidualTripleIncidences
```

を unused incidence に制限する。

推奨 definitions:

```lean
noncomputable def paritySafeDepthCollisionUnusedNearResidualTriples (n : ℕ) :=
  (paritySafeDepthCollisionUnusedResidualTripleIncidences n).filter
    (fun triple => triple ∈ paritySafeCanonicalNearResidualTripleIncidences n)

noncomputable def paritySafeDepthCollisionUnusedFarResidualTriples (n : ℕ) :=
  (paritySafeDepthCollisionUnusedResidualTripleIncidences n).filter
    (fun triple => triple ∈ paritySafeCanonicalFarResidualTripleIncidences n)
```

必須:

```text
UnusedNear ∩ UnusedFar = ∅
UnusedNear ∪ UnusedFar = UnusedAll
UnusedAll.card = UnusedNear.card + UnusedFar.card
```

Near side は即座に

```lean
theorem paritySafeDepthCollisionUnusedNearResidualTriples_subset_near
```

および

```lean
theorem paritySafeDepthCollisionUnusedNearResidualTriples_card_le_near
```

まで閉じる。

---

## 5. L072.4 — Far unused triple cannot be Terminal

`triple = (r,(q,s)) ∈ UnusedFar` とする。

canonical key

```text
key := (paritySafeCanonicalSupportPrime n r, (q, s))
```

について、既存 API を使って surviving far key へ戻す。

推奨経路:

```text
hfar
-> paritySafeCanonicalFarResidual_mem_productWaveSelector
-> paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
-> mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
-> key ∈ paritySafeSurvivingFarProductKeys
```

その後 terminal/recharge split を使う。

Terminal の場合、`r = nextSeat key` から

```text
r ∈ paritySafeTerminalFarProductSeats n
```

となるが、unused triple の seat は collision seat なので既存

```lean
paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
```

に反する。

必須 theorem 例:

```lean
theorem paritySafeDepthCollisionUnusedFarResidual_key_mem_recharge
    {n r q s : ℕ}
    (hunusedFar : (r, (q, s)) ∈
      paritySafeDepthCollisionUnusedFarResidualTriples n) :
    (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeRechargeSurvivingFarProductKeys n := by
  ...
```

---

## 6. L072.5 — Far unused triple routes to ExactFourth, not ExactDepth

上の recharge key を `key` とし、

```text
bt := paritySafeRechargeDualBaseKey n key
```

とする。

既存:

```text
paritySafeRechargeDualBaseKey_mem_exact
paritySafeRechargeExactDepthFourth_union
paritySafeRechargeExactDepthFourth_disjoint
```

により `bt` は ExactDepth または ExactFourth。

ExactDepth と仮定した場合は、

1. selector/survival から `r = paritySafeFarProductWaveNextSeat n key`。
2. `paritySafeRechargeExactSeat_eq_waveNextSeat_of_recharge_key` を使い、`bt` が `paritySafeRechargeExactDepthPairsAtSeat n r` に属することを示す。
3. `paritySafeRechargeExactKeyOfPair_packet` と
   `paritySafeRechargeDualBaseKey_injectiveOn` により、canonical choice の reverse key が元の `key` と一致することを示す。
4. 従って `(q,s)` は `paritySafeRechargeExactDepthResidualPairImageAtSeat n r` に入る。
5. unused 条件と矛盾。

よって ExactFourth。

必須 theorem 例:

```lean
theorem paritySafeDepthCollisionUnusedFarResidual_dualBase_mem_exactFourth
    {n r q s : ℕ}
    (hunusedFar : (r, (q, s)) ∈
      paritySafeDepthCollisionUnusedFarResidualTriples n) :
    paritySafeRechargeDualBaseKey n
      (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
        paritySafeRechargeExactFourthDirectionPairs n := by
  ...
```

ここが今回の数学的中心。

---

## 7. L072.6 — Far routing map is injective

Far unused triple を ExactFourth coordinate へ送る map を定義する。

```lean
noncomputable def paritySafeDepthCollisionUnusedFarToFourth
    (n : ℕ) (triple : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  paritySafeRechargeDualBaseKey n
    (paritySafeCanonicalSupportPrime n triple.1, triple.2)
```

Far unused domain 上で injective を示す。

推奨:

- equal dual-base coordinates
- `paritySafeRechargeDualBaseKey_injectiveOn`
- canonical recharge keys equal
- residual pair equal
- each far incidence has `seat = nextSeat key`
- therefore seat equal

必須 consumers:

```lean
theorem paritySafeDepthCollisionUnusedFarResidualTriples_card_le_exactFourth
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedFarResidualTriples n).card ≤
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

---

## 8. L072.7 — unused mass is already inside LowCost mass

Near/Far card splitと前節の two upper bounds から、まず

```lean
theorem paritySafeDepthCollisionUnusedResidualPairMass_le_near_add_fourth
    (n : ℕ) :
    paritySafeDepthCollisionUnusedResidualPairMass n ≤
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

次に `LowCostResidualMass` の定義から

```lean
theorem paritySafeDepthCollisionUnusedResidualPairMass_le_lowCostResidualMass
    (n : ℕ) :
    paritySafeDepthCollisionUnusedResidualPairMass n ≤
      paritySafeLowCostResidualMass n := by
  ...
```

を閉じる。

この theorem は **unused mass が独立した新 branch ではなく、既存 LowCost actual mass の内部に再吸収できる**ことを意味する。

---

## 9. L072.8 — LowCost remainder after unused routing

```lean
noncomputable def paritySafeLowCostResidualMassAfterUnused
    (n : ℕ) : ℕ :=
  paritySafeLowCostResidualMass n -
    paritySafeDepthCollisionUnusedResidualPairMass n
```

必須 exact identity:

```lean
theorem paritySafeLowCostResidualMass_eq_unused_add_afterUnused
    (n : ℕ) :
    paritySafeLowCostResidualMass n =
      paritySafeDepthCollisionUnusedResidualPairMass n +
      paritySafeLowCostResidualMassAfterUnused n := by
  ...
```

これは前節の upper bound を用いた Nat exact difference とする。

---

## 10. L072.9 — second cancellation frontier

L071 full-cover realized frontier:

```text
2 * OutsideCollisionPairOverlap
+ 9 * Collision.card
+ 3 * FiveDirection.card
+ 2 * UnusedResidualPairMass
+ 3 * totient(2*n)
<=
3 * IncidenceCount
+ 2 * LowCostResidualMass
```

へ L072.8 を代入し、`2 * UnusedResidualPairMass` を左右から cancellation する。

必須主定理:

```lean
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_threeTotient_le_fullCoverLowCostAfterUnused
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMassAfterUnused n := by
  ...
```

recommended/A+:

```lean
theorem ..._le_reducedQuotient_fullCoverLowCostAfterUnused ...
```

with `paritySafeIncidenceCount_eq_reducedQuotientInterval_sum` rewrite.

最終 RHS には以下を残さない:

```text
CollisionResidualPairSlack
UnusedResidualPairMass
LowCostResidualCapacity
LowCostResidualCapacitySlack
DepthResidualPairCapacityExcess
DepthFiberExcess
HigherSupportResidualExcess
```

---

## 11. n = 58 false-beam regression（推奨、計算が軽い場合のみ）

既存 collision witness `n = 58`, `r = 101` では

```text
58^2 + 101 = 3465 = 3^2 * 5 * 7 * 11
```

であり、既存 L057 witness は residual pair `(5,11)` と `(7,11)` を depth image に供給する。

canonical residual target には `(5,7)` も存在し、

```text
3 * 5 * 7 = 105 < 2 * 58 = 116
```

なので `(101,(5,7))` は Near 側の residual triple になるはずである。

もし `norm_num` / existing API だけで軽く閉じるなら、例えば

```lean
(5, 7) ∈ paritySafeDepthCollisionUnusedResidualPairsAtSeat 58 101
```

および

```lean
(101, (5, 7)) ∈ paritySafeCanonicalNearResidualTripleIncidences 58
```

を regression として追加してよい。

ただしこの regression のために definitions を大規模 unfold したり、`native_decide` を使ったり、checkpoint を止めたりしない。

この例の意味は明確:

```text
unused residual pair ≠ new fifth direction
```

であり、Near/Fourth routing を支持する false beam である。

---

## 12. STOP / 禁止

今回やらないこと:

- unused pair から fresh prime / fifth / sixth prime direction を作らない
- fifth/sixth product-wave counting を作らない
- Near wave の新しい asymptotic estimate をしない
- L018 depth budget を再評価しない
- Fourth gate capacity/slack を再評価しない
- generic hypergraph / recursive direction hierarchy を作らない
- descent をしない
- full-cover contradiction を主張しない
- Legendre / RH 結論へ進まない

---

## 13. Outcome 判定

### Outcome A+

以下が全部閉じる:

1. local unused pair -> canonical residual triple
2. global unused triple incidence with card = unused mass
3. unused Near/Far exact split
4. Far unused -> recharge（Terminal 排除）
5. Far unused dual-base -> ExactFourth（Depth 排除）
6. Far routing injection and card <= ExactFourth
7. `UnusedMass <= Near.card + ExactFourth.card`
8. `UnusedMass <= LowCostResidualMass`
9. `LowCostMass = UnusedMass + AfterUnused`
10. second cancellation full-cover frontier
11. reduced quotient consumer

### Outcome A

1--5 は閉じるが、global injection/cardinality cancellation に API engineering obstacle がある。
その場合は obstacle を exact theorem name / elaboration point とともに report し、generic abstraction へ逃げない。

### Outcome E

local unused pair を canonical residual tripleへ戻せない、または Far unused を Depth image から排除できない場合。
その場合は false beam / missing bridge を report して止める。

---

## 14. 実装レポート

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-unused-residual-pair-routing-260827.md
```

最低限記録:

- local unused pair packet
- global unused incidence realization
- Near/Far routing
- Terminal 排除の理由
- ExactDepth 排除の理由
- Far -> ExactFourth injection
- `UnusedMass <= LowCostMass`
- second cancellation frontier
- remaining RHS terms
- false beam/regression を追加した場合はその意味
- STOP を守ったこと
