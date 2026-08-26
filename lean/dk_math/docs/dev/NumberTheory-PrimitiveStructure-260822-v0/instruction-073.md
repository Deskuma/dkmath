# instruction-073 — PRIM-L058 Exact Depth Fiber / Local Residual-Pair Capacity

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `0e8882590f4a56e4b083813b676d0f42665a7803`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L057` は **Outcome A — PAID/UNPAID DEPTH LEDGER** として受理する。

L057 までで exact depth branch は

```text
ExactDepth.card
  = DepthSeats.card
  + DepthFiberExcess
```

へ exact に分離され、

```text
DepthSeats.card <= L018 DepthBudget
```

なので、Depth 側の未払い量は `DepthFiberExcess` だけになった。

また `n=58, r=101` では実際に

```text
(15,21) ∈ ExactDepth
(21,15) ∈ ExactDepth
ExactSeat(58,15,21) = 101
ExactSeat(58,21,15) = 101
2 <= DepthPairsAtSeat(58,101).card
```

が Lean で閉じている。

今回の bounded target は、この fiber multiplicity を新しい fifth direction へ進めず、**同一 seat の既存 residual-pair capacity** で上から支払うことだけである。

---

## 1. 数学的核

covered parity-safe seat `r` では canonical support prime を `p₀` とすると、L040/L041 により canonical erasure 後の co-support の card は

```text
(activeSupport n r).card - 1
```

である。

その erased support の unordered pair 数は

```text
choose ((activeSupport n r).card - 1) 2.
```

一方、同じ seat `r` にある exact depth pair `(b,t)` は L054 の reverse reconstruction により unique surviving far key

```text
(p,(q,s))
```

へ戻る。

その key の next seat は `r` であり、L048/L049 の rough/canonical selector equivalence によって

```text
(r,(q,s))
```

は actual canonical far residual incidence になる。

従って `(q,s)` は canonical prime を erase した co-support の unordered pair である。

さらに同一 seat で二つの exact pair が同じ `(q,s)` を与えたなら、canonical ownership により first prime `p` も同じで key が一致し、L052/L054 の dual coordinate equality から元の `(b,t)` も一致する。

よって fixed seat で

```text
DepthPairsAtSeat(n,r)
  ↪ upperPairs(erased canonical co-support at r)
```

という injection が存在する。

したがって主 local capacity は

```text
DepthPairsAtSeat(n,r).card
  <= choose ((activeSupport n r).card - 1) 2.
```

これが今回の魔核である。

特に collision seat では左辺 `>=2` なので

```text
2 <= choose (support.card - 1) 2
```

となり、

```text
4 <= support.card
```

が従う。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeDepthFiberResidualCapacity.lean
```

import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess
```

必要 API が import chain から見えない場合のみ、L048/L049/L040 の直接 import を追加してよい。

完成後 facade `DkMath.NumberTheory.Legendre` へ import を追加する。

---

## 3. L058.1 — exact pair の canonical reverse key

L054 には existential reverse theorem

```lean
paritySafeRechargeExactDualBasePairs_exists_recharge_key
```

がある。

fixed-seat fiber の injection を書きやすくするため、必要ならこの inverse を薄く canonicalize する。

候補:

```lean
noncomputable def paritySafeRechargeExactKeyOfPair
    (n : ℕ) (bt : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  if h : bt ∈ paritySafeRechargeExactDualBasePairs n then
    Classical.choose (paritySafeRechargeExactDualBasePairs_exists_recharge_key h)
  else
    (0,(0,0))
```

public packet:

```lean
theorem paritySafeRechargeExactKeyOfPair_packet
    {n : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDualBasePairs n) :
    paritySafeRechargeExactKeyOfPair n bt ∈
        paritySafeRechargeSurvivingFarProductKeys n ∧
      paritySafeRechargeDualBaseKey n
        (paritySafeRechargeExactKeyOfPair n bt) = bt := by
  ...
```

さらに uniqueness:

```lean
theorem paritySafeRechargeExactKeyOfPair_eq_of_recharge_coordinate
    {n : ℕ} {bt : ℕ × ℕ} {key : ℕ × (ℕ × ℕ)}
    (hbt : bt ∈ paritySafeRechargeExactDualBasePairs n)
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hcoord : paritySafeRechargeDualBaseKey n key = bt) :
    paritySafeRechargeExactKeyOfPair n bt = key := by
  ...
```

L052 `paritySafeRechargeDualBaseKey_injectiveOn` を使う。

この helper が不自然なら、`Finset.card_le_card` / `card_bij` の proof 内で `Classical.choose` を局所使用してもよい。generic inverse API の新設は必須ではない。

---

## 4. L058.2 — reverse key の seat return

L056 には private helper として exact seat = next seat の spine が既にある。
今回 fixed-seat injection に必要なので、public surface を一つだけ追加する。

候補:

```lean
theorem paritySafeRechargeExactKeyOfPair_nextSeat_eq_exactSeat
    {n : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDualBasePairs n) :
    paritySafeFarProductWaveNextSeat n
        (paritySafeRechargeExactKeyOfPair n bt) =
      paritySafeRechargeExactSeat n bt.1 bt.2 := by
  ...
```

または一般 key 版:

```lean
theorem paritySafeRecharge_nextSeat_eq_exactSeat_of_dualCoordinate ...
```

L056 の proof spine を再利用する。大きな reconstruction layer は作らない。

---

## 5. L058.3 — local residual-pair universe

seat `r` の canonical erased support を使って local unordered pair universe を定義する。

候補:

```lean
noncomputable def paritySafeCanonicalResidualPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  upperPairs
    ((squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r))
```

membership theorem を付ける。

covered candidate `hr` に対する exact card:

```lean
theorem paritySafeCanonicalResidualPairsAtSeat_card_eq_choose
    {n r : ℕ}
    (hr : r ∈ paritySafeCoveredCandidates n) :
    (paritySafeCanonicalResidualPairsAtSeat n r).card =
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
  ...
```

使用 API:

- `card_upperPairs_eq_choose`
- `paritySafeSupportExcess_seat_eq_quotientCoSupport_card`

---

## 6. L058.4 — depth fiber pair → local residual pair

fixed seat `r` の depth pair `bt` から reverse key

```text
key = (p,(q,s))
```

を取り、その residual pair `key.2 = (q,s)` を local residual-pair universeへ送る。

推奨 theorem shape:

```lean
theorem paritySafeRechargeExactDepthPair_residualPair_mem
    {n r : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r) :
    (paritySafeRechargeExactKeyOfPair n bt).2 ∈
      paritySafeCanonicalResidualPairsAtSeat n r := by
  ...
```

proof spine:

1. fiber membership から exact depth / exact pair membership と `ExactSeat = r`。
2. reverse key packet から surviving far key。
3. L049 surviving predicate から next seat の rough selector membership。
4. L048 `roughOffsets_eq_canonicalSelector` で canonical selector membership。
5. L058.2 で next seat を `r` に rewrite。
6. L047 `paritySafeCanonicalFarProductWaveOffset_mem_farResidual` で actual far residual incidence。
7. residual incidence membership から `q<s`, `q,s` erased co-support。
8. `upperPairs` membershipへ入れる。

L047 consumer を経由せず rough/canonical membership から直接 erased support membership を取れるなら、より短い route を採用してよい。

---

## 7. L058.5 — fixed-seat injection / local capacity

必須 injection theorem:

```lean
theorem paritySafeRechargeExactDepthPair_residualPair_injectiveOn
    {n r : ℕ} :
    Set.InjOn
      (fun bt => (paritySafeRechargeExactKeyOfPair n bt).2)
      (paritySafeRechargeExactDepthPairsAtSeat n r : Set (ℕ × ℕ)) := by
  ...
```

proof spine:

- two fiber pairs `bt₁,bt₂`。
- corresponding keys `key₁=(p₁,(q,s))`, `key₂=(p₂,(q,s))`。
- L058.4 route で両方が same seat の canonical selector に戻る。
- canonical selector membership から `p₁ = canonicalSupport n r = p₂`。
- residual pair equality と first-prime equality で `key₁=key₂`。
- reverse-key packet の dual coordinate equalityから `bt₁=bt₂`。

この injection から main local capacity:

```lean
theorem paritySafeRechargeExactDepthPairsAtSeat_card_le_choose_support
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).card <=
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
  ...
```

これは今回の最重要 theorem。

---

## 8. L058.6 — collision support richness

main local capacity から instruction-072 の未回収 A+ target を閉じる。

必須:

```lean
theorem paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    4 <= (paritySafeActiveSupport n r).card := by
  ...
```

proof:

- collision membership から fiber.card >= 2。
- L058.5 から `2 <= choose (support.card - 1) 2`。
- `support.card <= 3` を仮定すると `support.card - 1 <= 2` なので `choose ... 2 <= 1`、矛盾。
- `omega` / `Nat.choose_two_right` を使ってよい。

strongly preferred support-cost consumer:

```lean
theorem three_mul_depthFiberCollisionSeats_card_le_supportExcess
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card <=
      paritySafeSupportExcess n := by
  ...
```

理由: collision seat では support.card >=4 なので `support.card - 1 >=3`。collision seats は parity-safe candidate の subset。

これは collision **seat count** の cost であり、FiberExcess 全体を直接 bound する theorem ではないことを docstring に明記する。

---

## 9. L058.7 — unpaid fiber excess の support-only capacity

local capacity を fiber excess に反映する。

collision seat `r` では

```text
fiber.card - 1
  <= choose (support.card - 1) 2 - 1.
```

そこで tight な collision-only budget を定義する。

```lean
noncomputable def paritySafeRechargeExactDepthResidualPairCapacityExcess
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1)
```

必須:

```lean
theorem paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n <=
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  ...
```

proof:

- L057 `DepthFiberExcess_eq_collision_sum`。
- each collision seat で L058.5 local capacity。
- Nat subtraction monotonicity。

これにより exact-coordinate の未払い量を support-only finite capacity へ置換できる。

---

## 10. L058.8 — global consumer

L057 paid/unpaid upper ledgerへ L058.7 を代入する。

必須:

```lean
theorem paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthResidualCapacity_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n <=
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

strongly preferred:

`paritySafePrimePairOverlapCount` 版も同様に追加する。

---

## 11. n=58 regression witness

L057 actual collision を consumer して、一般 theorem の具体例を固定する。

最低限:

```lean
theorem paritySafeRechargeExactDepthFiber_collision_support_58 :
    4 <= (paritySafeActiveSupport 58 101).card := by
  apply paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
  ...
```

A+ target として軽ければ、実際に

```text
paritySafeActiveSupport 58 101 = {3,5,7,11}
```

または card = 4 まで `norm_num` / finite interval reasoning で閉じてよい。

ただしこの具体値のために長い enumeration proof は書かない。

---

## 12. 禁止事項 / 非目標

今回は以下を行わない。

- `DepthFiberExcess = 0` を一般に主張
- fiber singleton / `ExactDepth.card <= L018DepthBudget` を無条件に主張
- fifth direction への展開
- generic graph / hypergraph library
- generic valuation tower
- generic semiprime factorization framework
- smaller anchor / descent / induction
- analytic sieve / PNT / Mertens / asymptotics
- terminal / near / fourth の新 counting estimate
- global contradiction
- Legendre conjecture / RH proof claim

また

```text
3 * CollisionSeats.card <= SupportExcess
```

から `DepthFiberExcess` を直接 SupportExcess で bound してはならない。collision seat 一つの fiber excess は 1 より大きい場合があるため、seat count と multiplicity は区別する。

今回の目的は

```text
fiber multiplicity
  -> existing residual-pair combinatorial capacity
```

への transport だけである。

---

## 13. Outcome 判定

### Outcome A+ — LOCAL RESIDUAL-PAIR CAPACITY

1. reverse key helper / packet（または同等の局所 choice 実装）
2. exact pair seat = reverse key next seat
3. local residual-pair universe + exact choose card
4. depth fiber pair -> local residual pair
5. fixed-seat injection
6. `fiber.card <= choose (support.card - 1) 2`
7. collision support `card >= 4`
8. `3 * CollisionSeats.card <= SupportExcess`
9. support-only `DepthResidualPairCapacityExcess`
10. `DepthFiberExcess <= DepthResidualPairCapacityExcess`
11. global residual upper consumer
12. n=58 regression

### Outcome A — LOCAL FIBER CAPACITY

1–7 と n=58 regression を完成。
support-only excess sum / global consumer のどちらかを Lean API 上の複雑さにより未実装。

### Outcome B — COLLISION SUPPORT ONLY

一般 `collision -> support.card >=4` は閉じるが、fixed-seat full injection / choose capacity の canonical reverse-key surface が不自然。
その obstacle を report して停止する。

### Outcome C — FALSE

実際の exact depth fiber card が `choose (support.card - 1) 2` を超える concrete counterexample、または collision seat で support.card <4 の counterexample が出た場合。

---

## 14. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity
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

## 15. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-depth-fiber-residual-capacity-260826.md
```

最低限:

1. Outcome
2. reverse key / seat return strategy
3. local residual pair universe
4. fixed-seat injection
5. local choose capacity
6. collision support >=4
7. collision seat support cost
8. FiberExcess support-only capacity
9. global consumer
10. n=58 regression
11. non-goals
12. validation

を記録する。

---

## STOP

今回の終了地点は次。

```text
DepthFiber(r).card
  <= choose (ActiveSupport(r).card - 1) 2

collision r
  -> ActiveSupport(r).card >= 4

DepthFiberExcess
  <= DepthResidualPairCapacityExcess

ResidualPairMass
  <= Near
   + Terminal
   + L018DepthBudget
   + DepthResidualPairCapacityExcess
   + Fourth
```

ここで停止する。

次 checkpoint で初めて、`DepthResidualPairCapacityExcess` をさらに support-excess / higher residual combinatorics へ削るか、`ExactFourth` 側へ切り替えるかを比較する。