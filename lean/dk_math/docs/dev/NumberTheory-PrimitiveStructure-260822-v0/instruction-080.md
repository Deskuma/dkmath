# instruction-080 — PRIM-L060V Terminal / Collision Disjoint Weighted Support-Cost Ledger

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `615f66f2b0bf24663aabbe2bbe9b49071779cccd`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060U` は **Outcome A+ — DIRECT TERMINAL SEAT INJECTION / SEAT-CARD CLOSURE** として受理する。

L060U で cofactor 系の `whnf` blocker は回避された。現在 Lean で次が確定している。

```text
Terminal key=(p,(q,s))
  -> terminal next seat r
  -> ActiveSupport(n,r).card = 3

same terminal seat
  -> same canonical first prime
  -> same exact three-support
  -> ordering p<q<s fixes q,s
  -> same terminal key

TerminalSeats.card = TerminalKeys.card
```

今回の bounded target は、元 L060 の最後の残務である **support-cost ledger のみ**を閉じること。

```text
Terminal seat      -> support.card = 3 -> local cost = 2
Depth collision    -> support.card >= 4 -> local cost >= 3

TerminalSeats ∩ CollisionSeats = ∅

2 * TerminalKeys.card
+ 3 * CollisionSeats.card
<= SupportExcess
```

Near、FourDirectionGate fiber counting、ExactFourth の新 counting、第五方向、新しい residual 分解、descent には進まない。

---

## 1. 重要な数学的制約

今回の main theorem は、既存の個別 theorem

```text
2*T <= SupportExcess
3*C <= SupportExcess
```

を足して作ってはならない。

`SupportExcess` を二重に消費するためである。

必ず **disjoint union 上の一つの candidate-side sum** から証明する。

局所 cost function は

```lean
fun r => (paritySafeActiveSupport n r).card - 1
```

とする。

---

## 2. 既存 consumer API

### L060S/U

```lean
paritySafeTerminalFarProductSeats
mem_paritySafeTerminalFarProductSeats
paritySafeTerminalSurvivingFarProductKey_residual_seat
paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
paritySafeTerminalFarProductSeats_card_eq_terminalKeys
```

### L058/L059

```lean
paritySafeRechargeExactDepthFiberCollisionSeats
mem_paritySafeRechargeExactDepthFiberCollisionSeats
paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
three_mul_depthFiberCollisionSeats_card_le_supportExcess
```

`three_mul_depthFiberCollisionSeats_card_le_supportExcess` は comparison / regression として使ってよいが、main combined theorem を単純加算で作らない。

### support ledger

```lean
paritySafeSupportExcess
squareAnchorOddPointCoprimeOffsets
```

`paritySafeSupportExcess` は candidate 上の `support.card - 1` の sum。

---

## 3. L060V.1 — collision seats subset candidate を public 化

L059 `three_mul_depthFiberCollisionSeats_card_le_supportExcess` の proof 内には既に

```lean
have hsub : paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
    squareAnchorOddPointCoprimeOffsets n := by
  ...
```

がある。

これを再利用可能な public theorem として `ParitySafeFourDirectionGate.lean` に昇格する。

必須:

```lean
theorem paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  ...
```

既存 cost theorem は可能ならこの theorem を consumer するよう軽く refactor してよいが、proof churn が大きいなら不要。

新しい数学は入れない。

---

## 4. L060V.2 — terminal seat support/card/candidate surface

`ParitySafeTerminalSupportCost.lean` を継続編集する。

### 4.1 terminal seat support card = 3

必須:

```lean
theorem paritySafeTerminalFarProductSeat_activeSupport_card_eq_three
    {n r : ℕ}
    (hr : r ∈ paritySafeTerminalFarProductSeats n) :
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

proof:

1. `mem_paritySafeTerminalFarProductSeats.mp hr` で key witness を取る。
2. key を `(p,(q,s))` に destruct。
3. L060S `paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three`。
4. `nextSeat key = r` で rewrite。

support の定義を unfold しない。

### 4.2 terminal seats subset candidate

必須:

```lean
theorem paritySafeTerminalFarProductSeats_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  ...
```

推奨 route:

- terminal seat image witness `key=(p,(q,s))`。
- `paritySafeTerminalSurvivingFarProductKey_residual_seat hkey`。
- far residual membership を underlying residual incidenceへ落とす。
- `paritySafeCanonicalResidualTripleIncidence_packet` の candidate component を使う。
- seat equalityで transport。

covered candidate まで取れてもよいが mandatory ではない。

---

## 5. L060V.3 — terminal / collision seat disjointness

Terminal seat は support card exactly `3`。
Collision seat は L058 より support card at least `4`。

必須:

```lean
theorem paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
    (n : ℕ) :
    Disjoint
      (paritySafeTerminalFarProductSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  ...
```

proof は `Finset.disjoint_left` で十分。

```text
r ∈ TerminalSeats
r ∈ CollisionSeats
-> support.card = 3
-> 4 <= support.card
-> contradiction by omega
```

この theorem は support-size separation そのものなので、cofactor / nextSeat injectivity / FourGate を使わない。

---

## 6. L060V.4 — exact terminal local cost sum

局所 cost を明示しておくと main theorem が軽くなる。

推奨:

```lean
theorem paritySafeTerminalFarProductSeats_supportCost_sum_eq
    (n : ℕ) :
    (∑ r ∈ paritySafeTerminalFarProductSeats n,
      ((paritySafeActiveSupport n r).card - 1)) =
      2 * (paritySafeTerminalFarProductSeats n).card := by
  ...
```

または向き逆でもよい。

proof:

- `Finset.sum_congr`
- terminal seat card=3
- each term becomes 2
- `simp [Nat.mul_comm]`

key card versionへの rewrite は main theorem 最後に行う。

---

## 7. L060V.5 — collision local lower-cost sum

既存 L059 theorem は global SupportExcess まで進んでいるが、combined proof には union 前の local lower bound が必要。

薄い public theoremを追加する。

必須:

```lean
theorem three_mul_depthFiberCollisionSeats_card_le_localSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
      ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
  ...
```

proof は L059 existing `hterm` 部分そのもの。

```text
collision -> support.card >=4 -> 3 <= support.card-1
```

これも新数学ではなく既存 proof の factorization。

---

## 8. L060V.6 — union subset candidate

TerminalSeats と CollisionSeats の両 subset theorem から、

```lean
theorem paritySafeTerminalCollisionSeats_union_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ∪
      paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
        squareAnchorOddPointCoprimeOffsets n := by
  ...
```

を薄く追加してよい。

必須でなく main theorem 内 local `have` でもよい。

---

## 9. L060V.7 — main combined weighted support-cost ledger

今回の主 theorem。

必須:

```lean
theorem two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  ...
```

### 必須 proof architecture

`T := paritySafeTerminalFarProductSeats n`
`C := paritySafeRechargeExactDepthFiberCollisionSeats n`
`f r := (paritySafeActiveSupport n r).card - 1`

と考える。

1. L060U:

   ```text
   T.card = TerminalKeys.card
   ```

2. Terminal exact cost:

   ```text
   sum_T f = 2*T.card
   ```

3. Collision lower cost:

   ```text
   3*C.card <= sum_C f
   ```

4. `Disjoint T C` より

   ```text
   sum_(T ∪ C) f = sum_T f + sum_C f
   ```

   `Finset.sum_union` / current Mathlib equivalent を使用。

5. `T ∪ C ⊆ candidates` より

   ```text
   sum_(T ∪ C) f <= sum_candidates f
   ```

   非負 `Nat` なので `Finset.sum_le_sum_of_subset_of_nonneg` が使える。

6. `sum_candidates f = paritySafeSupportExcess n`。

したがって

```text
2*T.card + 3*C.card
  = sum_T f + 3*C.card
 <= sum_T f + sum_C f
  = sum_(T∪C) f
 <= SupportExcess
```

最後に `T.card = TerminalKeys.card` で statement へ rewrite。

### 禁止

次の形は禁止:

```text
have hT : 2*T <= SupportExcess := ...
have hC : 3*C <= SupportExcess := ...
omega
```

これは同じ `SupportExcess` を二回使う。

main theorem の proof term に **disjoint union / one sum** が実際に現れることを要求する。

---

## 10. optional consumers / regressions

### 10.1 seat version

key rewrite 前の theorem を public にしてよい。

```lean
theorem two_mul_terminalSeats_add_three_mul_collisionSeats_le_supportExcess ...
```

main proof を二段に分けるならむしろ推奨。

### 10.2 individual terminal cost

main theorem から

```lean
2 * TerminalKeys.card <= SupportExcess
```

を corollary にしてよい。

ただし main theorem の入力として個別 inequality を使わない。

### 10.3 n=16 / n=58

- n=16 terminal seat 17 の cost =2。
- n=58 collision seat 101 は terminal seat ではない。

が general theorem から軽く閉じるなら regression として追加してよい。

---

## 11. 非目標

今回は以下を行わない。

- Near branch counting
- FourDirectionGate first-prime fiber counting
- ExactFourth pair counting の強化
- fifth direction
- `DepthResidualPairCapacityExcess` の再帰分解
- generic weighted-hypergraph library
- analytic sieve / PNT / Mertens
- smaller anchor / descent / induction
- global contradiction
- Legendre conjecture / RH claim

また L060U の direct terminal injectivity proof を cofactor routeへ戻さない。

---

## 12. Outcome 判定

### Outcome A+ — DISJOINT WEIGHTED SUPPORT-COST CLOSURE

1. collision seats subset candidate public theorem
2. terminal seat support card=3
3. terminal seats subset candidate
4. TerminalSeats / CollisionSeats disjoint
5. terminal exact local cost sum
6. collision local lower cost sum
7. union subset candidate / equivalent local proof
8. single-union-sum main theorem

   ```text
   2*TerminalKeys.card + 3*CollisionSeats.card <= SupportExcess
   ```

9. report / docstrings

### Outcome A — SEAT-SIDE WEIGHTED CLOSURE

2–7 を閉じ、

```text
2*TerminalSeats.card + 3*CollisionSeats.card <= SupportExcess
```

まで完成するが key-card rewrite が engineering 上不自然。

L060U の card equality は既にあるため通常は A+ を期待する。

### Outcome B — DISJOINT LOCAL COST ONLY

Terminal support=3 transport、collision support>=4、disjointness、local cost sums は閉じるが union sum elaboration が engineering blocker。

### Outcome C — FALSE

- terminal seat と collision seat の concrete intersection、または
- terminal seat で support.card ≠3

の concrete counterexample が出た場合。

---

## 13. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate
lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
lake build DkMath.NumberTheory.Legendre
git diff --check
```

変更 Lean source について

```text
sorry
admit
axiom
native_decide
```

を追加しない。

---

## 14. STOP

次が Lean で閉じたら停止する。

```text
Terminal seat
  -> support.card = 3
  -> support cost exactly 2

Collision seat
  -> support.card >=4
  -> support cost at least 3

TerminalSeats ∩ CollisionSeats = empty

2 * TerminalKeys.card
+ 3 * CollisionSeats.card
<= SupportExcess
```

ここでレビューへ戻す。
