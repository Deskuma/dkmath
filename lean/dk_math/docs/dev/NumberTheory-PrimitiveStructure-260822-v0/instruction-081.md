# instruction-081 — PRIM-L061 Charged Residual Normal Form / Weighted Pair-Overlap Frontier

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `c70be30062b3fa10a8cfb9e5adeee03c5d34385d`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060V` は **Outcome A+ — DISJOINT WEIGHTED SUPPORT-COST CLOSURE** として受理する。

現在 Lean で次が確定している。

```text
PairOverlap
  = SupportExcess + ResidualPairMass

ResidualPairMass
  = Near
  + Terminal
  + DepthSeats
  + DepthFiberExcess
  + Fourth

2 * TerminalKeys.card
+ 3 * CollisionSeats.card
<= SupportExcess

TerminalSeats.card = TerminalKeys.card
```

また L057 では

```text
DepthFiberExcess
  = sum over CollisionSeats of (fiber.card - 1)
```

であり、各 collision fiber は card >= 2 である。

今回の bounded target は **新しい branch counting に進まず**、これら既存 ledger を一つに合成して、Terminal / collision の支払いを反映した weighted pair-overlap frontier を作ることだけである。

---

## 1. 数学的核

記号的に

```text
P := paritySafePrimePairOverlapCount n
S := paritySafeSupportExcess n
N := Near.card
T := TerminalKeys.card
D := DepthSeats.card
E := DepthFiberExcess
F := Fourth.card
C := CollisionSeats.card
```

とする。

既存 exact identity は

```text
P = S + (N + T + D + E + F)
```

である。

L060V より

```text
2*T + 3*C <= S
```

なので Nat subtraction を導入せず slack `K` を existential に取って

```text
S = 2*T + 3*C + K
```

と書ける。

したがって

```text
P
 = N + 3*T + D + E + F + 3*C + K
```

という charged normal form が得られる。

さらに collision seat では `fiber.card >= 2` なので local fiber excess は >=1。従って

```text
C <= E
```

である。

これを使えば

```text
N + 3*T + D + 4*C + F <= P
```

が得られる。

`D` 自体が collision seat を一回含むので、collision seat 一つはこの式の中で実質少なくとも

```text
1 (depth seat)
+ 1 (fiber excess)
+ 3 (support cost)
= 5
```

の pair-overlap cost を持つ。

必要なら `DepthSeats \ CollisionSeats` を noncollision depth seats と定義し、

```text
N + 3*T + NoncollisionDepthSeats.card + 5*C + F <= P
```

という equivalent frontier を追加してよい。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeChargedResidualLedger
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeChargedResidualLedger.lean
```

import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
```

既存 import chain を優先する。

完成後 facade `DkMath.NumberTheory.Legendre` へ import を追加する。

---

## 3. L061.1 — collision count is contained in fiber excess

まず L057 の exact collision sum を consumer にして、collision count が depth fiber excess 以下であることを公開する。

必須:

```lean
theorem paritySafeRechargeExactDepthFiberCollisionSeats_card_le_fiberExcess
    (n : ℕ) :
    (paritySafeRechargeExactDepthFiberCollisionSeats n).card <=
      paritySafeRechargeExactDepthFiberExcess n := by
  ...
```

推奨 proof:

1. `paritySafeRechargeExactDepthFiberExcess_eq_collision_sum` を rewrite。
2. `C.card = sum_C 1`。
3. collision membership から fiber.card >=2。
4. よって `1 <= fiber.card - 1`。
5. `Finset.sum_le_sum`。

新しい combinatorics は不要。

---

## 4. L061.2 — support-charge slack existence

Nat subtraction を global definition として導入しない。

必須:

```lean
theorem exists_terminalCollisionSupportChargeSlack
    (n : ℕ) :
    ∃ k : ℕ,
      paritySafeSupportExcess n =
        2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card + k := by
  ...
```

source:

```lean
two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess n
```

`Nat.exists_eq_add_of_le` 等 current Mathlib の最短 API、または `omega` でよい。

---

## 5. L061.3 — exact charged pair-overlap normal form

既存 exact identities:

```lean
paritySafePrimePairOverlapCount_eq_supportExcess_add_residual

paritySafeResidualPairMass_eq_near_add_terminal_add_depthSeats_add_depthFiberExcess_add_fourth
```

を使う。

第一候補の mandatory theorem:

```lean
theorem exists_paritySafePrimePairOverlapCount_charged_normal_form
    (n : ℕ) :
    ∃ k : ℕ,
      paritySafePrimePairOverlapCount n =
        (paritySafeCanonicalNearResidualTripleIncidences n).card +
        3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        (paritySafeRechargeExactDepthSeats n).card +
        paritySafeRechargeExactDepthFiberExcess n +
        (paritySafeRechargeExactFourthDirectionPairs n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        k := by
  ...
```

addition association が Lean 上重ければ、先に raw form を閉じてから normalized corollary を作ってよい。

raw form 例:

```lean
∃ k,
  P =
    (2*T + 3*C + k) +
    (N + T + D + E + F)
```

その後 `omega` / `simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]` で normalized form にする。

この theorem は exact identity。upper/lower estimate と混同しない。

---

## 6. L061.4 — weighted residual lower frontier

slack `k >= 0` を落として mandatory:

```lean
theorem paritySafeChargedResidualWeight_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      paritySafeRechargeExactDepthFiberExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card <=
        paritySafePrimePairOverlapCount n := by
  ...
```

exact normal form から直接出す。

---

## 7. L061.5 — absorb one unit of fiber excess per collision

L061.1 の `C <= E` を使い、より読みやすい mandatory frontier:

```lean
theorem paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      4 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card <=
        paritySafePrimePairOverlapCount n := by
  ...
```

意味:

```text
Terminal key: residual 1 + support charge 2 = weight >= 3
Collision seat: depth-seat base 1 + fiber excess >=1 + support charge 3 = weight >=5
```

上の theorem では `DepthSeats.card` が collision seat の base 1 を既に含むため、`+ 4*C` で total >=5 を表している。

---

## 8. L061.6 — optional explicit noncollision-depth normal form

軽ければ以下を追加してよい。

```lean
noncomputable def paritySafeRechargeExactDepthNoncollisionSeats (n : ℕ) : Finset ℕ :=
  paritySafeRechargeExactDepthSeats n \
    paritySafeRechargeExactDepthFiberCollisionSeats n
```

collision は depth seats の filter subset なので exact partition:

```lean
DepthSeats.card = NoncollisionDepthSeats.card + CollisionSeats.card
```

を閉じる。

すると corollary:

```text
Near
+ 3*Terminal
+ NoncollisionDepth
+ 5*Collision
+ Fourth
<= PairOverlap
```

が得られる。

これは optional。mandatory 5 まで閉じれば Outcome A+ としてよい。

---

## 9. L061.7 — global coprime pair-capacity consumer

既存 L041:

```lean
paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount
```

と合成して、mandatory:

```lean
theorem paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card +
      3 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthSeats n).card +
      4 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card <=
        squareAnchorCoprimePrimePairOverlapCount n := by
  exact (paritySafeNear_add_threeTerminal_add_depthSeats_add_fourCollision_add_fourth_le_primePairOverlapCount n).trans
    (paritySafePrimePairOverlapCount_le_squareAnchorCoprimePrimePairOverlapCount n)
```

shape は actual theorem namespace / arguments に合わせて調整可。

この theorem は finite global capacity frontier であり、まだ strict contradiction ではない。

---

## 10. regression / sanity

新しい大規模 numeric enumeration は不要。

軽ければ既存 `n=16` terminal witness と `n=58` collision witness を使い、weighted interpretation の arithmetic sanity を一つずつ置いてよい。

例:

```text
n=16 terminal -> weight contribution at least 3
n=58 collision seat 101 -> depth base + support/fiber charge gives local structural weight at least 5
```

ただし generic theorem の証明が主であり regression は optional。

---

## 11. 非目標

今回は以下を行わない。

- Near branch の新 product-wave counting
- FourDirectionGate first-prime fiber counting
- ExactFourth の新 capacity theorem
- fifth direction
- residual recursion
- generic hypergraph
- analytic sieve / PNT / asymptotic
- smaller-anchor descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

また L018 depth budget を今回の **lower frontier** に無理に代入しない。

```text
DepthSeats.card <= L018DepthBudget
```

は upper bound なので、

```text
... + L018DepthBudget <= PairOverlap
```

とはできない。向きを混同しないこと。

---

## 12. Outcome 判定

### Outcome A+ — CHARGED RESIDUAL NORMAL FORM

1. `CollisionSeats.card <= DepthFiberExcess`
2. support-charge slack existence
3. exact charged pair-overlap normal form
4. weighted charged residual <= PairOverlap
5. `Near + 3*Terminal + DepthSeats + 4*Collision + Fourth <= PairOverlap`
6. 上式を coprime prime-pair overlap capacity へ transport
7. facade import / report

optional noncollision-depth normalization が閉じれば A+ 内の強化とする。

### Outcome A — CHARGED PAIR-OVERLAP FRONTIER

1,2,4,5,6 が閉じるが exact existential normal form の association/elaboration が不自然な場合。

### Outcome B — COLLISION/FIBER CHARGE ONLY

`C <= E` と support-charge slack まで。global pair-overlap composition が engineering obstacle。

### Outcome C — FALSE

既存 accepted exact identities と L060V を組み合わせて上の weighted frontier が導けない concrete arithmetic/logical counterexample が出た場合。

---

## 13. STOP

次が Lean で閉じたら停止する。

```text
SupportExcess
  = 2*Terminal + 3*Collision + Slack

PairOverlap
  = Near
  + 3*Terminal
  + DepthSeats
  + DepthFiberExcess
  + Fourth
  + 3*Collision
  + Slack

Collision <= DepthFiberExcess

therefore

Near
+ 3*Terminal
+ DepthSeats
+ 4*Collision
+ Fourth
<= PairOverlap
<= CoprimePrimePairOverlapCapacity
```

この frontier を次 checkpoint で比較し、低コストで残る

```text
Near / noncollision Depth / Fourth
```

のどこへ進むかを選ぶ。