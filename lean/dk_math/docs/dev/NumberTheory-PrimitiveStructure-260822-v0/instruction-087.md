# instruction-087 — PRIM-L067 Fifth-Direction Packet / Fifth-Power Gate / Extra Support Charge

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `440c6ce2822cd5126b1b81eac00ef09ae877219f`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L066` は **Outcome A+ — DEPTH RESIDUAL BASELINE / FIFTH-DIRECTION TRIGGER ISOLATION COMPLETE** として受理する。

L066 により、collision residual は exact に

```text
DepthResidualPairCapacityExcess
= 2 * Collision.card
  + HigherSupportResidualExcess
```

へ分解され、さらに

```text
HigherSupportResidualExcess = 0
  iff FiveDirectionCollisionSeats = ∅
```

および collision seat 上で

```text
local higher residual > 0
  iff support.card >= 5
```

が確定した。

ここで重要なのは、L066 の「FiveDirection」はまだ `support.card >= 5` という発火条件の名前であり、実際の第五素数方向を抽出した theorem ではないことである。

今回の bounded target は、**五方向 collision seat から実際の 5 個の distinct active prime directions を取り出し、canonical first prime の fifth-power gate を証明し、同じ `support.card >= 5` を既存 support-cost ledger の追加 1 charge に反映すること**だけである。

five-direction wave capacity、fifth-prime injectivity、sixth direction、residual recursion/descent、analytic estimate、full-cover contradiction、Legendre/RH 結論には進まない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFifthDirectionGate.lean
```

import はまず

```lean
DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger
```

のみで試す。

facade `DkMath.NumberTheory.Legendre` に import を追加する。

---

## 2. 既存確定 API

### L059 four-direction packet

```lean
paritySafeRechargeDepthFiberCollision_fourDirection_packet
```

collision seat `r`、`p := paritySafeCanonicalSupportPrime n r` に対して、既に

```text
∃ q s u,
  q,s,u ∈ activeSupport(n,r)
  p < q, p < s, p < u
  q,s,u pairwise distinct
  p*q*s*u | n^2+r
```

が得られる。

また:

```lean
paritySafeRechargeDepthFiberCollision_canonicalPrime_mem_fourDirectionGate
paritySafeFourDirectionGatePrimes
```

がある。

### L066 five-direction trigger

```lean
paritySafeRechargeExactDepthFiveDirectionCollisionSeats
mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats
paritySafeRechargeExactDepthFiveDirectionCollisionSeats_subset_collision

paritySafeRechargeExactDepthHigherSupportResidualExcess
paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision
```

FiveDirectionCollisionSeat では

```text
5 <= activeSupport.card
```

が確定する。

### L060V support-cost ledger

```lean
paritySafeTerminalFarProductSeats_supportCost_sum_eq
three_mul_depthFiberCollisionSeats_card_le_localSupportCost
paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
paritySafeTerminalCollisionSeats_union_subset_candidate
paritySafeTerminalFarProductSeats_card_eq_terminalKeys

two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
```

今回、この最後の charge を five-direction seat 1 個につきさらに 1 だけ強化する。

---

## 3. L067.1 — actual fifth support direction packet

必須主定理その1。

候補 shape:

```lean
theorem paritySafeRechargeDepthFiveDirectionCollision_fiveDirection_packet
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    let p := paritySafeCanonicalSupportPrime n r
    ∃ q s u v,
      p ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r ∧
      u ∈ paritySafeActiveSupport n r ∧
      v ∈ paritySafeActiveSupport n r ∧
      p < q ∧ p < s ∧ p < u ∧ p < v ∧
      q ≠ s ∧ q ≠ u ∧ q ≠ v ∧
      s ≠ u ∧ s ≠ v ∧ u ≠ v ∧
      p * q * s * u * v ∣ n ^ 2 + r := by
  ...
```

証明方針:

1. `hr` から collision membership と `support.card >= 5` を得る。
2. L059 `paritySafeRechargeDepthFiberCollision_fourDirection_packet` から `q,s,u` を得る。
3. canonical `p` の active-support membership を既存 covered/canonical packet から得る。
   - collision seat -> depth seat -> nonempty depth fiber -> covered candidate
   - `paritySafeCanonicalSupportPrime_packet`
   の既存 route を再利用してよい。
4. `p,q,s,u` は 4 個 distinct で active support に入っている。
5. `support.card >= 5` なので `{p,q,s,u}` の外に `v` が存在することを Finset で示す。
   - generic cardinality library は作らない。
   - `support \ {p,q,s,u}` の nonempty、または「support ⊆ {p,q,s,u}` を仮定すると card <= 4」の contradiction でよい。
6. canonical minimum から `p <= v`、`v != p` から `p < v`。
7. `v ∈ activeSupport` から `v` prime / active / `v | n^2+r` を得る。
8. L059 の `p*q*s*u | n^2+r` と、distinct-prime coprimalityを使って

```text
p*q*s*u*v | n^2+r
```

を得る。

`Nat.Coprime.mul_dvd_of_dvd_of_dvd` と `Nat.coprime_primes` を使ってよい。

**新しい generic five-tuple / hypergraph abstractionは作らない。**

---

## 4. L067.2 — fifth-power gate

新しい finite gate:

```lean
noncomputable def paritySafeFiveDirectionGatePrimes
    (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun p => p ^ 5 < squareBody n)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeFiveDirectionGatePrimes
    {n p : ℕ} :
    p ∈ paritySafeFiveDirectionGatePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧ p ^ 5 < squareBody n := by
  ...
```

refinement:

```lean
theorem paritySafeFiveDirectionGatePrimes_subset_fourDirectionGatePrimes
    (n : ℕ) :
    paritySafeFiveDirectionGatePrimes n ⊆
      paritySafeFourDirectionGatePrimes n := by
  ...
```

active prime なので `2 <= p` を使い、`p^4 < p^5` から既存 four-direction gate へ落とす。

cardinality corollary も容易なら追加する:

```lean
theorem paritySafeFiveDirectionGatePrimes_card_le_fourDirectionGatePrimes ...
```

---

## 5. L067.3 — five-direction collision canonical prime enters p^5 gate

必須主定理その2:

```lean
theorem paritySafeRechargeDepthFiveDirectionCollision_canonicalPrime_mem_fiveDirectionGate
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    paritySafeCanonicalSupportPrime n r ∈
      paritySafeFiveDirectionGatePrimes n := by
  ...
```

L067.1 packet の `p<q,s,u,v` と 5-prime product divisibilityから

```text
p^5 < p*q*s*u*v <= n^2+r <= squareBody n
```

を示す。

注意:

- `p^5 < product` は明示的な multiplication monotonicity chain でよい。
- `product <= n^2+r` は point positivity + divisibility。
- `n^2+r <= squareBody n` は candidate/square-offset packet。
- `p` の active membershipを失わない。

この theorem が今回の数学的中心である。

---

## 6. L067.4 — global trigger reaches an actual fifth-power gate

L066 の global trigger と L067.3 を接続する。

まず positive/nonempty form を public にしてよい:

```lean
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_pos_iff_fiveDirectionCollision_nonempty
    (n : ℕ) :
    0 < paritySafeRechargeExactDepthHigherSupportResidualExcess n ↔
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).Nonempty := by
  ...
```

既存

```lean
paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision
```

から導いてよい。

そして:

```lean
theorem exists_fiveDirectionGatePrime_of_higherSupportResidualExcess_pos
    {n : ℕ}
    (hpos : 0 < paritySafeRechargeExactDepthHigherSupportResidualExcess n) :
    ∃ r,
      r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ∧
      paritySafeCanonicalSupportPrime n r ∈
        paritySafeFiveDirectionGatePrimes n := by
  ...
```

これで

```text
HigherSupportResidualExcess > 0
  -> actual five-support collision seat
  -> canonical p with p^5 < squareBody
```

が Lean theorem になる。

---

## 7. L067.5 — five-direction seats add one extra support-cost unit

FiveDirectionCollisionSeat では `support.card >= 5` なので、collision baseline support cost 3 より 1 多い。

局所 helper:

```lean
theorem paritySafeFiveDirectionCollision_localSupportCost_ge_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    4 ≤ (paritySafeActiveSupport n r).card - 1 := by
  ...
```

global collision charge を同じ seat sum の中で強化する。

必須:

```lean
theorem three_mul_collision_add_fiveDirection_card_le_localSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1) := by
  ...
```

推奨 proof:

collision set `C`、five set `F ⊆ C` として各 `r ∈ C` に

```text
3 + (if r ∈ F then 1 else 0) <= supportCost(r)
```

を示して sum する。

- `r ∈ F` なら L067.5 local `>=4`
- `r ∉ F` でも collision なので既存 `support.card >=4` から `>=3`
- `∑ r∈C if r∈F then 1 else 0 = F.card` は `F ⊆ C` を使う。

**既存 `3*C <= localCost` と別個の `F <= localCost` を足してはいけない。**
同じ local support cost を二重 charge しないこと。

---

## 8. L067.6 — strengthen terminal/collision support charge

L060V と同じ disjoint union architecture を使って、必須:

```lean
theorem two_mul_terminalKeys_add_three_mul_collision_add_fiveDirection_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  ...
```

proof architecture:

1. terminal seats と collision seats の既存 disjointness。
2. terminal support-cost exact `2`。
3. L067.5 の strengthened collision local sum。
4. union subset candidate。
5. candidate-side support-excess sumへ一度だけ包含。

L060V theorem を単純に足し算するのではなく、**union support-cost sum を再利用して single charge** とする。

---

## 9. L067.7 — sharpen L066 full-cover frontier by one unit per five-direction seat

L065/L066 の algebra に strengthened support charge を反映する。

必須 readable form:

```lean
theorem two_mul_pairOverlap_add_fiveDirection_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  ...
```

導出の係数確認:

```text
PairOverlap = S + R
R <= LowCost + T + DepthResidual
2*T + 3*C + F <= S
DepthResidual = 2*C + H
Candidate + S = Incidence       [full cover]
Candidate.card = totient(2*n)
```

より

```text
2*P + F + 3*totient(2*n)
<= 3*I + 2*LowCost + C + 2*H
```

となる。

reduced quotient interval rewrite も容易なら追加する。

no-fifth caseは L066 theorem と同値になるので、新しい重複 corollary は必須ではない。

---

## 10. facade / report

facade:

```text
DkMath.NumberTheory.Legendre
```

へ新 module import を追加する。

report 推奨:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-fifth-direction-gate-260827.md
```

report には少なくとも:

1. actual fifth-prime packet
2. `p^5 < squareBody` gate
3. HigherSupportResidual positive -> five-direction gate witness
4. support charge `2*T + 3*C + F <= S`
5. sharpened full-cover frontier
6. 非目標

を記録する。

---

## 11. Outcome 判定

### Outcome A+

以下をすべて達成:

1. actual 5-direction prime packet
2. `FiveDirectionGatePrimes`
3. five-gate subset four-gate
4. every FiveDirectionCollision canonical prime enters five-gate
5. positive HigherSupportResidual -> actual five-gate witness
6. strengthened collision support-cost `3*C + F <= localCost`
7. strengthened global support charge `2*T + 3*C + F <= S`
8. sharpened full-cover frontier
9. facade / report

### Outcome A

1--5 と 6--7 の少なくとも一方を達成し、残りが Lean engineering 上の小障害。
数学的 counterexample はない。

### Outcome B

actual fifth direction packet / five-power gate は閉じるが、support-charge strengthening に実質的障害がある。
障害 theorem と不足 API を report する。

### Outcome C

`support.card >= 5` から上記 actual five-prime packet / fifth-power gate が導けない concrete mathematical counterexample がある。

### Outcome E

数学ではなく elaboration / performance / API visibility のみが blocker。
最小再現を report する。

---

## 12. 明示的非目標

今回やらない:

- fifth product-wave capacity
- fifth-prime injectivity
- `(p,v)` 等から seat / key を復元すること
- sixth direction / sixth-power gate
- higher residual の再帰分解
- generic `k`-direction hypergraph / support tower library
- NearWaveBudget の解析評価
- prime-counting / PNT / sieve / asymptotic
- induction / descent
- full-cover contradiction
- Legendre conjecture / RH の証明主張

L067 の役割は、L066 で抽出した `support.card >= 5` trigger を **実際の fifth prime direction と fifth-power gate、および既存 support-cost ledger の追加 1 charge** に変換することだけである。
