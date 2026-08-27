# instruction-083 — PRIM-L063 Near First-Prime Fiber / Product-Wave Capacity

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `68bbdfb525c62cfe64c1dc8ad141712bf9b14b8a`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L062` は **Outcome A+ — LOW-COST RESIDUAL SPLIT COMPLETE** として受理する。

現在 Lean では

```text
LowCostResidual
  = Near
  + NonCollisionDepth
  + Fourth

LowCostResidual
  + 3*Terminal
  + 5*Collision
  <= PairOverlap
  <= CoprimePrimePairOverlapCapacity
```

が確定している。

また

```text
NonCollisionDepth.card <= L018 prime-square depth budget
```

も既にある。

したがって、低コスト枝の中で現在もっとも裸なのは `Near` である。

L042 の Near gate は exact に

```text
key=(p,(q,s))
p < q < s
p,q,s are odd active primes
p*q*s <= 2*n
```

であり、既存 theorem

```lean
paritySafeTripleGateNear_canonical_cube_lt_two_mul
```

から

```text
p^3 < 2*n
```

も確定している。

今回の bounded target は **Near を first-prime `p` ごとの有限 pair fiber に分解し、その fiber の product-wave occupancy を explicit finite capacity にすること**だけである。

Near を消す、漸近評価する、解析的 sieve を導入する、Fourth へ進む、Legendre を閉じる、という checkpoint ではない。

---

## 1. 新規 module

推奨:

```text
DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeNearFirstPrimeWaveCapacity.lean
```

`ParitySafeLowCostResidualSplit` を import してよい。

完了時に `DkMath.NumberTheory.Legendre` facade へ import を追加する。

---

## 2. L063.1 — near first-prime gate

Near key の first prime だけを取り出す有限集合を定義する。

候補:

```lean
noncomputable def paritySafeNearFirstPrimes (n : ℕ) : Finset ℕ :=
  (paritySafeTripleGatePrimes n).filter
    (fun p => p ^ 3 < 2 * n)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeNearFirstPrimes
    {n p : ℕ} :
    p ∈ paritySafeNearFirstPrimes n ↔
      p ∈ paritySafeTripleGatePrimes n ∧
      p ^ 3 < 2 * n := by
  ...
```

必須 consumer:

```lean
theorem paritySafeTripleGateNear_firstPrime_mem
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateNearTriples n) :
    p ∈ paritySafeNearFirstPrimes n := by
  ...
```

ここでは既存

```lean
paritySafeTripleGateNear_canonical_cube_lt_two_mul
```

を使う。cube-root / `Nat.sqrt` / real root は導入しない。

---

## 3. L063.2 — first-prime pair fiber

first prime `p` を固定した Near ordered pair `(q,s)` を定義する。

推奨形:

```lean
noncomputable def paritySafeNearPrimePairsAtFirst
    (n p : ℕ) : Finset (ℕ × ℕ) :=
  ((squareAnchorOddActivePrimes n).product
      (squareAnchorOddActivePrimes n)).filter
    (fun qs =>
      p < qs.1 ∧
      qs.1 < qs.2 ∧
      p * qs.1 * qs.2 ≤ 2 * n)
```

membership theorem を追加する。

必須の exact key characterization:

```lean
@[simp] theorem mem_paritySafeTripleGateNearTriples_iff_firstPrime_pair
    {n p q s : ℕ} :
    (p,(q,s)) ∈ paritySafeTripleGateNearTriples n ↔
      p ∈ paritySafeNearFirstPrimes n ∧
      (q,s) ∈ paritySafeNearPrimePairsAtFirst n p := by
  ...
```

### 注意

reverse direction では

```text
p ∈ NearFirstPrimes
```

から `p ∈ paritySafeTripleGatePrimes n` が取れるので、NearTriples の元定義へ戻せる。

generic triple/hypergraph abstractionは作らない。

---

## 4. L063.3 — exact first-prime key-card decomposition

Near triple key の cardinality を first-prime fiber sum として exact に表す。

目標:

```lean
theorem paritySafeTripleGateNearTriples_card_eq_sum_firstPrime_pairFibers
    (n : ℕ) :
    (paritySafeTripleGateNearTriples n).card =
      ∑ p ∈ paritySafeNearFirstPrimes n,
        (paritySafeNearPrimePairsAtFirst n p).card := by
  ...
```

proof engineering 上、直接の `Finset` sum が重ければ、theorem-local に

```text
NearFirstPrimePairIncidences
```

のような薄い incidence Finset を置き、key と `(p,(q,s))` の明示 bijection で閉じてよい。

ただし generic sigma/hypergraph library は作らない。

---

## 5. L063.4 — Near product-wave capacity

Near は Far と違い、一つの product key が shell 内で複数 seat を持ち得る。
したがって key-card だけではなく wave occupancy を保持する。

first-prime fiber 表現の budget を定義する。

候補:

```lean
noncomputable def paritySafeNearFirstPrimeWaveBudget (n : ℕ) : ℕ :=
  ∑ p ∈ paritySafeNearFirstPrimes n,
    ∑ qs ∈ paritySafeNearPrimePairsAtFirst n p,
      (squareWaveOffsets n (p * qs.1 * qs.2)).card
```

さらに Near key 上の同じ budget と exact に一致させる。

候補 theorem:

```lean
theorem paritySafeNearFirstPrimeWaveBudget_eq_nearTriple_sum
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      ∑ key ∈ paritySafeTripleGateNearTriples n,
        (squareWaveOffsets n
          (paritySafeTripleProductModulus key)).card := by
  ...
```

association / tuple normalization が重ければ、L063.3 の incidence helper を再利用してよい。

---

## 6. L063.5 — actual Near residual card <= Near wave budget

今回の main structural consumer。

必須:

```lean
theorem paritySafeCanonicalNearResidualTripleIncidences_card_le_nearFirstPrimeWaveBudget
    (n : ℕ) :
    (paritySafeCanonicalNearResidualTripleIncidences n).card ≤
      paritySafeNearFirstPrimeWaveBudget n := by
  ...
```

推奨 proof spine:

actual Near residual incidence

```text
(r,(q,s))
```

を

```text
((canonicalPrime(n,r),(q,s)), r)
```

へ送る。

既存 API:

```lean
mem_paritySafeCanonicalNearResidualTripleIncidences
paritySafeCanonicalResidualTripleIncidence_mem_productWave
```

から

```text
key ∈ NearTriples
r ∈ squareWaveOffsets n (productModulus key)
```

を得る。

map は `r` と `(q,s)` を保持するので incidence 上では injective。

Near upper incidence Finset を theorem-local または public に定義してよい。

Far の `wave.card <= 1` は使わない。Near では一般に multiple seats を許すことが本質である。

---

## 7. L063.6 — exact arithmetic form of Near budget

既存 theorem

```lean
card_squareWaveOffsets_eq_div_add_carry
```

を各 Near key に適用し、budget を exact arithmetic sum にする。

目標形:

```lean
theorem paritySafeNearFirstPrimeWaveBudget_eq_div_add_carry
    (n : ℕ) :
    paritySafeNearFirstPrimeWaveBudget n =
      ∑ p ∈ paritySafeNearFirstPrimes n,
        ∑ qs ∈ paritySafeNearPrimePairsAtFirst n p,
          ((2 * n) / (p * qs.1 * qs.2) +
            squareWaveCarry n (p * qs.1 * qs.2)) := by
  ...
```

product positivity は active-prime membership から取る。

### 非目標

この checkpoint では

```text
squareWaveCarry <= 1
harmonic/log estimate
prime counting estimate
sum 1/(p*q*s)
```

等の解析的圧縮は不要。

既存 API があり一行で得られる場合だけ補助 theorem として追加可。

---

## 8. L063.7 — LowCostResidual upper-control consumer

L062:

```text
LowCostResidual = Near + NonCollisionDepth + Fourth
```

と

```text
NonCollisionDepth <= L018DepthBudget
```

今回の

```text
Near <= NearWaveBudget
```

を合成する。

必須:

```lean
theorem paritySafeLowCostResidualMass_le_nearWaveBudget_add_L018Depth_add_fourth
    (n : ℕ) :
    paritySafeLowCostResidualMass n ≤
      paritySafeNearFirstPrimeWaveBudget n +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  ...
```

これは contradiction theorem ではない。

意味は、低コスト三枝のうち

```text
Near                -> explicit finite product-wave budget
NonCollisionDepth   -> L018 prime-square budget
Fourth              -> still raw fourth-direction card
```

まで整理された、ということだけである。

---

## 9. regression / false-beam

Near branch が空集合だと誤認しないため、軽い concrete witness を一つ残してよい。

候補:

```text
n = 101
key = (3,(5,7))
3*5*7 = 105 <= 202
```

`3,5,7` は `101` の odd active primes なので Near key の concrete example になる。

ただし `squareWaveOffsets 101 105` の full enumeration が重い場合は mandatory ではない。

新しい `native_decide` は使わない。

---

## 10. 禁止事項

今回禁止:

- Near key -> seat injectivity の主張
- Near wave card `<= 1` の主張
- Far API の無理な再利用
- generic hypergraph / sigma library
- analytic sieve
- PNT / Mertens / harmonic asymptotics
- new fourth-direction counting
- fifth direction
- residual recursion / descent
- global contradiction
- Legendre / RH conclusion

Near は multiple-seat branch として扱う。

---

## 11. heartbeat policy

- global `maxHeartbeats` を増やさない。
- tuple/sum normalization で重い場合は、まず explicit incidence helper に分解する。
- theorem-local heartbeat increase は、数学的に薄い `Finset` transport 一件に限る。
- `nextSeat` / cofactor の重い unfolding は今回不要。

---

## 12. Outcome

### Outcome A+ — NEAR FIRST-PRIME WAVE CAPACITY

以下が閉じる:

1. Near first-prime gate
2. first-prime pair fiber
3. exact Near key-card fiber decomposition
4. Near first-prime wave budget
5. actual Near residual card <= budget
6. div+carry exact arithmetic form
7. LowCostResidual upper-control consumer
8. facade / report / docstrings

### Outcome A — NEAR STRUCTURAL CAPACITY

1--5 と 7 が閉じ、div+carry の二重 sum normalization だけが軽微な engineering boundary。

### Outcome E — FINSET FIBER ENGINEERING BLOCK

Near membership equivalenceは閉じるが、card/sum fiber transport が elaboration 上の blocker。

この場合、解析へ逃げず explicit incidence Finset に分解した地点で STOP。

### Outcome C — FALSE

以下のどれかに concrete counterexample:

- Near key membership equivalence
- actual Near incidence -> Near product-wave incidence
- claimed first-prime fiber partition

---

## 13. STOP

今回の checkpoint は

```text
Near
  -> first prime p with p^3 < 2n
  -> ordered pair fiber (q,s), p*q*s <= 2n
  -> product-wave occupancy
  -> explicit finite NearWaveBudget

Near.card <= NearWaveBudget
```

まで。

その後に初めて、

```text
NearWaveBudget をさらに圧縮するか
Fourth branch を数えるか
```

を比較する。
