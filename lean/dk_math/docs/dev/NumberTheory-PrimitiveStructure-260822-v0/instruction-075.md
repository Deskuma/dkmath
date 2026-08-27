# instruction-075 — PRIM-L060 Terminal Exact Support / Disjoint Support-Cost Ledger

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `59d8776e08b2b9581cc35373bd5119ef0759b50b`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L059` は **Outcome A+ — FOUR-DIRECTION GATE** として受理する。

L059 では

```text
Depth collision
  -> canonical p ∈ FourDirectionGatePrimes

ExactFourth + witness(p,q)
  -> p ∈ FourDirectionGatePrimes
```

を閉じ、`p^4 < squareBody n` という genuine fourth-root scale restriction を得た。
また L058 で未回収だった

```text
3 * CollisionSeats.card <= SupportExcess
```

も回収済みである。

今回 FourDirectionGate の first-prime fiber counting には進まない。同じ first prime が複数 seat / pair を所有し得るため、gate membership だけでは cardinal gain にならない。

今回の bounded target は、global residual ledger に残る別 branch `Terminal` を、その固有条件

```text
next quotient = 1
```

を使って **exact support card = 3** まで落とし、L059 collision support cost と disjoint に合成することだけである。

---

## 1. 数学的核

terminal surviving far key

```text
key = (p,(q,s))
```

では L050 より

```text
n^2 < p*q*s <= n^2 + 2*n
nextQuotient n key = 1.
```

その唯一の far-wave seat を

```text
r := paritySafeFarProductWaveNextSeat n key
```

とすると、L049/L047 selector route から `r` は actual parity-safe far residual seat へ戻る。

terminal なので point は完全に

```text
n^2 + r = p*q*s
```

である。

`p,q,s` は distinct active primes で point を割る。
逆に active-support prime `a` が `n^2+r` を割れば

```text
a | p*q*s.
```

`a` は prime なので prime-dvd-mul を二回使って

```text
a = p or a = q or a = s.
```

従って terminal seat では

```text
paritySafeActiveSupport n r = {p,q,s}
```

か、少なくとも exact card theorem

```text
(paritySafeActiveSupport n r).card = 3
```

が成立する。

よって local support excess は exactly `2`。

一方 L059 depth-fiber collision seat は

```text
4 <= (paritySafeActiveSupport n r).card.
```

なので terminal seat と collision seat は disjoint である。

従って support-excess 全体に対して、二つの cost を二重計上せず

```text
2 * TerminalSeats.card
+ 3 * CollisionSeats.card
<= SupportExcess
```

を同時に charge できる。

terminal key -> seat が injective なら

```text
TerminalKeys.card = TerminalSeats.card
```

なので最終的に

```text
2 * TerminalKeys.card
+ 3 * CollisionSeats.card
<= SupportExcess
```

まで得る。

これが今回の主 consumer である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeTerminalSupportCost.lean
```

import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate
```

L046/L047/L049/L050 API は import chain を優先する。必要なら direct import を追加してよい。

完成後 facade `DkMath.NumberTheory.Legendre` へ import を追加する。

---

## 3. L060.1 — terminal seat packet

terminal key から next seat を actual far residual seat へ戻す薄い packet を公開する。

推奨 shape:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_seat_packet
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      (r,(q,s)) ∈ paritySafeCanonicalFarResidualTripleIncidences n ∧
      p = paritySafeCanonicalSupportPrime n r ∧
      n ^ 2 + r = p*q*s := by
  ...
```

証明 spine:

1. terminal membership -> surviving far key + `nextQuotient=1`。
2. surviving predicate -> next seat が rough selector membership。
3. L048 rough = canonical selector。
4. L047 `paritySafeCanonicalFarProductWaveOffset_mem_farResidual`。
5. canonical selector packet から first prime ownership。
6. L047/L049 cofactor factorization + `nextQuotient=1` から `n^2+r=p*q*s`。

既存 API の tuple association に合わせ theorem shape は調整可。

---

## 4. L060.2 — terminal seat image / injectivity

terminal seat image を定義する。

```lean
noncomputable def paritySafeTerminalFarProductSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeTerminalSurvivingFarProductKeys n).image
    (paritySafeFarProductWaveNextSeat n)
```

membership theoremを付ける。

次に fixed-seat uniqueness を証明する。

必須 target:

```lean
theorem paritySafeTerminalFarProductWaveNextSeat_injectiveOn
    {n : ℕ} :
    Set.InjOn
      (paritySafeFarProductWaveNextSeat n)
      (paritySafeTerminalSurvivingFarProductKeys n : Set (ℕ × (ℕ × ℕ))) := by
  ...
```

推奨 route:

- `key₁=(p₁,(q₁,s₁))`, `key₂=(p₂,(q₂,s₂))` が同一 seat `r`。
- L060.1 で両方 actual far residual incidence。
- canonical ownership より `p₁=p₂=canonicalPrime n r`。
- terminal なので両 far cofactor / next quotient は `1`。
- 既存 L046
  `paritySafeFarTripleCofactor_value_local_injective`
  を同一 seat / equal cofactor で使い `q₁=q₂`, `s₁=s₂`。
- key equality。

generic unique-factorization lemma を新設しない。

これより mandatory:

```lean
theorem paritySafeTerminalFarProductSeats_card_eq_terminalKeys
    (n : ℕ) :
    (paritySafeTerminalFarProductSeats n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card := by
  ...
```

向きは Lean の扱いやすい方でよい。

---

## 5. L060.3 — terminal exact support

今回の算術核。

必須 theorem の第一候補:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_eq
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    paritySafeActiveSupport n r = {p,q,s} := by
  ...
```

Finset notation / simp が不自然なら、以下の二本でも A+ 判定可。

```lean
p ∈ activeSupport n r ∧ q ∈ activeSupport n r ∧ s ∈ activeSupport n r
```

と

```lean
∀ a ∈ activeSupport n r, a = p ∨ a = q ∨ a = s
```

から exact card theorem:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

proof spine:

1. L060.1 actual residual packet から `p,q,s` active support membership / distinctness。
2. terminal point equation `n^2+r=p*q*s`。
3. `a ∈ activeSupport` -> `a` prime and `a | n^2+r`。
4. rewrite point equation, `Nat.Prime.dvd_mul` で `a|p*q` or `a|s`、さらに `a|p` or `a|q`。
5. prime divisibilityから equality。
6. p<q<s により三点 distinct、card=3。

---

## 6. L060.4 — terminal seats are exact-support-three

image seat 側へ transportする。

推奨:

```lean
theorem paritySafeTerminalFarProductSeat_activeSupport_card_eq_three
    {n r : ℕ}
    (hr : r ∈ paritySafeTerminalFarProductSeats n) :
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

また terminal seat は parity-safe covered candidate であることも公開する。

```lean
theorem paritySafeTerminalFarProductSeats_subset_coveredCandidates
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ⊆ paritySafeCoveredCandidates n := by
  ...
```

---

## 7. L060.5 — terminal support cost

terminal seat では support.card = 3 なので local support excess は `2`。

必須:

```lean
theorem two_mul_terminalFarProductSeats_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalFarProductSeats n).card <=
      paritySafeSupportExcess n := by
  ...
```

proof spine:

1. terminal seats subset parity-safe candidates。
2. 各 terminal seat で `support.card - 1 = 2`。
3. `2 * card = sum_terminal 2`。
4. subset sum で candidate 全体の `support.card -1` へ charge。

card equality と合成して key 版も必須:

```lean
theorem two_mul_terminalSurvivingFarProductKeys_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card <=
      paritySafeSupportExcess n := by
  ...
```

---

## 8. L060.6 — terminal / collision disjointness

L059 collision は support.card >=4、terminal は exactly 3。

必須:

```lean
theorem paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
    (n : ℕ) :
    Disjoint
      (paritySafeTerminalFarProductSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  ...
```

これは support cost の二重計上を防ぐ重要 theorem。

---

## 9. L060.7 — combined disjoint support-cost ledger

今回の main global consumer。

必須:

```lean
theorem two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card <=
        paritySafeSupportExcess n := by
  ...
```

推奨 proof:

- terminal key card = terminal seat card。
- terminal/collision seat disjointness。
- union 上の local cost sumとして
  - terminal seat term = 2
  - collision seat term >=3
- union subset `squareAnchorOddPointCoprimeOffsets n`。
- candidate-side `paritySafeSupportExcess` sumへ transport。

L059 の二つの個別 inequality を単純加算してはならない。同じ `SupportExcess` を二回使う誤りになる。**必ず disjoint union / single sum で証明する。**

A+ target として軽ければ weighted residual consumer を追加してよい。
例えば L057/L058 global ledger と組み合わせ、terminal cost を support side に明示した inequality。ただし Nat division を導入しない。

---

## 10. regression witnesses

### 10.1 n=16 terminal

既存 L049 witness:

```text
n=16
key=(3,(7,13))
nextQuotient=1
nextSeat=17
16^2+17=273=3*7*13
```

がある。

軽く閉じるなら:

```lean
theorem paritySafeTerminalSupport_regression_16 :
    (3,(7,13)) ∈ paritySafeTerminalSurvivingFarProductKeys 16 ∧
      paritySafeFarProductWaveNextSeat 16 (3,(7,13)) = 17 ∧
      paritySafeActiveSupport 16 17 = {3,7,13} := by
  ...
```

または card = 3 まででよい。

### 10.2 disjoint regression

L057/L058 `n=58,r=101` collision は support.card >=4 なので terminal seat ではないことを general disjointnessから corollary にしてよい。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- FourDirectionGate first-prime fiber counting
- `TerminalKeys.card <= number of active primes` のような根拠のない first-prime injection
- generic unique-factorization framework
- generic 3-hypergraph / 4-hypergraph
- fifth direction
- near branch counting
- analytic sieve / PNT / Mertens / asymptotics
- smaller anchor / descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

特に個別 theorem

```text
2*T <= SupportExcess
3*C <= SupportExcess
```

を単純加算して

```text
2*T + 3*C <= SupportExcess
```

としてはならない。combined theorem は terminal/collision seat の disjointness を使った **一つの support-excess sum** から証明する。

---

## 12. Outcome 判定

### Outcome A+ — TERMINAL EXACT SUPPORT / DISJOINT COST

1. terminal seat packet / point equation
2. terminal key -> seat injection
3. terminal seat image card = terminal key card
4. terminal active support exact `{p,q,s}` または同等の exact card=3 theorem
5. terminal seats subset covered candidate
6. `2 * TerminalKeys.card <= SupportExcess`
7. terminal seats disjoint collision seats
8. `2*TerminalKeys.card + 3*CollisionSeats.card <= SupportExcess`
9. n=16 regression
10. facade import / report

### Outcome A — TERMINAL SUPPORT COST

1,4,5,6 を完成し terminal exact support cost は閉じる。
seat injectivity / combined disjoint ledger の一部が Lean surface 上重い場合は obstacle を report して停止する。

### Outcome B — TERMINAL EXACT SUPPORT ONLY

terminal point equationと support.card=3 は閉じるが、global seat image/cost transportが不自然。

### Outcome C — FALSE

terminal actual seatで active support に `p,q,s` 以外の prime が存在する concrete counterexample、または terminal key -> next seat injectivityを壊す concrete counterexample が出た場合。

---

## 13. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 / 修正 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

---

## 14. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-terminal-support-cost-260826.md
```

最低限:

1. Outcome
2. terminal seat / point packet
3. terminal seat injectivity
4. exact support = three directions
5. terminal support cost
6. terminal/collision disjointness
7. combined support-cost ledger
8. n=16 regression
9. non-goals
10. validation

を記録する。

---

## STOP

今回の終了地点は次。

```text
Terminal key (p,q,s)
  -> exact seat r
  -> n^2+r = p*q*s
  -> ActiveSupport(n,r) = {p,q,s}
  -> support.card = 3

TerminalKeys.card = TerminalSeats.card

TerminalSeats ⟂ DepthCollisionSeats

2 * TerminalKeys.card
+ 3 * DepthCollisionSeats.card
<= SupportExcess
```

ここで停止する。

次 checkpoint で初めて、combined support-cost を global residual inequalityへどう組み込むか、または Near branch の product-wave capacityへ進むかを比較する。