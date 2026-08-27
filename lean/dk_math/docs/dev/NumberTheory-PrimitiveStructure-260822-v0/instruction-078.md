# instruction-078 — PRIM-L060T Terminal Seat Injection / Disjoint Support-Cost Closure

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `c55d49ea5dd9514083a62d2c55989366dddc7eae`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060S` は **Outcome A — TERMINAL EXACT-SUPPORT CLOSURE** として受理する。

L060S で engineering blocker は解消した。新しい definition-local API

```lean
@[simp] theorem mem_paritySafeActiveSupport_iff_dvd
```

を `ParitySafeIncidenceBalance.lean` に追加したことで、Terminal module 内で `paritySafeActiveSupport` を unfold せずに

```text
terminal key=(p,(q,s))
  -> p,q,s ∈ activeSupport at nextSeat
  -> every u ∈ activeSupport is p or q or s
  -> activeSupport.card = 3
```

まで通常 heartbeat で閉じた。

今回の bounded target は、元 instruction-075 の後半だけを回収することである。

```text
Terminal key
  -> unique terminal seat
  -> support.card = 3

Depth collision seat
  -> support.card >= 4

therefore TerminalSeats ∩ CollisionSeats = ∅

2 * TerminalKeys.card
+ 3 * CollisionSeats.card
<= SupportExcess
```

**Near、FourGate fiber counting、第五方向、新しい residual 分解には進まない。**

---

## 1. 既存確定 API

今回の proof は以下を consumer として使う。

### L060S

```lean
paritySafeTerminalSurvivingFarProductKey_residual_seat
paritySafeTerminalSurvivingFarProductKey_point_eq
paritySafeTerminalSurvivingFarProductKey_prime_packet
paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
mem_paritySafeActiveSupport_iff_dvd
```

### L046

```lean
paritySafeFarTripleCofactor_value_local_injective
paritySafeFarTripleCofactor_packet
```

### L058/L059

```lean
paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
three_mul_depthFiberCollisionSeats_card_le_supportExcess
```

後者の個別 inequality は regression / comparison 用であり、最終 combined theorem の proof では単純加算しない。

---

## 2. L060T.1 — terminal seat image

`ParitySafeTerminalSupportCost.lean` を継続編集する。

terminal key の next seat image を定義する。

```lean
noncomputable def paritySafeTerminalFarProductSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeTerminalSurvivingFarProductKeys n).image
    (paritySafeFarProductWaveNextSeat n)
```

membership theorem を追加する。

候補:

```lean
@[simp] theorem mem_paritySafeTerminalFarProductSeats
    {n r : ℕ} :
    r ∈ paritySafeTerminalFarProductSeats n ↔
      ∃ key ∈ paritySafeTerminalSurvivingFarProductKeys n,
        paritySafeFarProductWaveNextSeat n key = r := by
  ...
```

tuple association が扱いづらければ `Finset.mem_image` を直接 consumer してもよい。

---

## 3. L060T.2 — terminal key → seat injectivity

必須:

```lean
theorem paritySafeTerminalFarProductWaveNextSeat_injectiveOn
    {n : ℕ} :
    Set.InjOn
      (paritySafeFarProductWaveNextSeat n)
      (paritySafeTerminalSurvivingFarProductKeys n : Set (ℕ × (ℕ × ℕ))) := by
  ...
```

### 推奨 proof spine

`key₁=(p₁,(q₁,s₁))`, `key₂=(p₂,(q₂,s₂))` とし、同じ next seat `r` を持つとする。

1. 両 terminal key に `paritySafeTerminalSurvivingFarProductKey_prime_packet` を適用。
2. canonical ownership と seat equality から

   ```text
   p₁ = canonicalPrime(n,r) = p₂
   ```

   を得る。
3. `paritySafeTerminalSurvivingFarProductKey_residual_seat` から両方を同じ seat `r` の actual residual incidence に rewrite。
4. terminal membership → surviving far membership から、両 residual pair の canonical triple key が `paritySafeTripleGateFarTriples n` に属することを得る。
5. `paritySafeFarTripleCofactor_packet` と L060S point equation

   ```text
   n^2+r = p*q*s
   ```

   から各 seat-local far cofactor が exactly `1` であることを示す。

   薄い helper を追加してよい:

   ```lean
   theorem paritySafeTerminalSurvivingFarProductKey_farTripleCofactor_eq_one ... :
     paritySafeFarTripleCofactor n r q s = 1 := by
     ...
   ```

   ここでは `r = nextSeat ...` を statement に直接入れてもよい。
6. L046

   ```lean
   paritySafeFarTripleCofactor_value_local_injective
   ```

   を同一 seat / cofactor `1=1` で使い、`q₁=q₂`, `s₁=s₂`。
7. `p₁=p₂` と合わせ key equality。

### 禁止

- generic unique factorization theoremを新設しない。
- terminal product equalityから新しい ordered-prime-triple factorization frameworkを作らない。
- first-prime mapだけの injectivityを仮定しない。

---

## 4. L060T.3 — terminal seat card = terminal key card

injectivity から image card exact を閉じる。

必須:

```lean
theorem paritySafeTerminalFarProductSeats_card_eq_terminalKeys
    (n : ℕ) :
    (paritySafeTerminalFarProductSeats n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card := by
  ...
```

向きは Lean の扱いやすい方でよい。

`Finset.card_image_iff` / `Finset.card_image_of_injective` / `Finset.card_congr` など current Mathlib にある最短 API を使う。

---

## 5. L060T.4 — terminal seat consumer surface

image witness を unpack して L060S theorem を seat 側へ transportする。

必須:

```lean
theorem paritySafeTerminalFarProductSeat_activeSupport_card_eq_three
    {n r : ℕ}
    (hr : r ∈ paritySafeTerminalFarProductSeats n) :
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

さらに candidate subset:

```lean
theorem paritySafeTerminalFarProductSeats_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  ...
```

推奨 route:

- image witness `key=(p,(q,s))` を取る。
- L060 residual-seat theorem。
- `mem_paritySafeCanonicalFarResidualTripleIncidences` → residual incidence packet から candidate membership。

covered candidate subset まで取れるなら追加してよいが、今回の global support sum は `squareAnchorOddPointCoprimeOffsets` 上なので mandatory ではない。

---

## 6. L060T.5 — terminal support cost

terminal seat では support.card=3 なので

```text
support.card - 1 = 2.
```

必須 seat version:

```lean
theorem two_mul_terminalFarProductSeats_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalFarProductSeats n).card ≤
      paritySafeSupportExcess n := by
  ...
```

proof:

1. `2 * seats.card = ∑ r∈TerminalSeats, 2`。
2. 各 seat で L060T.4 より `support.card - 1 = 2`。
3. TerminalSeats subset candidate。
4. `paritySafeSupportExcess` の一つの candidate sumへ subset transport。

card equalityから key versionも追加:

```lean
theorem two_mul_terminalSurvivingFarProductKeys_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card ≤
      paritySafeSupportExcess n := by
  ...
```

ただしこれは次の combined theorem の代用ではない。

---

## 7. L060T.6 — TerminalSeats / CollisionSeats disjointness

L060S:

```text
terminal seat -> support.card = 3
```

L058:

```text
collision seat -> support.card >= 4
```

なので disjoint。

必須:

```lean
theorem paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
    (n : ℕ) :
    Disjoint
      (paritySafeTerminalFarProductSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  ...
```

proof は `Finset.disjoint_left` で seat `r` を仮定し、card=3 と card>=4 を `omega` で矛盾させればよい。

また combined sum に必要なので collision seats subset candidate を local/public helper として追加してよい。

候補:

```lean
theorem paritySafeRechargeExactDepthFiberCollisionSeats_subset_candidate
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  ...
```

既存 L059 `three_mul_depthFiberCollisionSeats_card_le_supportExcess` の proof spine を再利用する。

---

## 8. L060T.7 — combined disjoint support-cost ledger

今回の main theorem。

必須:

```lean
theorem two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  ...
```

### 必須 proof discipline

個別 theorem

```text
2*T <= SupportExcess
3*C <= SupportExcess
```

を足してはならない。

必ず seat domain 上の **一つの disjoint union sum** から証明する。

推奨:

```text
TSeats := paritySafeTerminalFarProductSeats n
CSeats := paritySafeRechargeExactDepthFiberCollisionSeats n
f(r) := activeSupport.card - 1
```

1. `Disjoint TSeats CSeats`。
2. `TSeats ∪ CSeats ⊆ squareAnchorOddPointCoprimeOffsets n`。
3. terminal seat では `f(r)=2`。
4. collision seat では `3≤f(r)`。
5. よって

   ```text
   2*TSeats.card + 3*CSeats.card
     <= ∑ r∈TSeats∪CSeats, f(r)
     <= ∑ r∈candidate, f(r)
     = SupportExcess.
   ```

6. L060T.3 で `TSeats.card = TerminalKeys.card` に rewrite。

必要なら中間 theorem を分ける:

```lean
theorem two_mul_terminalSeats_add_three_mul_collisionSeats_le_supportExcess ...
```

を先に閉じ、最後に key-card equality を rewriteする方を推奨する。

---

## 9. regressions

### n=16 Terminal

既存:

```text
key=(3,(7,13))
nextSeat=17
support.card=3
```

から軽ければ

```lean
17 ∈ paritySafeTerminalFarProductSeats 16
```

を固定する。

### n=58 collision disjoint

既存 actual collision `r=101` と general disjointness から

```text
101 ∉ paritySafeTerminalFarProductSeats 58
```

を軽く閉じられるなら regression として追加してよい。

どちらも長い enumeration は不要。

---

## 10. heartbeat 方針

L060S で membership bridge が通ったので、今回 `paritySafeActiveSupport` を直接 unfold してはならない。

- 通常 heartbeat を優先。
- local helper 一つだけ重い場合のみ `set_option maxHeartbeats 800000 in` まで可。
- global unlimited heartbeatは禁止。
- timeoutした場合は exact theorem を消して compiling surface に戻し、どの step が blocker か reportする。

---

## 11. 非目標

今回は以下を行わない。

- Near branch counting
- FourDirectionGate first-prime fiber counting
- DepthResidualPairCapacityExcess の再帰分解
- ExactFourth の新しい cardinal estimate
- fifth direction
- generic unique-factorization / hypergraph library
- analytic sieve / PNT / asymptotics
- smaller anchor / descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

---

## 12. Outcome

### Outcome A+ — TERMINAL DISJOINT SUPPORT-COST CLOSURE

1. TerminalSeats image
2. terminal next-seat injectivity
3. `TerminalSeats.card = TerminalKeys.card`
4. terminal seat support.card=3
5. TerminalSeats subset candidate
6. `2*TerminalKeys.card <= SupportExcess`
7. TerminalSeats disjoint CollisionSeats
8. combined single-sum theorem

   ```text
   2*TerminalKeys.card + 3*CollisionSeats.card <= SupportExcess
   ```

9. report / facade remains clean

### Outcome A — TERMINAL SEAT COST

1–6 complete。combined disjoint ledger の Finset union transport のみ engineering obstacle。

### Outcome B — TERMINAL INJECTION ONLY

1–3 complete。seat support transport または support-cost sum で blocker。

### Outcome E — ENGINEERING BLOCK

terminal key→seat injectivity の cofactor surface が current API では重すぎる。counterexample ではないことを reportし、compiled spineを保持。

### Outcome C — FALSE

terminal key→nextSeat injectivity の concrete counterexample、または Terminal seat と Collision seat の実 intersection が見つかった場合。

---

## STOP

今回の終了地点は次。

```text
TerminalKeys.card = TerminalSeats.card

Terminal seat
  -> support.card = 3

TerminalSeats ∩ CollisionSeats = ∅

2*TerminalKeys.card
+ 3*CollisionSeats.card
<= SupportExcess
```

ここで停止する。

この closure の後に初めて、Near branch または remaining residual-capacity / Fourth branch のどちらを次に消費するか比較する。
