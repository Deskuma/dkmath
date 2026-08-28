# instruction-076 — PRIM-L060R Terminal Support Proof Decomposition / Heartbeat Repair

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `95c6933ccfda848f1a79470c721f0b98f035c1b8`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060` は **partial / pre-Outcome-B — TERMINAL SEAT SPINE** として受理する。

現在すでに次は Lean で閉じている。

```text
terminal key
  -> canonical far residual seat

n^2 + nextSeat = p*q*s

n=16, key=(3,(7,13)), nextSeat=17
```

一方 instruction-075 の Outcome B でも必須だった

```text
terminal activeSupport.card = 3
```

は未完了である。

report にある heartbeat は数学的 counterexample ではなく、`Finset` / coercion / support 定義を大きな theorem 内で一度に reduce した際の elaboration engineering obstacle と判断する。

今回の bounded target は **新しい数学へ進まず L060 を小分割して完走すること**である。

---

## 1. 重要方針 — exact Finset equality を最初に狙わない

次を一発で証明しようとして heartbeat を消費してはならない。

```lean
paritySafeActiveSupport n r = {p,q,s}
```

代わりに proof surface を次へ分割する。

```text
(A) p,q,s ∈ activeSupport
(B) every a ∈ activeSupport is p or q or s
(C) {p,q,s}.card = 3
(D) card sandwich

3 = {p,q,s}.card
  <= activeSupport.card
  <= {p,q,s}.card = 3
```

これだけで mandatory theorem

```text
activeSupport.card = 3
```

が閉じる。

exact Finset equality は card theorem 後に軽く閉じる場合のみ追加する。

---

## 2. 修正対象

原則として既存 module を継続編集する。

```text
DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeTerminalSupportCost.lean
```

新しい generic support / factorization module は作らない。

facade import は既に存在するので維持する。

---

## 3. L060R.1 — terminal seat packet を一段だけ強化

既存 theorem:

```lean
paritySafeTerminalSurvivingFarProductKey_residual_seat
paritySafeTerminalSurvivingFarProductKey_point_eq
```

を再利用し、必要なら薄い packet を追加する。

推奨:

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

推奨 spine:

1. existing residual-seat theorem。
2. `mem_paritySafeCanonicalFarResidualTripleIncidences` から base residual incidence。
3. L041 `paritySafeCanonicalResidualTripleIncidence_packet` から candidate seat。
4. existing `terminal_canonical_seat` と
   `mem_paritySafeCanonicalFarProductWaveOffsets` の canonical-owner field から
   `p = canonicalSupportPrime n r`。
5. existing point equation。

tuple association は current API に合わせて調整可。

この packet を後続 theorem で何度も巨大 destructuring しないための boundary とする。

---

## 4. L060R.2 — 三つの support membership を独立 theorem にする

mandatory:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    let r := paritySafeFarProductWaveNextSeat n (p,(q,s))
    p ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r := by
  ...
```

優先 route:

- seat packet の residual incidence `hinc`。
- `paritySafeCanonicalResidualTripleIncidence_packet hinc` から
  `p,q,s` の active-prime / divisibility packet。
- candidate seat では

```lean
squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
```

が使える。

`q,s` について erased quotient support から active support へ戻す既存 L041/L059 と同じ短い route を再利用してよい。

あるいは `paritySafeActiveSupport` を **各 membership goal だけ局所的に** unfold し、

```text
prime is active
prime divides n^2+r
```

を入れてもよい。

module 全体の support equality を `simp [paritySafeActiveSupport]` で処理しない。

---

## 5. L060R.3 — support の任意要素は p/q/s のどれか

今回の heartbeat repair の中心。

mandatory:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_cases
    {n p q s a : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (ha : a ∈ paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p,(q,s)))) :
    a = p ∨ a = q ∨ a = s := by
  ...
```

proof spine:

1. `r := nextSeat` を局所 `let` してもよい。
2. `ha` の `paritySafeActiveSupport` membership を **この hypothesis だけ** unpack。
   - `a ∈ squareAnchorOddActivePrimes n`
   - `SquareOffsetForbiddenBy n a r`
3. active membership から `Nat.Prime a`。
4. `SquareOffsetForbiddenBy` から `a ∣ n^2+r`。
5. existing terminal point equationで

```text
a ∣ p*q*s
```

へ rewrite。
6. `Nat.Prime.dvd_mul` を二回使う。

```text
a|p*q or a|s
(a|p or a|q) or a|s
```

7. terminal residual packet から `p,q,s` も prime。
8. `Nat.dvd_prime` と `a.ne_one` で divisibility を equality へ変換。

ここでは generic unique-factorization lemma を作らない。

もし `SquareOffsetForbiddenBy` unfold が重い場合、既存

```lean
mem_paritySafeActiveWaveOffsets_iff_dvd
```

を利用する thin bridge を一つ置いてよい。

例:

```lean
theorem mem_paritySafeActiveSupport_iff_active_and_dvd
    {n r a : ℕ} :
    a ∈ paritySafeActiveSupport n r ↔
      a ∈ squareAnchorOddActivePrimes n ∧ a ∣ n^2+r := by
  simp [paritySafeActiveSupport, SquareOffsetForbiddenBy]
```

ただしこの bridge が単独 build で軽く閉じる場合のみ追加する。

---

## 6. L060R.4 — exact card=3 は subset/card sandwich で閉じる

まず local subset を作る。

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_subset_three
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p,(q,s))) ⊆ {p,q,s} := by
  intro a ha
  rcases paritySafeTerminalSurvivingFarProductKey_activeSupport_cases hkey ha with
    rfl | rfl | rfl <;> simp
```

逆 inclusion:

```lean
{p,q,s} ⊆ paritySafeActiveSupport n r
```

は L060R.2 から作る。

L041 residual packet の distinctness

```text
p != q
p != s
q != s
```

を使い

```text
({p,q,s} : Finset ℕ).card = 3
```

を閉じる。

mandatory card theorem:

```lean
theorem paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n) :
    (paritySafeActiveSupport n
      (paritySafeFarProductWaveNextSeat n (p,(q,s)))).card = 3 := by
  ...
```

proof は equality rewrite ではなく

```text
card {p,q,s} <= card activeSupport
card activeSupport <= card {p,q,s}
card {p,q,s} = 3
```

の sandwich を `Finset.card_le_card` + `omega` で閉じる。

A+ target として、この後 cheap なら exact Finset equality を追加してよい。

---

## 7. L060R.5 — terminal seat image

exact support が閉じてから image layer へ進む。

```lean
noncomputable def paritySafeTerminalFarProductSeats
    (n : ℕ) : Finset ℕ :=
  (paritySafeTerminalSurvivingFarProductKeys n).image
    (paritySafeFarProductWaveNextSeat n)
```

membership theorem を追加。

mandatory:

```lean
theorem paritySafeTerminalFarProductSeat_activeSupport_card_eq_three
    {n r : ℕ}
    (hr : r ∈ paritySafeTerminalFarProductSeats n) :
    (paritySafeActiveSupport n r).card = 3 := by
  ...
```

mandatory subset:

```lean
theorem paritySafeTerminalFarProductSeats_subset_candidate
    (n : ℕ) :
    paritySafeTerminalFarProductSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
  ...
```

strongly preferred:

```lean
paritySafeTerminalFarProductSeats n ⊆ paritySafeCoveredCandidates n
```

covered は support card=3 から nonempty を作ればよい。

---

## 8. L060R.6 — terminal key -> seat injectivity

exact support theoremとは独立に、既存 L046 local injectivity を consumer する。

mandatory target:

```lean
theorem paritySafeTerminalFarProductWaveNextSeat_injectiveOn
    {n : ℕ} :
    Set.InjOn
      (paritySafeFarProductWaveNextSeat n)
      (paritySafeTerminalSurvivingFarProductKeys n : Set (ℕ × (ℕ × ℕ))) := by
  ...
```

推奨 route:

- `key₁=(p₁,(q₁,s₁))`, `key₂=(p₂,(q₂,s₂))`。
- same seat `r`。
- L060R.1 から両 key の first prime は same canonical prime、従って `p₁=p₂`。
- 両方 terminal なので local far cofactor は `1`。
- existing L046

```lean
paritySafeFarTripleCofactor_value_local_injective
```

を同じ seat `r`、equal cofactor `1` で使い `(q₁,s₁)=(q₂,s₂)`。
- key equality。

もし `paritySafeFarTripleCofactor = 1` bridge が L046 API 上重い場合、**この theorem 内だけ**で point equations

```text
p*q₁*s₁ = n²+r = p*q₂*s₂
```

から `p` を cancel し、ordered prime pair uniqueness を局所 proof してよい。

generic unique-factorization frameworkは作らない。

これより mandatory:

```lean
theorem paritySafeTerminalFarProductSeats_card_eq_terminalKeys
    (n : ℕ) :
    (paritySafeTerminalFarProductSeats n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card := by
  ...
```

`Finset.card_image_iff` / `card_image_of_injective` 等 current Mathlib API に合わせる。

---

## 9. L060R.7 — terminal cost

terminal seat card=3 より local support excessは exactly 2。

mandatory:

```lean
theorem two_mul_terminalFarProductSeats_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalFarProductSeats n).card ≤
      paritySafeSupportExcess n := by
  ...
```

proof:

```text
2*T.card
  = sum_{r in T} 2
  = sum_{r in T} (support.card - 1)
  <= sum_{candidate r} (support.card - 1)
  = SupportExcess
```

image card equality と合成して key 版も mandatory:

```lean
theorem two_mul_terminalSurvivingFarProductKeys_card_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card ≤
      paritySafeSupportExcess n := by
  ...
```

---

## 10. L060R.8 — terminal / collision disjointness

mandatory:

```lean
theorem paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats
    (n : ℕ) :
    Disjoint
      (paritySafeTerminalFarProductSeats n)
      (paritySafeRechargeExactDepthFiberCollisionSeats n) := by
  ...
```

proof は support cardだけでよい。

```text
terminal seat -> support.card = 3
collision seat -> support.card >= 4
```

---

## 11. L060R.9 — combined support-cost ledger

最終 mandatory target:

```lean
theorem two_mul_terminalKeys_add_three_mul_collisionSeats_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  ...
```

**個別 inequality を単純加算してはならない。**

heartbeat を避けるため、次の三段に分けることを推奨する。

### 11.1 terminal exact local sum

```text
2*TSeats.card
  = sum_{r in TSeats} (support.card - 1)
```

### 11.2 collision lower local sum

```text
3*CSeats.card
  <= sum_{r in CSeats} (support.card - 1)
```

L059 `collision_support_card_ge_four` を使う。

### 11.3 disjoint union transport

terminal/collision disjointnessから

```text
sum_T f + sum_C f
  = sum_{T ∪ C} f
  <= sum_candidate f
  = SupportExcess
```

を閉じる。

大きな `if r ∈ ... then ... else ...` weighted sum は作らない。

---

## 12. heartbeat policy

### 必須

- global `set_option maxHeartbeats 0` は禁止。
- module 全体の heartbeat limit を無制限化しない。
- proof decomposition を先に行う。
- heavy `simp` / `aesop` / full Finset equality unfolding を避ける。

### 許可

小分割後も **一つの theorem だけ** current default を僅かに超える場合、局所的に

```lean
set_option maxHeartbeats 800000 in
```

程度を付けてよい。

既存 L042 に同様の局所 heartbeat annotation があるため、これは engineering boundary として許容する。

ただし 800000 でも閉じない theorem を force しない。その場合は、その theorem より一段手前の packet までを report し Outcome を下げる。

---

## 13. regression

mandatory:

```text
n=16
key=(3,(7,13))
nextSeat=17
activeSupport.card = 3
```

strongly preferred:

```text
activeSupport 16 17 = {3,7,13}
```

これは既存 L041 witnessにも同じ exact support equality があるので、一般 theorem の回帰として reuse 可能。

---

## 14. 禁止事項 / 非目標

今回は以下を行わない。

- Near branch へ進む
- FourDirectionGate first-prime fiber counting
- fifth direction
- generic unique-factorization framework
- generic hypergraph
- analytic sieve / PNT / Mertens
- smaller-anchor descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

今回の仕事は **L060 を heartbeat-safe な proof surface へ分解して完走することだけ**である。

---

## 15. Outcome 判定

### Outcome A+ — L060 REPAIRED / DISJOINT COST COMPLETE

1. terminal seat packet
2. p/q/s support membership
3. arbitrary support member cases
4. terminal support card=3
5. terminal seat image / candidate subset
6. terminal key -> seat injectivity
7. terminal seat card = terminal key card
8. terminal support cost
9. terminal/collision disjointness
10. combined disjoint support-cost ledger
11. n=16 regression

### Outcome A — TERMINAL SUPPORT COST COMPLETE

1–5 と terminal support cost を完成。
seat injectivity / combined disjoint ledger のどちらかが local Lean surface 上まだ重い場合。

### Outcome B — TERMINAL EXACT SUPPORT COMPLETE

1–4 を完成し `support.card=3` は閉じるが、image/cost transport が unresolved。

### Outcome C — FALSE

terminal actual seatで support.card≠3 の concrete counterexample、または terminal key -> seat injectivityの concrete counterexampleを得た場合。

### Outcome P — ENGINEERING PARTIAL

数学的 counterexampleは無いが、L060R.3/L060R.4 の小分割後も heartbeat / elaboration obstacleで `support.card=3` に到達しない場合。

その場合は **どの最小 theorem が閉じ、どの次の theorem が heartbeat になるか**を exact に report して停止する。

---

## 16. validation

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
lake build DkMath.NumberTheory.Legendre
git diff --check
```

修正 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

---

## 17. report

既存 report を更新するか、repair report を追加する。

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-terminal-support-cost-repair-260826.md
```

最低限:

1. Outcome
2. heartbeat root cause
3. seat packet
4. three-membership packet
5. support cases theorem
6. card sandwich
7. seat injection strategy
8. terminal cost
9. terminal/collision disjointness
10. combined cost ledger
11. n=16 regression
12. remaining boundary
13. validation

---

## STOP

今回の終了地点は最大でも次。

```text
Terminal key
  -> exact support card = 3
  -> unique terminal seat coordinate
  -> cost 2 per terminal seat

Depth collision seat
  -> support card >= 4
  -> cost >= 3

TerminalSeats ∩ CollisionSeats = ∅

2*TerminalKeys.card + 3*CollisionSeats.card
  <= SupportExcess
```

ここで停止する。

Near branch / global obstruction へは次 checkpoint で初めて進む。