# instruction-079 — PRIM-L060U Direct Terminal Support-Key Reconstruction / Seat-Card Closure

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `42eb8c49d0ce65c4833cb2d667bde3bc78eab9e3`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L060T` は **Outcome E — ENGINEERING BLOCK** として受理する。

現在 Lean で確定しているもの:

```text
terminal key=(p,(q,s))
  -> next terminal seat r
  -> p,q,s ∈ ActiveSupport(n,r)
  -> every u ∈ ActiveSupport(n,r) is p or q or s
  -> ActiveSupport(n,r).card = 3

TerminalSeats := image nextSeat TerminalKeys
```

L060T で失敗したのは `nextSeat` injectivity の数学的反例ではなく、
L046 `paritySafeFarTripleCofactor_value_local_injective` へ接続する proof の
`whnf` elaboration である。通常 heartbeat / local `800000` の双方で timeout した。

今回の bounded target は **cofactor API を完全に使わず**、L060S で既に compiled API となった exact three-support surface だけから terminal key を seat から復元することである。

今回 combined support-cost ledger へは進まない。

---

## 1. 最重要禁止事項

injectivity proof では以下を使わない。

```text
paritySafeFarTripleCofactor_value_local_injective
paritySafeFarTripleCofactor
paritySafeFarTripleCofactor_packet
paritySafeFarProductWaveCofactor_*
```

これらは L060T の `whnf` blocker を再導入するためである。

また generic unique-factorization framework、新しい ordered-prime factorization library を作らない。

今回使う数学は **same seat の exact active support と order だけ**。

---

## 2. 既存 consumer API

`ParitySafeTerminalSupportCost.lean` から以下を使う。

```lean
paritySafeTerminalSurvivingFarProductKey_prime_packet
paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport
paritySafeTerminalSurvivingFarProductKey_activeSupport_cases
paritySafeTerminalSurvivingFarProductKey_activeSupport_card_eq_three
paritySafeTerminalFarProductSeats
mem_paritySafeTerminalFarProductSeats
```

prime packet は terminal key `(p,(q,s))` に対して

```text
p,q,s ∈ OddActivePrimes
p < q < s
p = canonicalSupportPrime n (nextSeat key)
```

を与える。

---

## 3. L060U.1 — explicit scalar same-seat uniqueness

`Set.InjOn` を最初に書かない。

まず tuple coercion / function whnf を避けた explicit scalar theorem を閉じる。

推奨 shape:

```lean
theorem paritySafeTerminalKeys_components_eq_of_nextSeat_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁, (q₁, s₁)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (h₂ : (p₂, (q₂, s₂)) ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (hseat :
      paritySafeFarProductWaveNextSeat n (p₁, (q₁, s₁)) =
        paritySafeFarProductWaveNextSeat n (p₂, (q₂, s₂))) :
    p₁ = p₂ ∧ q₁ = q₂ ∧ s₁ = s₂ := by
  ...
```

### proof spine

#### 3.1 first prime

両 prime packet から

```text
p₁ = canonicalPrime(n,seat₁)
p₂ = canonicalPrime(n,seat₂)
```

を得る。

`hseat` を `congrArg (paritySafeCanonicalSupportPrime n)` へ通して

```text
p₁ = p₂
```

を得る。

`nextSeat` の definition を unfold しない。

#### 3.2 transport q₂,s₂ into support of key₁ seat

`paritySafeTerminalSurvivingFarProductKey_three_mem_activeSupport h₂` から

```text
q₂,s₂ ∈ ActiveSupport(n,seat₂)
```

を得る。

`hseat` だけで rewrite し

```text
q₂,s₂ ∈ ActiveSupport(n,seat₁)
```

へ transportする。

ここでも `ActiveSupport` は unfold しない。

#### 3.3 use key₁ support cases

L060S

```lean
paritySafeTerminalSurvivingFarProductKey_activeSupport_cases h₁
```

を `q₂`, `s₂` に使い

```text
q₂ = p₁ ∨ q₂ = q₁ ∨ q₂ = s₁
s₂ = p₁ ∨ s₂ = q₁ ∨ s₂ = s₁
```

を得る。

prime packet の

```text
p₁ < q₁ < s₁
p₂ < q₂ < s₂
p₁ = p₂
```

だけで `omega` case split し、

```text
q₂ = q₁
s₂ = s₁
```

を決定する。

ここが今回の数学的核。

### 注意

support equality `{p,q,s}` 自体を再証明しなくてよい。
`activeSupport_cases` はすでに compiled theorem なので、その consumer に徹する。

---

## 4. L060U.2 — explicit key equality theorem

components theorem から薄く key equality を作る。

```lean
theorem paritySafeTerminalKeys_eq_of_nextSeat_eq
    {n : ℕ}
    {key₁ key₂ : ℕ × (ℕ × ℕ)}
    (h₁ : key₁ ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (h₂ : key₂ ∈ paritySafeTerminalSurvivingFarProductKeys n)
    (hseat : paritySafeFarProductWaveNextSeat n key₁ =
      paritySafeFarProductWaveNextSeat n key₂) :
    key₁ = key₂ := by
  rcases key₁ with ⟨p₁,q₁,s₁⟩
  rcases key₂ with ⟨p₂,q₂,s₂⟩
  obtain ⟨hp,hq,hs⟩ :=
    paritySafeTerminalKeys_components_eq_of_nextSeat_eq h₁ h₂ hseat
  subst p₂
  subst q₂
  subst s₂
  rfl
```

実際の nested pair destructuring syntax は current Lean に合わせる。

この theorem 自体で `nextSeat` を unfold しない。

---

## 5. L060U.3 — finite-domain injectivity wrapper

explicit equality theorem が通常 heartbeat で通った後だけ、wrapper を追加する。

第一候補:

```lean
theorem paritySafeTerminalFarProductWaveNextSeat_injectiveOn
    {n : ℕ} :
    Set.InjOn
      (paritySafeFarProductWaveNextSeat n)
      (paritySafeTerminalSurvivingFarProductKeys n : Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb hab
  exact paritySafeTerminalKeys_eq_of_nextSeat_eq ha hb hab
```

もしこの **wrapper statement 自体** が `whnf` timeout するなら、無理に保持しない。
その場合は次節の card proof を `Finset.card_image_iff` / `Finset.card_bij` の finite-domain equality premiseで直接閉じる。

重要なのは `Set.InjOn` theorem 名を得ることではなく

```text
TerminalSeats.card = TerminalKeys.card
```

を得ること。

---

## 6. L060U.4 — TerminalSeats.card = TerminalKeys.card

mandatory target:

```lean
theorem paritySafeTerminalFarProductSeats_card_eq_terminalKeys
    (n : ℕ) :
    (paritySafeTerminalFarProductSeats n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card := by
  ...
```

`paritySafeTerminalFarProductSeats` はすでに `Finset.image` である。

current Mathlib の最短 API を使う。
候補:

- `Finset.card_image_iff`
- `Finset.card_image_of_injective`
- `Finset.card_congr`
- `Finset.card_bij`

`Set.InjOn` wrapper が重い場合は explicit theorem
`paritySafeTerminalKeys_eq_of_nextSeat_eq` を直接 injectivity premise に与える。

### 向き

最終 theorem の向きは上記を優先するが、Lean API が自然なら

```text
TerminalKeys.card = TerminalSeats.card
```

でも可。docstring で exact equality と分かればよい。

---

## 7. regression

n=16 の既存 terminal keyを使い、軽ければ seat image membership を固定する。

```lean
theorem paritySafeTerminalFarProductSeat_regression_16 :
    17 ∈ paritySafeTerminalFarProductSeats 16 := by
  ...
```

既存 `(3,(7,13))` が TerminalKeys へ実際に入る theorem が API 上見えていない場合、長い membership enumeration はしない。

regression は optional。

---

## 8. Outcome

### Outcome A+ — DIRECT TERMINAL SEAT INJECTION

1. explicit scalar component uniqueness
2. explicit key equality from same seat
3. finite-domain injectivity wrapper（または同等の direct finite proof）
4. `TerminalSeats.card = TerminalKeys.card`
5. no cofactor API in the injectivity proof

### Outcome A — CARD EQUALITY WITHOUT SET WRAPPER

1,2,4 が閉じる。
`Set.InjOn` wrapper だけが elaboration surface 上重いが、finite card equality は explicit uniqueness theorem から閉じる。

### Outcome E2 — NEXTSEAT STATEMENT ENGINEERING BLOCK

explicit scalar theorem

```text
terminal h₁ h₂ + nextSeat equality -> component equality
```

自体が、cofactor API を一切使わないにもかかわらず `whnf` timeout する。

この場合は failed theorem を残さず report して STOP。
次 checkpoint では `nextSeat` を opaque coordinate wrapper / local abbreviation へ隔離するかを判断する。

### Outcome C — FALSE

concrete terminal keys `key₁ ≠ key₂` が同じ next seat を持つことを Lean / finite computation で確認した場合。

---

## 9. 禁止事項 / 非目標

今回は以下を行わない。

- L046 cofactor injectivity route の再試行
- global heartbeat increase / unlimited heartbeat
- combined support-cost ledger
- terminal/collision disjointness
- terminal seat support-cost inequality
- Near branch counting
- FourDirectionGate fiber counting
- ExactFourth の新 counting
- fifth direction
- generic factorization / graph / hypergraph
- analytic estimate / PNT / sieve
- descent / induction
- global contradiction
- Legendre conjecture / RH claim

今回の目的はただ一つ:

```text
same terminal seat
  -> same terminal key
  -> TerminalSeats.card = TerminalKeys.card
```

を **L060S exact-support APIだけで**閉じること。

---

## 10. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTerminalSupportCost
lake build DkMath.NumberTheory.Legendre
git diff --check
```

変更 Lean source に

```text
sorry
admit
axiom
native_decide
```

がないことを確認する。

---

## 11. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-terminal-direct-seat-injection-260827.md
```

最低限:

1. Outcome
2. L060T whnf blocker recap
3. direct exact-support uniqueness strategy
4. component equality theorem
5. key equality / injectivity surface
6. terminal key-seat card equality
7. cofactor API unused confirmation
8. validation
9. remaining boundary

を記録する。

---

## STOP

今回の終了点:

```text
TerminalKeys
  --nextSeat injective via exact support--> TerminalSeats

TerminalSeats.card = TerminalKeys.card
```

ここで停止する。

次 checkpoint で初めて

```text
Terminal support.card = 3
Collision support.card >= 4
```

を使った disjoint weighted support-cost ledgerへ戻る。
