# instruction-064 — PRIM-L049 Far-Key Unique Shell Representative / Exact Survival Count

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `69b0af18682087db93ac9a8e86c8e426adf985bf`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L048` は **Outcome A+ — Canonical-Minimum Exclusion / Rough Cofactor Selector** として受理する。

L048 までで、far key

```text
key := (p,(q,s))
m := paritySafeTripleProductModulus key = p*q*s
t := paritySafeFarProductWaveCofactor n key r
```

に対する actual far residual incidence は exact に

```text
r ∈ squareWaveOffsets n m
Nat.Coprime (2*n) t
∀ a ∈ squareAnchorOddActivePrimes n, a < p → ¬ a ∣ t
```

へ書き換えられた。

また far key では `2*n < m` なので、既存 L042 により wave occupancy は `≤ 1`。
今回の目的は、この `≤ 1` を単なる cardinal bound のまま残さず、shell 内の唯一の候補 multiple を **明示式** で固定し、rough selector fiber を `{r₀}` または `∅` の二択へ潰すことである。

核心は

```text
t₀ := n^2 / m + 1
r₀ := m*t₀ - n^2
```

である。

`t₀` は `n^2` を厳密に越える最初の `m`-multiple の quotient、`r₀` はその shell offset である。
`m > 2*n` なので square shell `(n^2, n^2+2*n]` に `m` の multiple が存在するなら、それは必ず `m*t₀` の一個だけである。

今回ここを exact finite arithmetic として閉じる。

---

## 1. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival
```

ファイル:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarProductWaveSurvival.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
```

だけを使う。

facade:

```text
DkMath.NumberTheory.Legendre
```

へ追加する。

generic interval / floor libraryを新設しない。必要ならこの module 内に小さい private Nat lemma を置く。

---

## 2. canonical next multiple data

### L049.1 next quotient

```lean
def paritySafeFarProductWaveNextQuotient
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ :=
  n ^ 2 / paritySafeTripleProductModulus key + 1
```

### L049.2 next seat

```lean
def paritySafeFarProductWaveNextSeat
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ :=
  paritySafeTripleProductModulus key *
      paritySafeFarProductWaveNextQuotient n key - n ^ 2
```

### L049.3 shell-fit predicate

Prop でよい。

```lean
def ParitySafeFarProductKeyFitsShell
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Prop :=
  paritySafeTripleProductModulus key *
      paritySafeFarProductWaveNextQuotient n key ≤
    n ^ 2 + 2 * n
```

必要なら `[DecidablePred]` は infer させる。Bool 化しない。

---

## 3. far wave quotient uniqueness — 第一主定理

far key `(p,(q,s))` と arbitrary wave hit `r` について、L047 cofactor

```text
t := (n^2+r)/(p*q*s)
```

が canonical next quotient `t₀` と一致することを証明する。

目標:

```lean
theorem paritySafeFarProductWaveCofactor_eq_nextQuotient
    {n p q s r : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p*q*s)) :
    paritySafeFarProductWaveCofactor n (p,(q,s)) r =
      paritySafeFarProductWaveNextQuotient n (p,(q,s)) := by
  ...
```

数学的には、`m := p*q*s`, `N := n^2` として

```text
N < m*t = N+r ≤ N+2*n < N+m
```

だから

```text
N/m < t < N/m + 2
```

となり `t = N/m + 1`。

Nat division API が直接噛み合わない場合だけ、local private lemma を置いてよい。概念形:

```lean
private theorem eq_div_add_one_of_mul_in_next_window
    {N m t : ℕ}
    (hm : 0 < m)
    (hlo : N < m*t)
    (hhi : m*t < N+m) :
    t = N/m + 1 := by
  ...
```

この lemma を generic public API に昇格させない。

---

## 4. next seat / wave の exact singleton law

L049.3 から、far key に対して wave membership 自体を明示 seat に同定する。

strongly preferred target:

```lean
theorem mem_squareWaveOffsets_farKey_iff_eq_nextSeat
    {n p q s r : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    r ∈ squareWaveOffsets n (p*q*s) ↔
      ParitySafeFarProductKeyFitsShell n (p,(q,s)) ∧
      r = paritySafeFarProductWaveNextSeat n (p,(q,s)) := by
  ...
```

必要な方向:

### wave hit → fit + equality

- L049.3 で quotient `t=t₀`。
- factorization `m*t=n^2+r`。
- `r≤2*n` から fit。
- `m*t₀-n^2=r`。

### fit → next seat is wave hit

- division algorithmから `n^2 < m*t₀`。
- fitから `m*t₀≤n^2+2*n`。
- よって `1≤r₀≤2*n`。
- `n^2+r₀=m*t₀`。
- したがって `r₀ ∈ squareWaveOffsets n m`。

Nat subtractionの bookkeeping が重ければ、このためだけの local lemma は可。

さらに数行なら:

```lean
theorem squareWaveOffsets_farKey_eq_if_singleton
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    squareWaveOffsets n (p*q*s) =
      if ParitySafeFarProductKeyFitsShell n (p,(q,s)) then
        {paritySafeFarProductWaveNextSeat n (p,(q,s))}
      else ∅ := by
  ...
```

これは optional ではなく、membership iff が閉じたなら strongly preferred。

---

## 5. next-seat cofactor value

fit の下で、next seat の L047 cofactor が `t₀` そのものであることを expose する。

```lean
theorem paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hfit : ParitySafeFarProductKeyFitsShell n (p,(q,s))) :
    paritySafeFarProductWaveCofactor n (p,(q,s))
        (paritySafeFarProductWaveNextSeat n (p,(q,s))) =
      paritySafeFarProductWaveNextQuotient n (p,(q,s)) := by
  ...
```

L049.3 と fit→wave theoremから出せるならそれを再利用する。

---

## 6. explicit far-key survival predicate

L048 rough selector の三条件を、唯一候補 `t₀,r₀` の算術条件へ移す。

```lean
def ParitySafeFarProductKeySurvives
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Prop :=
  ParitySafeFarProductKeyFitsShell n key ∧
    Nat.Coprime (2*n) (paritySafeFarProductWaveNextQuotient n key) ∧
    ∀ a ∈ squareAnchorOddActivePrimes n,
      a < key.1 →
        ¬ a ∣ paritySafeFarProductWaveNextQuotient n key
```

**重要:** ここへ `canonicalSupportPrime`、candidate membership、wave membership を再導入しない。
この predicate は `n`, key, division, coprimality, finite active-prime exclusion だけで完結させる。

---

## 7. rough fiber = singleton or empty — strongest local theorem

far key ごとに:

```lean
theorem paritySafeFarProductWaveRoughOffsets_eq_if_survives
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveRoughOffsets n (p,(q,s)) =
      if ParitySafeFarProductKeySurvives n (p,(q,s)) then
        {paritySafeFarProductWaveNextSeat n (p,(q,s))}
      else ∅ := by
  ...
```

少なくとも membership iff は必須:

```lean
r ∈ paritySafeFarProductWaveRoughOffsets n key
  ↔ ParitySafeFarProductKeySurvives n key ∧
     r = paritySafeFarProductWaveNextSeat n key
```

これにより既存 `card ≤ 1` を **exact 0/1 law** へ強化する。

```lean
theorem paritySafeFarProductWaveRoughOffsets_card_eq_if_survives
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    (paritySafeFarProductWaveRoughOffsets n (p,(q,s))).card =
      if ParitySafeFarProductKeySurvives n (p,(q,s)) then 1 else 0 := by
  ...
```

---

## 8. surviving far-key Finset / global exact count

```lean
noncomputable def paritySafeSurvivingFarProductKeys (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeTripleGateFarTriples n).filter
    (ParitySafeFarProductKeySurvives n)
```

membership simp theoremを置く。

L048 exact rough-fiber sum と L049.7 の 0/1 law を使い、今回の strongest global theorem:

```lean
theorem paritySafeCanonicalFarResidual_card_eq_survivingFarProductKeys_card
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeSurvivingFarProductKeys n).card := by
  ...
```

を閉じる。

これが今回の主到達点。

意味は:

```text
actual far residual mass
= sum of 0/1 rough fibers
= number of far product keys satisfying one explicit finite survival predicate
```

である。

ここではまだ surviving key の総数を数値的に評価しない。

---

## 9. optional A+: nontrivial quotient forces half-scale first prime

L048 の

```text
paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
```

と L047 cofactor packet の `2*t < n+2` を unique next seatへ適用し、survivalした far keyについて

```text
t₀ = 1 ∨ 2*p < n+2
```

を得られるなら追加する。

概念形:

```lean
theorem paritySafeFarProductKeySurvives_nextQuotient_one_or_key_halfScale
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hsurv : ParitySafeFarProductKeySurvives n (p,(q,s))) :
    paritySafeFarProductWaveNextQuotient n (p,(q,s)) = 1 ∨
      2*p < n+2 := by
  ...
```

これは次 checkpoint で terminal `t₀=1` / recharge `t₀>1` split を作る入口になる。

数行〜20行程度なら Outcome A+ とする。重ければ Outcome A で止める。

---

## 10. arithmetic sanity witnesses

既存 witness を unique-quotient viewへ固定する。

最低限、数行の `norm_num` で閉じるなら:

```text
n=16, key=(3,7,13): m=273, t₀=1, r₀=17
n=62, key=(3,5,37): m=555, t₀=7, r₀=41
n=62, key=(3,11,17): m=561, t₀=7, r₀=83
n=17, key=(3,5,7): m=105, t₀=3, r₀=26
```

全て typed residual membership を再証明する必要はない。next quotient / next seat arithmetic の sanity check で十分。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- surviving key count の asymptotic / harmonic evaluation
- PNT / Mertens / Rosser / Jacobsthal / analytic sieve / RH
- generic rough-number counting library
- fourth/fifth/k-direction hypergraph
- smaller-anchor `SquareOffsetsFullyCovered`
- induction / infinite descent
- global contradiction / Legendre proof declaration
- all far keys surviveしない、または surviving keys = 0 の主張
- terminal/recharge の大規模 split（§9 の小 theorem を除く）
- repository-wide Nat division refactor

この checkpoint は **far product wave の唯一 shell representative と exact survival predicate** だけを固定する。

---

## 12. Outcome 判定

### Outcome A+ — UNIQUE FAR-KEY SURVIVAL / HALF-SCALE CONSUMER

必須:

1. next quotient / next seat / fit predicate。
2. arbitrary far wave hit の quotient = next quotient。
3. wave membership ↔ fit + next-seat equality。
4. next-seat cofactor = next quotient。
5. explicit `ParitySafeFarProductKeySurvives`。
6. rough fiber = singleton/empty または同値な exact membership + 0/1 card law。
7. `far residual card = surviving far-key card`。
8. §9 の `t₀=1 ∨ 2*p<n+2` consumer。

### Outcome A — UNIQUE FAR-KEY SURVIVAL COUNT

1〜7 が exact に閉じる。§9 は未実装または current API 上重い。

### Outcome B — UNIQUE REPRESENTATIVE ONLY

1〜4 は閉じるが、rough selector との exact survival rewrite で Finset / Decidable bookkeeping が過大。
その場合は unique representative theorem と exact gap を report し、無理に abstraction を増やさない。

### Outcome C — FORMULA GAP

`n^2/m+1` が current `squareWaveOffsets` semantics と一致しない、または boundary `≤ n^2+2*n` / Nat subtraction に実質的な反例がある。
その場合は最小反例と正しい boundary formula を report し、誤った theorem を弱めて通さない。

---

## 13. 検証

実装後:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source のみ:

```text
sorry
admit
axiom
native_decide
```

を監査する。

既存 repository の known `sorry` は今回の判定対象外。

---

## 14. レポート

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-far-product-wave-survival-260826.md
```

最低限:

1. Outcome A+/A/B/C。
2. next quotient / next seat formula。
3. far wave unique representative theorem。
4. rough fiber singleton/empty exact law。
5. surviving far-key cardinal equality。
6. §9 を実装したか。
7. arithmetic witnesses。
8. 禁止事項を越えていないこと。
9. build / audit 結果。
