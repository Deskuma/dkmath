# instruction-065 — PRIM-L050 Terminal / Recharge Split / Sqrt-Scale First Prime

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `813f652e36478a9fef0f5708b06ba33142044138`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L049` は **Outcome A+ — UNIQUE FAR-KEY SURVIVAL / HALF-SCALE CONSUMER** として受理する。

L049 までで far key

```text
key := (p,(q,s))
m   := paritySafeTripleProductModulus key = p*q*s
t₀  := paritySafeFarProductWaveNextQuotient n key
r₀  := paritySafeFarProductWaveNextSeat n key
```

について、far wave / rough selector は完全に一席へ圧縮された。

```text
roughOffsets key = {r₀}  if key survives
                 = ∅     otherwise
```

さらに

```text
FarResidual.card = paritySafeSurvivingFarProductKeys.card
```

が exact に成立し、surviving key には

```text
t₀ = 1 ∨ 2*p < n+2
```

がある。

今回の目的は surviving-key world 自体を

```text
terminal : t₀ = 1
recharge : 1 < t₀
```

へ exact に二分し、recharge branch の第一 prime `p` を **sqrt-scale**

```text
p^2 ≤ n
```

まで押し下げることである。

これは smaller-anchor descent ではない。同じ anchor `n` の有限 key universe に対する scale gate である。

---

## 1. 数学的核

### terminal branch

`t₀ = n^2 / m + 1` なので、positive modulus `m` の下で

```text
t₀ = 1  ↔  n^2 < m
```

である。

survival の shell-fit は

```text
m*t₀ ≤ n^2 + 2*n
```

なので terminal では単に

```text
n^2 < m ≤ n^2 + 2*n
```

となる。

また `t₀ = 1` なら

```text
Coprime (2*n) 1
```

と smaller-prime roughness は自動である。

従って far key の terminal survival は **triple product 自身が square shell に入ること**と exact に一致するはずである。

### recharge branch

`1 < t₀` の surviving key では L048/L049 により

```text
p ≤ t₀
```

を得られる。

一方 far triple gate は `p < q < s` なので

```text
p^3 < p*q*s = m
```

である。

したがって

```text
p^4 < m*t₀
```

であり、survival shell-fit から

```text
m*t₀ ≤ n^2 + 2*n < (n+1)^2
```

なので

```text
p^4 < (n+1)^2
```

となる。

自然数ではこれから

```text
p^2 ≤ n
```

が従う。

これが今回の主たる新しい scale gate である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarProductKeyRecharge.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSurvival
```

だけを使う。

facade `DkMath.NumberTheory.Legendre` へ import する。

---

## 3. L050.1 terminal / recharge surviving keys

次を置く。

```lean
noncomputable def paritySafeTerminalSurvivingFarProductKeys
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeSurvivingFarProductKeys n).filter
    (fun key => paritySafeFarProductWaveNextQuotient n key = 1)

noncomputable def paritySafeRechargeSurvivingFarProductKeys
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeSurvivingFarProductKeys n).filter
    (fun key => 1 < paritySafeFarProductWaveNextQuotient n key)
```

それぞれ membership simp theorem を置く。

`paritySafeFarProductWaveNextQuotient` は definition 上 positive なので、surviving key は必ずどちらか一方に入る。

証明するもの:

```lean
paritySafeTerminalRechargeSurvivingFarProductKeys_disjoint
paritySafeTerminalRechargeSurvivingFarProductKeys_union
```

union は

```text
terminal ∪ recharge = surviving
```

とする。

---

## 4. L050.2 exact residual-card split

上の partition と L049 の

```text
FarResidual.card = SurvivingKeys.card
```

を接続し、

```lean
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeSurvivingFarProductKeys n).card := by
  ...
```

を閉じる。

これで far residual mass の terminal/recharge split を exact ledger として固定する。

---

## 5. L050.3 terminal branch = triple product in shell

far key `(p,(q,s))` に対して、まず局所 theorem として

```lean
theorem paritySafeFarProductWaveNextQuotient_eq_one_iff_anchor_sq_lt_modulus
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    paritySafeFarProductWaveNextQuotient n (p,(q,s)) = 1 ↔
      n^2 < p*q*s := by
  ...
```

を証明する。

`m>0` は gate prime packet から供給する。

そのうえで terminal membership を arithmetic interval に exact 化する。

strongly preferred theorem:

```lean
theorem mem_paritySafeTerminalSurvivingFarProductKeys_iff_product_in_shell
    {n p q s : ℕ} :
    (p,(q,s)) ∈ paritySafeTerminalSurvivingFarProductKeys n ↔
      (p,(q,s)) ∈ paritySafeTripleGateFarTriples n ∧
      n^2 < p*q*s ∧
      p*q*s ≤ n^2 + 2*n := by
  ...
```

逆向きでは:

1. `n^2 < m` から `t₀=1`。
2. 上端から shell-fit。
3. `Coprime (2*n) 1` は simp。
4. smaller active prime `a` について `¬ a ∣ 1` は `Nat.Prime a` から閉じる。
5. よって `ParitySafeFarProductKeySurvives`。

この theorem により terminal branch から `survival` predicate も `nextQuotient` も消える。

数行なら次も追加してよい。

```lean
theorem paritySafeTerminalSurvivingFarProductKey_nextSeat_eq_product_sub_square
    ... :
    paritySafeFarProductWaveNextSeat n (p,(q,s)) = p*q*s - n^2 := by
  ...
```

---

## 6. L050.4 sqrt-scale active-prime world

same-anchor finite world として次を定義する。

```lean
noncomputable def paritySafeSqrtScaleActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter (fun p => p^2 ≤ n)
```

membership:

```lean
@[simp] theorem mem_paritySafeSqrtScaleActivePrimes
    {n p : ℕ} :
    p ∈ paritySafeSqrtScaleActivePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧ p^2 ≤ n := by
  ...
```

これは新しい anchor universe ではない。同じ `n` における active prime の finite subworld である。

---

## 7. L050.5 recharge first-prime sqrt gate — 主定理

最低限、次を閉じる。

```lean
theorem paritySafeRechargeSurvivingFarProductKey_firstPrime_sq_le_anchor
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p^2 ≤ n := by
  ...
```

証明方針:

1. recharge membership から

   ```text
   far gate membership
   survival
   1 < t₀
   ```

   を得る。
2. L049 の unique next seat を rough selector に戻す。
3. L048

   ```text
   paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
   ```

   と

   ```text
   paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
   ```

   から `p ≤ t₀`。
4. gate packet `p<q<s` と prime positivityから

   ```text
   p^3 < p*q*s
   ```

   を得る。local arithmetic lemmaでよい。
5. `p>0` と `p≤t₀` を使い

   ```text
   p^4 < (p*q*s)*t₀
   ```

6. survival shell-fitから

   ```text
   (p*q*s)*t₀ ≤ n^2+2*n
   ```

7. `n^2+2*n < (n+1)^2`。
8. もし `n < p^2` なら `n+1 ≤ p^2` なので平方して矛盾。
9. `p^2 ≤ n`。

`nlinarith` / `omega` を局所的に使ってよい。generic sqrt API や real-valued square root は導入しない。

続けて finite-world membership まで公開する。

```lean
theorem paritySafeRechargeSurvivingFarProductKey_firstPrime_mem_sqrtScale
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p ∈ paritySafeSqrtScaleActivePrimes n := by
  ...
```

active membership は far gate packet から得る。

### 重要な解釈

L049 の half-scale

```text
2*p < n+2
```

より今回の

```text
p^2 ≤ n
```

の方が本質的に強い scale compression である。

ただし「sqrt(n) を新 anchor にする」「その anchor で cover を仮定する」という話ではない。

---

## 8. L050.6 strongly preferred A+ — recharge keys を sqrt-scale first prime で fiberize

主定理が軽く閉じた場合、recharge key を第一 prime ごとに整理する。

```lean
noncomputable def paritySafeRechargeFarProductKeysAtPrime
    (n p : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeRechargeSurvivingFarProductKeys n).filter
    (fun key => key.1 = p)
```

membership theoremを置く。

sqrt-scale 外では空:

```lean
theorem paritySafeRechargeFarProductKeysAtPrime_eq_empty_of_not_mem_sqrtScale
    {n p : ℕ}
    (hp : p ∉ paritySafeSqrtScaleActivePrimes n) :
    paritySafeRechargeFarProductKeysAtPrime n p = ∅ := by
  ...
```

さらに exact first-prime fiber sum を閉じる。

```lean
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_sqrtScale_fiber_sum
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      ∑ p ∈ paritySafeSqrtScaleActivePrimes n,
        (paritySafeRechargeFarProductKeysAtPrime n p).card := by
  ...
```

各 recharge key は first coordinate を一つしか持たないため、これは重複のない exact partition である。

これが閉じれば **Outcome A+** とする。

bookkeeping が大きい場合は sqrt-scale membership theorem までで Outcome A として止めてよい。

---

## 9. optional consumer — next quotient prime-factor packet

数行で既存 L044/L048 を再利用できる場合のみ、recharge key の `t₀` の prime divisor `u` について

```text
p ≤ u
u ∈ paritySafeHalfScaleActivePrimes n
```

をまとめた theorem を追加してよい。

ただしこれは今回の A/A+ 判定には不要。

新しい cofactor-prime graph や injective charge は作らない。

---

## 10. arithmetic sanity witnesses

軽ければ arithmetic-only witness を置く。

```text
n=16, key=(3,7,13): t₀=1       -- terminal
n=62, key=(3,5,37): t₀=7       -- recharge, 3^2 ≤ 62
n=17, key=(3,5,7):  t₀=3       -- recharge, 3^2 ≤ 17
```

実際の Finset membership を `norm_num` で無理に展開しない。next quotient と inequality の数値 sanity だけでよい。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- `sqrt n` を新しい square anchor とみなすこと
- smaller-anchor `SquareOffsetsFullyCovered`
- induction / infinite descent
- recharge key → first prime の injectivity 主張
- recharge key → cofactor / prime divisor の global injectivity 主張
- `t₀` が prime / squarefree であるという主張
- `p ∤ t₀` の主張
- q または s も `q^2 ≤ n`, `s^2 ≤ n` とする主張
- harmonic / asymptotic / PNT / Mertens / analytic sieve
- generic hypergraph
- global contradiction / Legendre proof declaration
- RH

特に false beam

```text
17^2 + 26 = 3*5*7*3
```

を維持し、recharge cofactor は canonical prime `p` 自身を含み得ることを忘れない。

---

## 12. Outcome 判定

### Outcome A+ — TERMINAL/RECHARGE EXACT SPLIT / SQRT-SCALE FIBERIZATION

最低条件:

1. terminal / recharge surviving-key Finset
2. disjoint / union exact partition
3. `FarResidual.card = terminal.card + recharge.card`
4. terminal membership = far triple product in square shell
5. `paritySafeSqrtScaleActivePrimes`
6. recharge first prime `p^2 ≤ n`
7. recharge first prime sqrt-scale membership
8. recharge card の exact sqrt-scale first-prime fiber sum

### Outcome A — TERMINAL/RECHARGE EXACT SPLIT / SQRT-SCALE GATE

1–7 が閉じ、8 の fiber bookkeeping のみ残る。

### Outcome B — SPLIT ONLY

terminal/recharge exact split と terminal characterization は閉じたが、`p^2 ≤ n` の arithmetic bridge に current API 上の明確な障害がある。

その場合は障害を theorem 形で report し、推測で弱い bound に差し替えない。

### Outcome C — SQRT-SCALE BEAM FALSE

`p^2 ≤ n` に genuine counterexample がある場合。

その場合は具体的 `(n,p,q,s,t₀,r₀)` を固定し、どの inequality が崩れるかを report する。

数学上は unexpected。

---

## 13. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について確認:

```text
sorry
admit
axiom
native_decide
```

既存 repository-wide の既知 `sorry` は今回の判定対象外。

---

## 14. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-far-product-key-terminal-recharge-sqrt-scale-260826.md
```

必須記載:

1. Outcome
2. terminal / recharge exact split
3. terminal triple-product shell characterization
4. sqrt-scale derivation `p^4 < point < (n+1)^2`
5. `p^2 ≤ n` theorem
6. A+ の場合は first-prime fiber sum
7. false beam / non-goals
8. validation

---

## 15. STOP 条件

今回の停止点は

```text
FarResidual.card
  = TerminalSurvivingKeys.card
  + RechargeSurvivingKeys.card

TerminalSurvivingKey
  ↔ far triple product itself lies in the square shell

RechargeSurvivingKey
  → first prime p lies in the same-anchor sqrt-scale active world
  → p^2 ≤ n
```

A+ ならさらに

```text
RechargeSurvivingKeys.card
  = sum over sqrt-scale active p of first-prime fiber cards
```

まで。

ここから先の各 `p` fiber の `(q,s)` counting、prime-pair capacity、sieve、contradiction へは進まない。