# instruction-066 — PRIM-L051 Recharge Pair-Product Return / Dual Reduced-Base Fiber

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `bbc53c823588d376e4030c562d5d24ae4daabd2e`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L050` は **Outcome A+ — TERMINAL/RECHARGE EXACT SPLIT / SQRT-SCALE FIBERIZATION** として受理する。

L050 までで、surviving far key

```text
key := (p,(q,s))
m   := p*q*s
t₀  := paritySafeFarProductWaveNextQuotient n key
r₀  := paritySafeFarProductWaveNextSeat n key
```

は terminal / recharge に exact 分割され、recharge では

```text
1 < t₀
p ≤ t₀
p < q < s
m*t₀ = n^2 + r₀
1 ≤ r₀ ≤ 2*n
p^2 ≤ n
```

まで得られている。

今回の bounded target は、recharge key の最初の **二 prime の積**

```text
b := p*q
```

を same-anchor reduced first-half world へ戻すことだけである。

---

## 1. 数学的核

recharge key では `p ≤ t₀` と `q < s` があるため、正値性を使って

```text
p*q < t₀*s
```

したがって

```text
(p*q)^2 < (p*q)*(s*t₀) = p*q*s*t₀.
```

survival の shell-fit から

```text
p*q*s*t₀ ≤ n^2 + 2*n < (n+1)^2.
```

よって

```text
(p*q)^2 < (n+1)^2.
```

自然数上ではこれから

```text
p*q ≤ n
```

が従う。

これが今回の主 scale compression である。

さらに `p,q` は active odd primes なので、既存

```lean
activePrime_reducedResidue_packet
```

から

```text
Coprime (2*n) p
Coprime (2*n) q
```

を得る。従って

```text
Coprime (2*n) (p*q).
```

したがって `b=p*q` は L046 の既存 universe

```lean
paritySafeFarCofactorBaseOffsets n
```

へ入る。

つまり recharge key は、少なくとも

```text
first-pair product b = p*q
next quotient      t₀
```

という **二つの reduced first-half coordinate** を同じ finite world に返す。

これは smaller anchor / descent ではない。両方とも anchor `n` における same-anchor coordinate である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargePairProduct.lean
```

最初は

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge
```

だけを試す。

完成したら facade

```text
DkMath.NumberTheory.Legendre
```

へ import を追加する。

---

## 3. L051.1 — first-pair product

必要なら薄い def を置く。

```lean
/-- Product of the first two ordered active primes of a far key. -/
def paritySafeRechargeFirstPairProduct
    (key : ℕ × (ℕ × ℕ)) : ℕ :=
  key.1 * key.2.1
```

単なる notation 的 def なので、proof が逆に重くなるなら直接 `p*q` を使ってもよい。

---

## 4. L051.2 — recharge pair-product old-scale gate — 第一主定理

必須 theorem:

```lean
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_le_anchor
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p * q ≤ n := by
  ...
```

推奨証明 spine:

1. `hkey` から surviving far key / `1 < t₀` を展開。
2. L050/L048 の既存 consumer から `p ≤ t₀` を取る。
   - 既存 theorem を直接使えるなら再証明しない。
3. far gate から `p < q < s` と primality / positivity を取る。
4. `p ≤ t₀`, `q < s` から

   ```text
   (p*q)^2 < p*q*s*t₀
   ```

   を作る。
5. shell-fit で

   ```text
   p*q*s*t₀ ≤ n^2 + 2*n < (n+1)^2
   ```

6. よって `(p*q)^2 < (n+1)^2`。
7. `n < p*q` を仮定すると `n+1 ≤ p*q` なので平方単調性と矛盾。
8. `p*q ≤ n`。

`Nat.sqrt` は導入しない。今回必要なのは自然数不等式だけである。

---

## 5. L051.3 — pair product reduced-base return

必須 theorem:

```lean
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_coprime_two_mul
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    Nat.Coprime (2*n) (p*q) := by
  ...
```

既存 `activePrime_reducedResidue_packet` を使う。

`p,q` が `squareAnchorOddActivePrimes n` に属することは far gate packet から取る。

その上で strongest public return:

```lean
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p*q ∈ paritySafeFarCofactorBaseOffsets n := by
  ...
```

membership は既存

```lean
mem_paritySafeFarCofactorBaseOffsets
```

へ

```text
1 ≤ p*q
p*q ≤ n
Coprime (2*n) (p*q)
```

を入れる。

### optional but strongly preferred

recharge key の `t₀` も同じ base world に属する key-level theorem を公開する。

```lean
theorem paritySafeRechargeSurvivingFarProductKey_nextQuotient_mem_farCofactorBase
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextQuotient n (p,(q,s)) ∈
      paritySafeFarCofactorBaseOffsets n := by
  ...
```

これは新数学を作らず、next seat → actual far residual → L046 cofactor-base return、または既存 packet の transport で閉じる。

この theorem が安ければ、今回の概念を

```text
b = p*q ∈ reduced first-half base
 t₀      ∈ reduced first-half base
```

という **dual reduced-base return** として公開できる。

---

## 6. L051.4 — pair-product fibers

recharge keys を pair-product 値で fiberize する。

```lean
noncomputable def paritySafeRechargeFarProductKeysAtPairProduct
    (n b : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeRechargeSurvivingFarProductKeys n).filter
    (fun key => key.1 * key.2.1 = b)
```

membership simp theorem:

```lean
@[simp] theorem mem_paritySafeRechargeFarProductKeysAtPairProduct ... :
  key ∈ paritySafeRechargeFarProductKeysAtPairProduct n b ↔
    key ∈ paritySafeRechargeSurvivingFarProductKeys n ∧
    key.1 * key.2.1 = b := by
  ...
```

base world 外は empty:

```lean
theorem paritySafeRechargeFarProductKeysAtPairProduct_eq_empty_of_not_mem_base
    {n b : ℕ}
    (hb : b ∉ paritySafeFarCofactorBaseOffsets n) :
    paritySafeRechargeFarProductKeysAtPairProduct n b = ∅ := by
  ...
```

そして必須 exact fiber sum:

```lean
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_pairProductBase_fiber_sum
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      ∑ b ∈ paritySafeFarCofactorBaseOffsets n,
        (paritySafeRechargeFarProductKeysAtPairProduct n b).card := by
  ...
```

L050 と同じ `Finset.sum_card_fiberwise_eq_card_filter` route が使えるはず。

ここでは pair-product fiber の cardinality bound は要求しない。

---

## 7. L051.5 — global exact residual decomposition

L050 の

```text
FarResidual.card = Terminal.card + Recharge.card
```

と今回の pair-product fiber sum を合成する。

strongly preferred:

```lean
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_pairProductFibers
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      ∑ b ∈ paritySafeFarCofactorBaseOffsets n,
        (paritySafeRechargeFarProductKeysAtPairProduct n b).card := by
  ...
```

これは新しい上界ではなく、既存 exact mass をより小さい finite coordinate world へ再配列する theorem である。

---

## 8. L051.6 — ordered-prime pair uniqueness from product — optional A+

同じ pair-product 値が異なる ordered prime pair `(p,q)` を表すことはない。

recharge membership から `p,q` は prime かつ `p<q`。

可能なら local/private helper:

```lean
private theorem ordered_prime_pair_eq_of_mul_eq
    {p₁ q₁ p₂ q₂ : ℕ}
    (hp₁ : Nat.Prime p₁)
    (hq₁ : Nat.Prime q₁)
    (hp₂ : Nat.Prime p₂)
    (hq₂ : Nat.Prime q₂)
    (hlt₁ : p₁ < q₁)
    (hlt₂ : p₂ < q₂)
    (hmul : p₁*q₁ = p₂*q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  ...
```

L046 に類似 private lemma があるが private なので直接使えない。今回だけ数行で再構成してよい。generic factorization API へ昇格しない。

public theorem 候補:

```lean
theorem paritySafeRecharge_firstPair_eq_of_pairProduct_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁,(q₁,s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (h₂ : (p₂,(q₂,s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hprod : p₁*q₁ = p₂*q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  ...
```

**重要:** これは key 全体の injectivity ではない。`s₁=s₂` は結論しない。

これが閉じれば Outcome A+ とする。

---

## 9. arithmetic witnesses / false beam

小さな `norm_num` theorem を一つ置くなら、次を優先する。

```text
recharge:
  n=17, key=(3,5,7), t₀=3
  p*q = 15 ≤ 17

recharge:
  n=62, key=(3,5,37), t₀=7
  p*q = 15 ≤ 62

terminal false beam:
  n=16, key=(3,7,13), t₀=1
  p*q = 21 > 16
```

意味:

```text
p*q ≤ n
```

は **recharge consumer** であり、全 far key に拡張してはいけない。

型付き Finset membership を数値展開する必要はない。

---

## 10. 今回の strongest interpretation

L050 では recharge key が

```text
p ∈ sqrt-scale active primes
```

へ戻った。

L051 ではさらに

```text
(p,q) ordered prime pair
        ↓ multiply
b = p*q
        ↓
b ≤ n
Coprime (2*n) b
        ↓
b ∈ paritySafeFarCofactorBaseOffsets n
```

へ戻す。

同時に cofactor `t₀` も同じ finite reduced-base world にいる。

したがって recharge factorization

```text
n^2 + r₀ = (p*q) * s * t₀
```

のうち、

```text
b := p*q
t := t₀
```

の二つが同じ first-half reduced universe に入る。

ここが次の capacity attack の入口である。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- `b=p*q` から key 全体 `(p,q,s)` が一意だと主張しない
- `(b,t₀)` から key 全体が一意だと主張しない
- `b ≤ t₀` / `t₀ ≤ b` を仮定しない
- `b ≠ t₀` を仮定しない
- `t₀` の primality / squarefreeness
- `p ∤ t₀`
- `q^2 ≤ n` や `s^2 ≤ n` の無根拠な強化
- generic pair graph / hypergraph
- pair-product fiber cardinality の closed form
- harmonic / sieve / PNT / Mertens / asymptotic estimate
- `sqrt n` を新 anchor とすること
- smaller-anchor `SquareOffsetsFullyCovered`
- induction / infinite descent
- global contradiction
- Legendre conjecture / RH の proof claim

---

## 12. Outcome 判定

### Outcome A+ — DUAL REDUCED-BASE PAIR RETURN

最低条件:

1. recharge key で `p*q ≤ n`
2. `Coprime (2*n) (p*q)`
3. `p*q ∈ paritySafeFarCofactorBaseOffsets n`
4. pair-product fiber Finset
5. recharge card の exact pair-product fiber sum
6. `FarResidual.card = Terminal.card + pair-product fiber sum`
7. pair-product equality から ordered first pair `(p,q)` の equality

`next quotient ∈ paritySafeFarCofactorBaseOffsets` も公開できれば明示的に report する。

### Outcome A — PAIR-PRODUCT RETURN / EXACT FIBER

1〜6 が成立。ordered pair uniqueness は未実装。

### Outcome B — SCALE RETURN ONLY

`p*q ≤ n` と reduced-base membership は成立するが、fiber bookkeeping が予想以上に重い。

### Outcome C — PROPOSED PAIR RETURN FAILS

`p*q ≤ n` の導出が成立しない。反例または欠けている仮定を exact に報告する。

---

## 13. Validation

実装後:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source についてのみ確認:

```text
sorry
admit
axiom
native_decide
```

既存 repository-wide `sorry` は今回の判定対象外。

---

## 14. report

作成候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-recharge-pair-product-dual-base-260826.md
```

report には最低限:

1. Outcome
2. `p*q ≤ n` の proof spine
3. reduced-base return
4. pair-product fiber sum
5. terminal false beam
6. ordered pair uniquenessを実装したか
7. dual base `(p*q,t₀)` の意味
8. 非目標
9. validation

を記録する。
