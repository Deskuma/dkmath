# PPW-010E — canonical q-fold load-bearing proof handoff

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
module: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
```

PPW-010D の theorem-facing canonical shadow spec は Green 済み。

現在の Core:

```text
prime_eq_of_pow_eq_pow
prime_pow_exponent_injective
primePower_witness_unique
primePowerBaseShadow
primePowerExponentShadow
primePowerShadow_spec
canonicalPrimePowerShadowCost
pascalPrimePowerPairSupportUpTo
canonicalPrimePowerSupportUpTo
primePowerPairLabel
pascalPrimePowerPHZCanonicalUpTo
```

この checkpoint では新しい概念層を増やさず、PPW-010 の load-bearing proof だけを閉じる。

必須完了 theorem:

```lean
eulerPrimePowerMode_eq_primePower_cpow_neg
image_primePowerPairLabel_support_eq_canonicalSupport
primePowerPair_summand_eq_canonical
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

`sorry` / `axiom` / `admit` は使用しない。

標準解析 von Mangoldt、`-ζ'/ζ`、無限級数、零点、RH へは進まない。

---

## 2. `cpow` bridge は branch condition を導入しない

今回の base は自然数 cast なので、一般 `Complex.cpow_mul` を使わない。

使う候補 API:

```lean
Complex.cpow_nat_mul
Complex.natCast_cpow_natCast_mul
Nat.cast_pow
```

中心 theorem:

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
  calc
    eulerPrimePowerMode p j s =
        ((p : ℂ) ^ (-s)) ^ j := by
      rw [eulerPrimePowerMode, eulerPrimePrimitiveMode_eq_cpow_neg hp]
    _ = (p : ℂ) ^ ((j : ℂ) * (-s)) := by
      symm
      exact Complex.cpow_nat_mul (p : ℂ) j (-s)
    _ = ((p : ℂ) ^ j) ^ (-s) := by
      exact Complex.natCast_cpow_natCast_mul p j (-s)
    _ = (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
      simp only [Nat.cast_pow]
```

Mathlib version差で最後の `simp only` が逆向きになれば `simpa only [Nat.cast_pow]` 等へ調整してよい。

数学内容は変えない。

---

## 3. canonical shadow の witness-specific corollary

`primePowerShadow_spec` から、任意 witness と canonical choice が一致する theorem を作る。

候補:

```lean
theorem primePowerBaseShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p)
    (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerBaseShadow q = p
```

```lean
theorem primePowerExponentShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p)
    (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerExponentShadow q = j
```

```lean
theorem canonicalPrimePowerShadowCost_eq_log_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p)
    (hj : 0 < j)
    (hq : q = p ^ j) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ)
```

証明は `primePowerShadow_spec` と `primePower_witness_unique` を比較する。

最終 fold の中で `Classical.choose` を直接展開しない。

---

## 4. support membership theorem

### 4.1 pair support

```lean
@[simp] theorem mem_pascalPrimePowerPairSupportUpTo_iff
    {X : ℕ} {pk : ℕ × ℕ} :
    pk ∈ pascalPrimePowerPairSupportUpTo X ↔
      pk.1 ∈ pascalPrimeCoordinateSupportUpTo X ∧
      pk.2 < X ∧
      pk.1 ^ (pk.2 + 1) ≤ X
```

既存 `mem_pascalPrimeCoordinateSupportUpTo_iff` により、membership から prime proof と `p ≤ X` を回収できるようにする。

### 4.2 canonical support

```lean
@[simp] theorem mem_canonicalPrimePowerSupportUpTo_iff
    {X q : ℕ} :
    q ∈ canonicalPrimePowerSupportUpTo X ↔
      q ≤ X ∧ IsPrimePowerLabel q
```

`Finset.mem_range` と `Nat.lt_succ_iff` を利用する。

---

## 5. pair label の support 上 injectivity

全 `ℕ × ℕ` 上の injectivity は主張しない。

必要なのは、固定 cutoff `X` の pair support 上だけ。

候補:

```lean
theorem primePowerPairLabel_injOn
    (X : ℕ) :
    Set.InjOn primePowerPairLabel
      (↑(pascalPrimePowerPairSupportUpTo X) : Set (ℕ × ℕ))
```

`pk`, `pl` の support membership から `pk.1`, `pl.1` が prime。

label equality は exact に

```text
pk.1 ^ (pk.2 + 1) = pl.1 ^ (pl.2 + 1)
```

なので、既存 `primePower_witness_unique` を使うか、Mathlib の prime-power positive-exponent injectivityを使って、

```text
pk.1 = pl.1
pk.2 + 1 = pl.2 + 1
```

を得る。

最後は `Prod.ext` と `omega`。

---

## 6. image equality が主算術 theorem

```lean
theorem image_primePowerPairLabel_support_eq_canonicalSupport
    (X : ℕ) :
    (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel =
      canonicalPrimePowerSupportUpTo X
```

`Finset.ext q`; `Finset.mem_image` で両方向を証明する。

### forward

pair `pk = (p,k)` から、

```text
p prime
p^(k+1) ≤ X
```

が得られる。

したがって label `p^(k+1)` は `IsPrimePowerLabel` かつ `≤ X`。

### backward

canonical `q` から `primePowerShadow_spec` を使って

```text
p := primePowerBaseShadow q
j := primePowerExponentShadow q
p prime
0 < j
q = p^j
```

を取る。

pair は

```text
(p, j - 1)
```

とする。

必要な bound:

```text
p ≤ X
j - 1 < X
p ^ ((j - 1) + 1) ≤ X
```

`p ≤ X` は `p ≤ p^j = q ≤ X` から得る。

`j - 1 < X` は prime `p` なので `1 < p`、かつ `Nat.lt_pow_self p.one_lt j` から

```text
j < p^j = q ≤ X
```

を得て `omega` で閉じる。

指数正規化は `0 < j` から `Nat.sub_add_cancel` を使う。

ここを Green にした後でのみ sum fold へ進む。

---

## 7. PPW-009 nested sum を pair-support sum へ正規化

補助 theorem を置く。

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) s
```

これは解析 theorem ではなく、

```text
product Finset
+ filter cutoff
+ nested sum
```

の有限和正規化だけ。

`Finset.sum_filter`, product sum の標準 API、`simp` を優先する。

---

## 8. canonical range sum を canonical-support sum へ正規化

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s))
```

`canonicalPrimePowerShadowCost q` は prime-power でない `q` では `0` なので、range sum から filter support へ落とすだけ。

---

## 9. 一項 summand compatibility

```lean
theorem primePowerPair_summand_eq_canonical
    {X : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ pascalPrimePowerPairSupportUpTo X)
    (s : ℂ) :
    (Real.log (pk.1 : ℝ) : ℂ) *
        eulerPrimePowerMode pk.1 (pk.2 + 1) s =
      (canonicalPrimePowerShadowCost (primePowerPairLabel pk) : ℂ) *
        (((primePowerPairLabel pk : ℕ) : ℂ) ^ (-s))
```

ここでは二本だけ使う。

```text
canonicalPrimePowerShadowCost_eq_log_of_witness
eulerPrimePowerMode_eq_primePower_cpow_neg
```

pair support から prime proof を回収する。

---

## 10. 最終 fold

最後にだけ `Finset.image` を使う。

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s
```

証明構造:

```text
PPW-009 nested sum
= pair-support sum
= image primePowerPairLabel 上の canonical summand sum
= canonicalPrimePowerSupportUpTo X 上の sum
= canonical range sum
```

二段目は `primePowerPairLabel_injOn` と `primePowerPair_summand_eq_canonical`。
三段目は `image_primePowerPairLabel_support_eq_canonicalSupport`。

必要なら `Finset.sum_bij` を使ってもよいが、bijection の数学内容を theorem として残すため、image equality 自体は必須とする。

---

## 11. 完了条件

次の四 theorem がすべて Green になった時点で PPW-010 完了。

```lean
eulerPrimePowerMode_eq_primePower_cpow_neg
image_primePowerPairLabel_support_eq_canonicalSupport
primePowerPair_summand_eq_canonical
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

推奨検証:

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
lake build DkMath.RH
git diff --check
```

新しい解析仮定を加えない。
新しい canonical choice を増やさない。
新しい PHZ 定義を増やさない。

この checkpoint は proof closure のみ。
