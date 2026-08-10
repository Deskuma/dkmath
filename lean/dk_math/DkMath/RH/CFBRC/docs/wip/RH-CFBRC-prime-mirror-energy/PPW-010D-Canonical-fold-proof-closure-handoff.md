# PPW-010D — canonical q-fold proof closure 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
module: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
```

PPW-010C の基盤は Green 済み。

現在の Core:

```text
prime_eq_of_pow_eq_pow
prime_pow_exponent_injective
primePower_witness_unique
primePowerBaseShadow
primePowerExponentShadow
canonicalPrimePowerShadowCost
pascalPrimePowerPairSupportUpTo
canonicalPrimePowerSupportUpTo
primePowerPairLabel
pascalPrimePowerPHZCanonicalUpTo
```

この checkpoint では新しい概念を増やさず、PPW-010 の未完二定理を閉じる。

```lean
eulerPrimePowerMode_eq_primePower_cpow_neg
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

`sorry` / `axiom` / `admit` は使わない。

---

## 2. `cpow` bridge は自然数 base の専用 law で閉じる

一般の `Complex.cpow_mul` の branch 条件は持ち込まない。

Mathlib の自然数 base 用 theorem を使う。

```lean
Complex.cpow_nat_mul
Complex.natCast_cpow_natCast_mul
```

目標 theorem:

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
  ...
```

推奨変形順:

```text
eulerPrimePowerMode p j s
= (eulerPrimePrimitiveMode p s)^j
= (((p : ℂ)^(-s))^j)
= (p : ℂ)^((j : ℂ) * (-s))
= (((p : ℂ)^j)^(-s))
= (((p^j : ℕ) : ℂ)^(-s))
```

Lean の候補骨格:

```lean
  rw [eulerPrimePowerMode, eulerPrimePrimitiveMode_eq_cpow_neg hp]
  rw [← Complex.cpow_nat_mul]
  rw [Complex.natCast_cpow_natCast_mul]
  norm_num
```

最後の cast normalization が `norm_num` だけで閉じなければ、`Nat.cast_pow` / `norm_cast` / `change` を使う。

この theorem は `j = 0` も含めて成立する形を優先する。

---

## 3. canonical choice の spec を先に固定する

`primePowerBaseShadow` と `primePowerExponentShadow` は同じ `IsPrimePowerLabel q` witness から選ばれている。

以下を先に theorem 化する。

```lean
theorem primePowerShadow_spec
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    Nat.Prime (primePowerBaseShadow q) ∧
      0 < primePowerExponentShadow q ∧
      q = primePowerBaseShadow q ^ primePowerExponentShadow q
```

その後、任意 witness から canonical choice を回収する。

```lean
theorem primePowerBaseShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j) (hq : q = p ^ j) :
    primePowerBaseShadow q = p

 theorem primePowerExponentShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j) (hq : q = p ^ j) :
    primePowerExponentShadow q = j

 theorem canonicalPrimePowerShadowCost_eq_log_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j) (hq : q = p ^ j) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ)
```

証明は `primePower_witness_unique` を使う。

---

## 4. support membership theorem

pair support:

```lean
@[simp] theorem mem_pascalPrimePowerPairSupportUpTo_iff
    {X p k : ℕ} :
    (p, k) ∈ pascalPrimePowerPairSupportUpTo X ↔
      Nat.Prime p ∧ p ≤ X ∧ k < X ∧ p ^ (k + 1) ≤ X
```

canonical support:

```lean
@[simp] theorem mem_canonicalPrimePowerSupportUpTo_iff
    {X q : ℕ} :
    q ∈ canonicalPrimePowerSupportUpTo X ↔
      q ≤ X ∧ IsPrimePowerLabel q
```

必要なら conjunction の順序は `simp` が最も扱いやすい形へ調整してよい。

---

## 5. pair label の support 上 injectivity

`primePowerPairLabel` は全 `ℕ × ℕ` 上では injective ではない。

したがって global `Function.Injective` を主張しない。

必要なのは support 上だけ。

```lean
theorem primePowerPairLabel_injOn
    (X : ℕ) :
    Set.InjOn primePowerPairLabel
      (↑(pascalPrimePowerPairSupportUpTo X) : Set (ℕ × ℕ)) := by
  ...
```

二つの pair

```text
(p,k), (q,l)
```

について support membership から `Nat.Prime p`, `Nat.Prime q` を取り出し、

```text
p^(k+1) = q^(l+1)
```

へ `primePower_witness_unique` を適用する。

指数は `k+1 = l+1` なので最後は `omega` で pair equality へ戻す。

---

## 6. support image equality

まず値の集合として fold を完成させる。

```lean
theorem image_primePowerPairLabel_support_eq_canonicalSupport
    (X : ℕ) :
    (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel =
      canonicalPrimePowerSupportUpTo X := by
  ...
```

forward:

```text
(p,k) in pair support
→ p prime
→ k+1 > 0
→ q = p^(k+1)
→ q ≤ X
→ IsPrimePowerLabel q
```

reverse:

```text
q in canonical support
→ q ≤ X
→ q = p^j, p prime, j > 0
→ choose pair (p, j-1)
```

この reverse で必要な bounds:

```text
p ≤ X
j - 1 < X
p^j ≤ X
```

`p ≤ X` は `p ∣ q` と `0 < q` から出してよい。

`j - 1 < X` は `Nat.lt_pow_self hp.one_lt j` と `q = p^j ≤ X` から十分に強い bound が得られる。細部は `omega` で調整する。

---

## 7. nested PPW-009 sum を pair-support sum へ一度正規化する

直接 canonical sum へ飛ばさない。

まず helper theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) s
```

これは PPW-009 の nested `if` sum と filtered product support の定義展開だけで閉じる層。

ここでは canonical choice は使わない。

---

## 8. canonical range sum を canonical-support sum へ正規化する

helper theorem:

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s))
```

`q` が prime-power でない場合の canonical cost が `0` なので、range sum から filter sum へ移せる。

---

## 9. summand compatibility

pair support の一項が、その natural label の canonical summand と一致する theorem を置く。

```lean
theorem primePowerPair_summand_eq_canonical
    {X : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ pascalPrimePowerPairSupportUpTo X)
    (s : ℂ) :
    (Real.log (pk.1 : ℝ) : ℂ) *
        eulerPrimePowerMode pk.1 (pk.2 + 1) s =
      (canonicalPrimePowerShadowCost (primePowerPairLabel pk) : ℂ) *
        (((primePowerPairLabel pk : ℕ) : ℂ) ^ (-s)) := by
  ...
```

使用する Core:

```text
support membership → Nat.Prime pk.1
eulerPrimePowerMode_eq_primePower_cpow_neg
canonicalPrimePowerShadowCost_eq_log_of_witness
```

---

## 10. Finset fold

最終 theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s := by
  ...
```

推奨は以下の二択。

### Route A — `Finset.image` + support InjOn

既に作った

```text
primePowerPairLabel_injOn
image_primePowerPairLabel_support_eq_canonicalSupport
```

を使って image 上へ sum を移送する。

### Route B — support subtype の embedding

`Finset.image` の sum API が扱いにくければ、

```text
{pk // pk ∈ pascalPrimePowerPairSupportUpTo X}
```

を domain にして `primePowerPairLabel` を embedding 化し、`Finset.attach` + `Finset.map` へ切り替える。

`primePowerPairLabel` の global injectivity を捏造しないこと。

---

## 11. 完了条件

以下が全部 Green になったとき PPW-010 完了。

```text
eulerPrimePowerMode_eq_primePower_cpow_neg
primePowerShadow_spec
primePowerBaseShadow_eq_of_witness
primePowerExponentShadow_eq_of_witness
canonicalPrimePowerShadowCost_eq_log_of_witness
mem_pascalPrimePowerPairSupportUpTo_iff
mem_canonicalPrimePowerSupportUpTo_iff
primePowerPairLabel_injOn
image_primePowerPairLabel_support_eq_canonicalSupport
pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
primePowerPair_summand_eq_canonical
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

build:

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
lake build DkMath.RH
git diff --check
```

この checkpoint では PPW-011 へ進まない。
