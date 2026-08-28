# PPW-010C — canonical q-fold finalization 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
module: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
```

PPW-010B の追加基盤は Green 済み。

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

この checkpoint で PPW-010 を完了する。
PPW-011 へはまだ進まない。

最終目標は次の二定理。

```lean
eulerPrimePowerMode_eq_primePower_cpow_neg
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

標準解析 von Mangoldt、`-ζ'/ζ`、無限級数、零点、RH は扱わない。

---

## 2. レビュー上の軽微な修正

現状、次の三定義直前は `/- ... -/` なので通常コメントであり docstring ではない。

```text
primePowerExponentShadow
pascalPrimePowerPairSupportUpTo
canonicalPrimePowerSupportUpTo
primePowerPairLabel
```

公開 API として残すものは `/-- ... -/` へ直すこと。

数学的内容には影響しない。

---

## 3. cpow bridge は branch 条件なしで組める

一般 `Complex.cpow_mul` を使って principal branch 条件を処理する必要はない。
正の自然数 base について、Mathlib の次の二定理を直接組み合わせる。

```lean
Complex.cpow_nat_mul
Complex.natCast_cpow_natCast_mul
```

概念的には、任意の `p j : ℕ`, `z : ℂ` に対して

```text
((p : ℂ) ^ z) ^ j
  = (p : ℂ) ^ ((j : ℂ) * z)
  = (((p : ℂ) ^ j) ^ z)
  = (((p ^ j : ℕ) : ℂ) ^ z)
```

となる。

したがって `hp : Nat.Prime p` を使って primitive mode を `p^(-s)` に直した後、

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
  rw [eulerPrimePowerMode, eulerPrimePrimitiveMode_eq_cpow_neg hp]
  calc
    ((p : ℂ) ^ (-s)) ^ j =
        (p : ℂ) ^ ((j : ℂ) * (-s)) := by
          symm
          exact Complex.cpow_nat_mul (p : ℂ) j (-s)
    _ = (((p : ℂ) ^ j) ^ (-s)) := by
          exact Complex.natCast_cpow_natCast_mul p j (-s)
    _ = (((p ^ j : ℕ) : ℂ) ^ (-s)) := by
          norm_num
```

を第一候補とする。

最後の cast normalization は `norm_num` / `norm_cast` / `simp` の通る形へ調整してよい。
statement の数学内容は変えない。

---

## 4. canonical shadow の spec を先に固定する

Finset fold の前に、choice を theorem-facing API で隠す。

候補:

```lean
theorem primePowerShadow_spec
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    Nat.Prime (primePowerBaseShadow q) ∧
      0 < primePowerExponentShadow q ∧
      q = primePowerBaseShadow q ^ primePowerExponentShadow q
```

次に任意 witness から canonical choice を回収する。

```lean
theorem primePowerBaseShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerBaseShadow q = p

 theorem primePowerExponentShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerExponentShadow q = j
```

既存 `primePower_witness_unique` を使う。

その結果、cost を witness-independent に読む。

```lean
theorem canonicalPrimePowerShadowCost_eq_log_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ)
```

---

## 5. pair support の membership theorem

まず定義展開を毎回しないため membership theorem を置く。

```lean
@[simp] theorem mem_pascalPrimePowerPairSupportUpTo_iff
    {X p k : ℕ} :
    (p,k) ∈ pascalPrimePowerPairSupportUpTo X ↔
      p ∈ pascalPrimeCoordinateSupportUpTo X ∧
      k < X ∧
      p ^ (k + 1) ≤ X
```

canonical 側も置く。

```lean
@[simp] theorem mem_canonicalPrimePowerSupportUpTo_iff
    {X q : ℕ} :
    q ∈ canonicalPrimePowerSupportUpTo X ↔
      q ≤ X ∧ IsPrimePowerLabel q
```

`Finset.mem_range` の `< X+1` は `q ≤ X` へ `omega` で落とす。

---

## 6. pair label injectivity

pair support 上で `primePowerPairLabel` が injective であることを証明する。

```lean
theorem primePowerPairLabel_injective_on
    {X : ℕ} :
    Set.InjOn primePowerPairLabel
      (↑(pascalPrimePowerPairSupportUpTo X) : Set (ℕ × ℕ))
```

または Finset 用に直接、

```lean
theorem primePowerPairLabel_eq_imp_eq_of_mem
    {X : ℕ} {a b : ℕ × ℕ}
    (ha : a ∈ pascalPrimePowerPairSupportUpTo X)
    (hb : b ∈ pascalPrimePowerPairSupportUpTo X)
    (hlab : primePowerPairLabel a = primePowerPairLabel b) :
    a = b
```

を置く。

証明では support membership から `Nat.Prime a.1`, `Nat.Prime b.1` を得て、

```lean
primePower_witness_unique
```

を exponent `a.2+1`, `b.2+1` に適用する。

Mathlib に既存の `Nat.Prime.pow_inj` / `Nat.Prime.pow_inj'` もあるが、既存 DkMath Core をそのまま使ってよい。大改造しない。

---

## 7. image equality

中心となる有限 support theorem を先に作る。

```lean
theorem image_primePowerPairLabel_eq_canonicalSupport
    (X : ℕ) :
    (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel =
      canonicalPrimePowerSupportUpTo X
```

### pair → q

`(p,k)` が pair support にあれば、

```text
p prime
p^(k+1) ≤ X
```

なので、label は `q ≤ X` の positive prime power。

### q → pair

`q` が canonical support にあれば `primePowerShadow_spec` から

```text
p := primePowerBaseShadow q
j := primePowerExponentShadow q
q = p^j
p prime
0 < j
```

を得る。

pair は

```text
(p, j - 1)
```

を使う。

必要な bounds:

```text
p ≤ X
j - 1 < X
p^j ≤ X
```

`p ≤ X` は `p ∣ p^j = q`, `q ≤ X`, `q > 0` から得てよい。

`j - 1 < X` は Mathlib の

```lean
Nat.lt_pow_self p.one_lt j
```

を利用できる。

`j < p^j = q ≤ X` から `j - 1 < X` を `omega` で閉じる。

これにより無理な exponent envelope 補題を新設しない。

---

## 8. pair-sum を support sum へ正規化

PPW-009 の nested `if` sum を、pair support 上の plain sum に一度変換する。

候補 theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) s
```

これは fold 本体と切り離す。

---

## 9. canonical sum も canonical support へ正規化

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) * ((q : ℂ) ^ (-s))
```

非 prime-power `q` では cost が `0` なので、range sum から filter sum へ落とすだけ。

---

## 10. summand compatibility

pair support 上で、一項が canonical label の一項と一致する theorem を置く。

```lean
theorem primePower_pair_summand_eq_canonical_summand
    {X : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ pascalPrimePowerPairSupportUpTo X)
    (s : ℂ) :
    (Real.log (pk.1 : ℝ) : ℂ) *
        eulerPrimePowerMode pk.1 (pk.2 + 1) s =
      (canonicalPrimePowerShadowCost (primePowerPairLabel pk) : ℂ) *
        (((primePowerPairLabel pk : ℕ) : ℂ) ^ (-s))
```

ここで使うのは、

```text
eulerPrimePowerMode_eq_primePower_cpow_neg
canonicalPrimePowerShadowCost_eq_log_of_witness
```

の二つ。

---

## 11. 最終 fold

上記を組み合わせて、

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s
```

を証明する。

実装手段は、

```text
Finset.sum_bij
Finset.sum_image
Finset.sum_equiv
```

のうち Lean 4.32.2 で最も素直なものを選んでよい。

推奨は、先に `image_primePowerPairLabel_eq_canonicalSupport` と injectivity を Green にしてから `Finset.sum_image` を使う経路。

nested sum のまま bijection を組まない。

---

## 12. successor decoder は fold 後に追加

fold が Green したら余力で、

```lean
@[simp] theorem pascalPrimePowerPHZCanonicalUpTo_succ_sub
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo (X + 1) s -
        pascalPrimePowerPHZCanonicalUpTo X s =
      (canonicalPrimePowerShadowCost (X + 1) : ℂ) *
        (((X + 1 : ℕ) : ℂ) ^ (-s))
```

を置く。

これは PPW の `(N,N+1)` decoder が canonical natural-number axis に到達したことを示す。

ただし PPW-010 完了判定には必須ではない。最終 fold を優先する。

---

## 13. 完了条件

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
lake build DkMath.RH
git diff --check
```

新規 `sorry` / `axiom` / `admit` を追加しない。

PPW-010 完了条件:

```text
[必須] eulerPrimePowerMode_eq_primePower_cpow_neg
[必須] image_primePowerPairLabel_eq_canonicalSupport
[必須] pair summand = canonical summand
[必須] pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

ここまで Green した時点で PPW-011 へ進む。
