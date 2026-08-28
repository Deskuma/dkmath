# PPW-010B — canonical q-fold completion 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
current module: DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
```

PPW-010 の基礎層は Green 済み。

現在すでにある Core:

```text
prime_eq_of_pow_eq_pow
prime_pow_exponent_injective
primePower_witness_unique
primePowerBaseShadow
canonicalPrimePowerShadowCost
pascalPrimePowerPHZCanonicalUpTo
```

この checkpoint は PPW-010 の完了用であり、PPW-011 へは進まない。

目標は次の二点を同じ module で Green 化すること。

```text
1. eulerPrimePowerMode p j s = ((p^j : ℕ) : ℂ)^(-s)
2. PPW-009 の (p,k) pair-sum = canonical q-indexed sum
```

標準解析 von Mangoldt、`-ζ'/ζ`、無限級数、零点、RH はまだ扱わない。

---

## 2. レビュー結果

現在の `PascalPrimePowerCanonicalFold.lean` は、算術側の witness uniqueness と canonical shadow の器まで正しく到達している。

特に、

```lean
primePower_witness_unique
```

によって、同じ正の prime power `n` に対する

```text
base prime
positive exponent
```

が一意であることは Core 化済み。

一方、canonical sum はまだ PPW-009 pair-sum と接続されていない。

また、現在の module docstring では「corresponding prime-power mode is the natural-label complex power」と書いているが、その exact theorem はまだ未実装なので、この checkpoint で statement と実装を一致させる。

---

## 3. `cpow` branch law の安全な扱い

今回の base は任意の複素数ではなく、正の自然数 `p` の複素埋め込みである。

したがって principal-branch 問題を一般形で解こうとしない。

Mathlib には次がある。

```lean
Complex.cpow_nat_mul
Complex.cpow_nat_mul'
Complex.natCast_arg
```

概念的には、

$$
((p : \mathbb C)^{-s})^j
=
(p : \mathbb C)^{j(-s)}
=
((p : \mathbb C)^j)^{-s}.
$$

第1段は `Complex.cpow_nat_mul`。

第2段は `Complex.cpow_nat_mul'` を使える。base が自然数埋め込みなので、

$$
\arg(p)=0
$$

は `Complex.natCast_arg` で simp 可能であり、必要な branch 条件は

```text
-π < 0
0 ≤ π
```

へ落ちる。

`cpow_mul` の一般 branch 条件を直接追わないこと。

---

## 4. natural-label mode bridge

中心 theorem 候補:

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p j : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s))
```

推奨証明鎖:

```text
eulerPrimePowerMode
→ eulerPrimePrimitiveMode_eq_cpow_neg hp
→ Complex.cpow_nat_mul
→ Complex.cpow_nat_mul'
→ Nat.cast_pow / norm_cast / simp
```

`j = 0` も statement 自体は成立するので、可能なら全 `j : ℕ` で通す。

branch 条件の elaboration が重ければ、正の exponent 版を先に置いてもよい。

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg_of_pos
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) (s : ℂ) : ...
```

ただし最終的には pair-sum で使う `j = k + 1` 版が Green なら十分。

専用 theorem を置いてもよい。

```lean
theorem eulerPrimePowerMode_succ_eq_primePower_cpow_neg
    {p k : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p (k + 1) s =
      (((p ^ (k + 1) : ℕ) : ℂ) ^ (-s))
```

---

## 5. canonical exponent shadow

現在 `primePowerBaseShadow q` だけがある。

pair fold を実装しやすくするため、canonical exponent も追加する。

候補:

```lean
noncomputable def primePowerExponentShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then
    Classical.choose (Classical.choose_spec hq)
  else 0
```

`hq : IsPrimePowerLabel q` のもとで最低限次を固定する。

```lean
theorem primePowerBaseShadow_prime
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    Nat.Prime (primePowerBaseShadow q)

 theorem primePowerExponentShadow_pos
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    0 < primePowerExponentShadow q

 theorem primePower_eq_base_pow_exponentShadow
    {q : ℕ} (hq : IsPrimePowerLabel q) :
    q = primePowerBaseShadow q ^ primePowerExponentShadow q
```

既存 `primePower_witness_unique` から、任意 witness `q = p^j` に対し、

```lean
theorem primePowerBaseShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerBaseShadow q = p
```

```lean
theorem primePowerExponentShadow_eq_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    primePowerExponentShadow q = j
```

を置く。

これにより canonical cost も、

```lean
theorem canonicalPrimePowerShadowCost_eq_log_of_witness
    {q p j : ℕ}
    (hp : Nat.Prime p) (hj : 0 < j)
    (hq : q = p ^ j) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ)
```

へ固定できる。

---

## 6. Finset support を先に作る

pair-sum と q-sum を nested `Finset.sum` のまま直接書き換えようとしない。

先に有限 support の bijection を作る。

### 6.1 pair support

```lean
def pascalPrimePowerPairSupportUpTo (X : ℕ) : Finset (ℕ × ℕ) :=
  ((pascalPrimeCoordinateSupportUpTo X).product (Finset.range X)).filter
    (fun pk => pk.1 ^ (pk.2 + 1) ≤ X)
```

意味:

```text
p is Pascal-born prime up to X
k < X
p^(k+1) ≤ X
```

### 6.2 canonical q support

```lean
noncomputable def canonicalPrimePowerSupportUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter IsPrimePowerLabel
```

### 6.3 label map

```lean
def primePowerPairLabel (pk : ℕ × ℕ) : ℕ :=
  pk.1 ^ (pk.2 + 1)
```

---

## 7. support bijection

中心は二つ。

```lean
theorem primePowerPairLabel_injective_on_support
    (X : ℕ) :
    Set.InjOn primePowerPairLabel
      ↑(pascalPrimePowerPairSupportUpTo X)
```

証明の核は `primePower_witness_unique`。

pair support membership から両 base prime が prime で、exponent は `k+1 > 0`。

`p^(k+1) = q^(l+1)` なら base と exponent が一致し、pair 自体が一致する。

次に image characterization:

```lean
theorem primePowerPairLabel_image_eq_canonicalSupport
    (X : ℕ) :
    (pascalPrimePowerPairSupportUpTo X).image primePowerPairLabel =
      canonicalPrimePowerSupportUpTo X
```

逆向きでは `q ∈ canonicalPrimePowerSupportUpTo X` から explicit witness

```text
q = p^j
p prime
0 < j
q ≤ X
```

を取る。

`p ≤ X` は `p ∣ q` と `q ≤ X` から出す。

pair exponent index は `k := j - 1`。

必要な `k < X` は `q = p^j ≤ X` と `p ≥ 2`, `j > 0` から得る。ここは Mathlib API に合わせて補題を局所追加してよい。

この boundedness は有限 search envelope を正当化するだけで、数学的 cutoff 自体は `p^j ≤ X` のまま変えない。

---

## 8. PPW-009 pair-sum を support sum に正規化

既存

```lean
pascalPrimePowerPHZFiniteUpTo
```

について、まず一枚 intermediary theorem を置く。

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
        (Real.log (pk.1 : ℝ) : ℂ) *
          eulerPrimePowerMode pk.1 (pk.2 + 1) s
```

この形に落としてから canonical fold を行う。

---

## 9. canonical q-sum も filtered support に正規化

現在の定義は `range (X+1)` 全体に対し、non-prime-power を cost `0` にしている。

次を置く。

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        (canonicalPrimePowerShadowCost q : ℂ) *
          ((q : ℂ) ^ (-s))
```

これで両辺とも本当に prime-power support 上の有限和になる。

---

## 10. 最終 pair-to-q fold

中心 theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s
```

推奨証明:

```text
pairSupport_sum
→ primePowerPairLabel の injective image
→ Finset.sum_bij / sum_image
→ canonicalPrimePowerShadowCost_eq_log_of_witness
→ eulerPrimePowerMode_succ_eq_primePower_cpow_neg
→ canonicalSupport_sum
```

重要:

```text
complex phase cancellation
analytic continuation
infinite series
```

は一切使わない。有限算術 fold だけで閉じる。

---

## 11. canonical `(X,X+1)` decoder

pair fold が Green したら、canonical sum 側では successor law は非常に単純になる。

候補:

```lean
@[simp] theorem pascalPrimePowerPHZCanonicalUpTo_succ_sub
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo (X + 1) s -
        pascalPrimePowerPHZCanonicalUpTo X s =
      (canonicalPrimePowerShadowCost (X + 1) : ℂ) *
        (((X + 1 : ℕ) : ℂ) ^ (-s))
```

これは `Finset.sum_range_succ` から出す。

pair-sum 側にも fold theorem を介して同じ decoder を移送できる。

```lean
@[simp] theorem pascalPrimePowerPHZFiniteUpTo_succ_sub
```

これが Green すると、

```text
X → X+1
```

で追加されるものは canonical natural label `X+1` の一項だけ、という形になる。

---

## 12. checkpoint 境界

PPW-010B で主張してよいもの:

```text
positive prime-power witness uniqueness
canonical base / exponent
canonical finite log shadow
natural-label complex mode
pair support ↔ q support bijection
finite pair PHZ = finite canonical q Dirichlet polynomial
canonical successor decoder
```

まだ主張しないもの:

```text
canonicalPrimePowerShadowCost = Mathlib の analytic von Mangoldt function
finite q-sum = -ζ'/ζ
infinite sum convergence
critical strip continuation
zeta zero / pole relation
RH
```

---

## 13. 次 checkpoint

この checkpoint が Green になった時点で PPW-010 を完了とする。

その次に PPW-011 を作り、初めて

```text
canonicalPrimePowerShadowCost
↔ classical / Mathlib von Mangoldt API
↔ Re(s) > 1 の Dirichlet series
↔ -ζ'/ζ
```

を監査する。

まず有限 arithmetic identity と analytic identity を分離すること。

---

## 14. 推奨 build

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
lake build DkMath.RH
git diff --check
```

新規 `sorry` / `axiom` / `admit` は追加しない。

statement の数学内容を保つ限り、Finset bijection、`cpow` 正規形、cast、search-envelope の boundedness 補題は Codex が調整してよい。
