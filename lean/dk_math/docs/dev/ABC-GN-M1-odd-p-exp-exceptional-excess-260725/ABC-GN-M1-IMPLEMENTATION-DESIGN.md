# ABC–GN M1 Implementation Design

副題: odd-prime exponent における exceptional valuation excess の完全消去

## 1. Objective

基底ブランチの `GNExceptionalValuationExcess` は、指数 `n` を割る prime channel 上の valuation multiplicity を測る。

```lean
noncomputable def GNExceptionalValuationExcess (n a b : ℕ) : ℝ :=
  ∑ q ∈ (GN n a b).factorization.support.filter (fun q => q ∣ n),
    (((GN n a b).factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)
```

M1 の目的は、`n = p` が奇素数なら、この有限和が恒等的にゼロであることを証明すること。

最終 theorem shape:

```lean
/-- Odd-prime exponents carry no exponent-exceptional GN multiplicity. -/
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalValuationExcess p T.a T.b = 0 := by
  ...
```

Budget wrapper:

```lean
/-- The exceptional affine budget is exactly zero at odd-prime exponent. -/
theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalExcessBudgetAffine T p 0 0 := by
  ...
```

`hb` は GN nonzero や既存 API との接続に必要な場合のみ残す。不要なら theorem surface から除去する。

## 2. Current API facts

### 2.1. Boundary–GN overlap is exponent-supported

既存 theorem:

```lean
Triple.gcd_boundary_GN_dvd_exp
Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
```

意味:

$$q\mid T.a\quad\land\quad q\mid GN_n(T.a,T.b)\quad\Longrightarrow\quad q\mid n$$

M1 では逆方向に近い局所事実を奇素数指数で作る。

$$p\mid GN_p(T.a,T.b)\quad\Longrightarrow\quad p\mid T.a$$

### 2.2. Exceptional excess is a filtered finite sum

既存定義では、各 summand は

$$\left(v_q(GN)-1\right)\log q$$

である。

したがって全体をゼロにする最短 route は、filtered support の各 `q` について

```lean
(GN p T.a T.b).factorization q = 1
```

を証明すること。

### 2.3. Prime support facts

`q ∈ m.factorization.support` から次が得られる。

```text
q is prime
q ∣ m
1 ≤ m.factorization q
```

既存補題:

```lean
one_le_factorization_of_mem_support
```

Mathlib 側の support / factorization prime lemmas を reconnaissance で確認し、独自補題を増やさない。

## 3. Mathematical spine

`a := T.a`、`b := T.b` と書く。

一般 GN は、

$$GN_p(a,b)=\frac{(a+b)^p-b^p}{a}$$

に対応する。

奇素数 `p` に対し、目標 chain は次。

### 3.1. Exceptional support collapse

`q` が exceptional support に属するなら、

```text
q ∈ factorization.support (GN p a b)
q ∣ p
```

である。

support から `q` は prime、`hp : Prime p` と `q ∣ p` から、

$$q=p$$

を得る。

候補補題:

```lean
theorem eq_exp_of_mem_exceptional_support_prime_exp
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : q ∈ (GN p a b).factorization.support)
    (hqexp : q ∣ p) :
    q = p
```

この補題は ABC triple に依存しない。

### 3.2. Detection modulo p

素数 `p` では中間二項係数が `p` で割れるため、

$$GN_p(a,b)\equiv a^{p-1}\pmod p$$

となる。

したがって、

$$p\mid GN_p(a,b)\Longrightarrow p\mid a^{p-1}\Longrightarrow p\mid a$$

候補補題:

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime_exp
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

実装候補:

1. general binomial coefficient congruence;
2. an existing theorem about `gcd gap GN` specialized to prime exponent plus an additional nonzero argument;
3. direct finite expansion only for the initial `p = 5` checkpoint.

ここは reconnaissance の Outcome に応じて選ぶ。

### 3.3. Coprime boundary removes p from b

ABC triple では `T.hcop : Coprime T.a T.b` がある。

$$p\mid a\quad\Longrightarrow\quad p\nmid b$$

候補補題は新設せず、`Nat.Coprime` API を直接使う。

### 3.4. Exact valuation one

必要な局所定理は、

$$p\mid GN_p(a,b)\Longrightarrow p^2\nmid GN_p(a,b)$$

または同値な、

$$v_p(GN_p(a,b))=1$$

である。

#### Route A: binomial modulo p²

`p ∣ a`、`p ∤ b` とする。

二項展開では、

$$GN_p(a,b)=p b^{p-1}+\sum_{j=2}^{p-1}\binom pj a^{j-1}b^{p-j}+a^{p-1}$$

中間項は `p` を係数に持ち、さらに `a` を一つ以上持つので `p²` で割れる。`a^{p-1}` も `p ≥ 3` より `p²` で割れる。

したがって、

$$GN_p(a,b)\equiv p b^{p-1}\pmod{p^2}$$

`p ∤ b` より右辺は `p²` で割れず、valuation は正確に一。

#### Route B: LTE

`c := a+b` とする。

`p ∣ a = c-b`、`p ∤ b`、`p ∤ c` より、奇素数 LTE で

$$v_p(c^p-b^p)=v_p(c-b)+v_p(p)=v_p(a)+1$$

一方、

$$c^p-b^p=a\,GN_p(a,b)$$

なので valuation の加法性から、

$$v_p(GN_p(a,b))=1$$

となる。

#### Selection rule

```text
prefer existing trusted LTE API if theorem matching is direct
otherwise use explicit modulo-p² binomial route
```

一般化のために巨大な cyclotomic / algebraic-number dependency を追加しない。

候補 theorem:

```lean
theorem padicValNat_GN_prime_exp_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1
```

または factorization へ直接着地する。

```lean
theorem factorization_GN_prime_exp_eq_one_of_mem_support
    {p a b : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∈ (GN p a b).factorization.support) :
    (GN p a b).factorization p = 1
```

## 4. Fixed exponent five checkpoint

一般 proof の前に、指数 `5` で theorem surface と sum closure を検証する。

### 4.1. Arithmetic shape

一般 GN の `p = 5` specialization は、局所座標で

$$GN_5(a,b)=a^4+5a^3b+10a^2b^2+10ab^3+5b^4$$

となる。

mod `5` では、

$$GN_5(a,b)\equiv a^4\pmod5$$

`5 ∣ GN₅` なら `5 ∣ a`。

mod `25` では `5 ∣ a` のもとで、

$$GN_5(a,b)\equiv5b^4\pmod{25}$$

`Coprime a b` より `5 ∤ b` なので、`25 ∤ GN₅`。

### 4.2. Dependency boundary

FLT5 側には同じ多項式観測があるが、ABC module から FLT module を import しない。

許可するもの:

```text
read-only comparison with DkMath.FLT.Five.GN5
reuse of a genuinely general theorem after moving it to the correct owner module
```

禁止するもの:

```text
DkMath.ABC -> DkMath.FLT.Five dependency
copying a large FLT5 proof tower
using FLT5 final theorem as arithmetic input
```

## 5. Sum closure

局所 valuation theorem が得られた後、`GNExceptionalValuationExcess` を unfold する。

```lean
classical
unfold GNExceptionalValuationExcess
refine Finset.sum_eq_zero ?_
intro q hq
```

`hq` を support membership と `q ∣ p` に分解し、`q = p` を得る。

次に factorization multiplicity を一へ置換する。

```text
factorization q - 1 = 0
real cast = 0
summand = 0
```

`Real.log q` の評価や positivity は不要。multiplicity factor 自体がゼロになる。

この設計により、解析層を一切使わず有限算術だけで M1 を閉じる。

## 6. Budget bridge

zero theorem から次を得る。

```lean
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

定義を展開すると目標は、

$$0\le0\cdot\log\operatorname{rad}(abc)+0$$

なので `simp` で閉じる。

さらに split composition の caller-facing theorem を置く価値がある。

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (hexn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

これは既存 `GNValuationExcessBudgetAffine.of_split` に zero exceptional budget を投入する薄い wrapper とする。

最終 contract 全体をこの branch で再設計しない。

## 7. Proposed modules

### Preferred minimal layout

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

役割:

```text
odd-prime local valuation
factorization multiplicity one
exceptional finite sum zero
zero affine budget
split-budget wrapper
```

### Split layout, only if general GN arithmetic becomes reusable

```text
DkMath/NumberTheory/GN/OddPrimeExceptional.lean
  general GN congruence and valuation-one results

DkMath/ABC/GNOddPrimeExceptionalExcess.lean
  Triple wrapper, sum zero, budget bridge
```

新しい aggregator import は M1 theorem 完成後に判断する。

## 8. Verification

Focused build candidate:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
```

必要なら existing aggregate:

```text
lake build DkMath.ABC.GNFinalBudgetBridge
```

Axiom audit candidate:

```lean
#print axioms DkMath.ABC.Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
#print axioms DkMath.ABC.Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

許容される標準依存:

```text
propext
Classical.choice
Quot.sound
```

## 9. Stop conditions

次の場合は一般化を止め、固定指数 `5` の成果を確定して設計へ戻る。

```text
1. general LTE API requires a large unrelated dependency tower
2. general binomial congruence causes broad refactoring
3. theorem statement needs hidden assumptions not present in Triple
4. p = 2 contaminates the odd-prime proof surface
5. factorization/padic bridge is missing and requires a separate foundational module
```

固定 `5` theorem だけでも、`ABCGNFinalBudgetContract` の候補指数を `n = 5` と選ぶ route では M1 を完全消去できる。

一般奇素数化は望ましいが、M1 討伐の必須条件ではない。

## 10. Non-circularity audit

M1 proof は次だけを使う。

```text
ABC triple coprimality
GN binomial / difference-power identity
prime divisibility
p-adic valuation or square-divisibility
finite factorization support
```

使ってはならないもの:

```text
ABC inequality
abc_main_axiom
uniform valuation budget assumption
GNExceptionalExcessBudgetAffine as an input
FLT5 no-solution theorem
probabilistic or density assumptions
```

これにより、zero exceptional budget は最終 ABC contract の独立した算術入力として成立する。