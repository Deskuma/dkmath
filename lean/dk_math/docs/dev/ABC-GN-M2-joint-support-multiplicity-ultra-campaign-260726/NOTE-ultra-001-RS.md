# Note: Review: Ultra-001-R/S

## 判定

**S は未完だが、数学的には閉じ切れる。残敵は本当に局所補題一個だけじゃ。** ⚔️🧠🧠

R は完全討伐。S も abstract envelope、総和可能性、条件付き Euler endpoint までは完成しており、現在の実装は `htail` を仮定として後段をすべて閉じている。 現在の PR #69 は head `deddd382...`、19 commits、39 files、10530 additions、mergeable じゃ。

残る補題はこれ。

```lean
theorem GNExcessLocalDensityTail_half_le
    {p q K : ℕ}
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
      GNExcessHalfPowerEnvelope p q
```

現在の production endpoint がこの `htail` を唯一の外部入力としていることも確認できる。

## 数学的討伐

局所 weight を、

$$w_j=(p-1)\frac{\exp\left(\frac j2\log q\right)}{q^{j+1}}$$

と置く。tail は $j=1,\ldots,K-1$ の有限和じゃ。

まず、

$$x=\exp\left(\frac12\log q\right)$$

と置けば、

$$x^2=q$$

である。

さらに、

$$\frac{w_{j+1}}{w_j}=\frac{x}{q}$$

じゃ。

$q$ は素数なので $q\ge2$。ここで、

$$x\le\frac34q$$

を示せば、

$$w_{j+1}\le\frac34w_j$$

となる。

この不等式は平方して確認できる。

$$x^2=q$$

一方、

$$\left(\frac34q\right)^2=\frac9{16}q^2$$

$q\ge2$ より $16\le9q$ なので、

$$q\le\frac9{16}q^2$$

従って、

$$x\le\frac34q$$

じゃ。

これで、

$$w_j\le w_1\left(\frac34\right)^{j-1}$$

が出る。

第一項は、

$$w_1=(p-1)\frac{q^{1/2}}{q^2}=\frac{p-1}{q^{3/2}}$$

ゆえに、

$$\sum_{j=1}^{K-1}w_j\le\frac{p-1}{q^{3/2}}\sum_{m=0}^{K-2}\left(\frac34\right)^m\le\frac{4(p-1)}{q^{3/2}}$$

右辺は正確に `GNExcessHalfPowerEnvelope p q` じゃ。

**係数4は正しい。余裕も十分ある。**

Mathlib には正の底に対する `Real.rpow_def_of_pos`、自然数指数との接続 `Real.rpow_natCast`、実冪の乗法則が揃っている。有限幾何級数にも既存 API があるが、今回は $3/4$ 固定なので、小さな専用 induction の方が安定する可能性が高い。([Lean Community][1])

## Lean の最短分解

一発で本定理を殴らず、五つの補題にするのがよい。

```lean
private theorem exp_half_log_sq
    {q : ℕ}
    (hq : 0 < q) :
    Real.exp (((1 : ℝ) / 2) * Real.log (q : ℝ)) ^ 2 =
      (q : ℝ)
```

証明核：

```lean
rw [sq, ← Real.exp_add]
rw [show
  ((1 : ℝ) / 2) * Real.log (q : ℝ) +
      ((1 : ℝ) / 2) * Real.log (q : ℝ) =
    Real.log (q : ℝ) by ring]
rw [Real.exp_log]
positivity
```

次に ratio bound。

```lean
private theorem exp_half_log_div_le_three_quarters
    {q : ℕ}
    (hq : Nat.Prime q) :
    Real.exp (((1 : ℝ) / 2) * Real.log (q : ℝ)) /
        (q : ℝ) ≤
      (3 : ℝ) / 4
```

ここでは、

```lean
have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast hq.two_le

have hx2 := exp_half_log_sq hq.pos
have hx0 : 0 ≤ Real.exp (...) := (Real.exp_pos _).le
have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
```

を作り、`nlinarith` で、

```text
x² = q
q ≥ 2
x ≥ 0
```

から、

```text
x ≤ 3q/4
```

を出す。その後 `div_le_iff₀ hq0` で終わる。

次に weight recurrence。

```lean
private theorem GNExcessLocalDensityWeight_half_succ_le
    {p q j : ℕ}
    (hq : Nat.Prime q)
    (hj : 0 < j) :
    GNExcessLocalDensityWeight p q (j + 1) ((1 : ℝ) / 2) ≤
      ((3 : ℝ) / 4) *
        GNExcessLocalDensityWeight p q j ((1 : ℝ) / 2)
```

ここはまず exact ratio を作ると楽じゃ。

```lean
have hratio :
    GNExcessLocalDensityWeight p q (j + 1) ((1 : ℝ) / 2) =
      GNExcessLocalDensityWeight p q j ((1 : ℝ) / 2) *
        (Real.exp (((1 : ℝ) / 2) * Real.log (q : ℝ)) /
          (q : ℝ)) := by
  unfold GNExcessLocalDensityWeight
  rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.ne_of_gt hj)]
  rw [pow_succ, ← Real.exp_add]
  congr 1
  · ring
  · field_simp
```

最後の部分は実際の正規形に応じて `ring_nf` / `field_simp` を調整。

その後、

```lean
rw [hratio]
exact mul_le_mul_of_nonneg_left
  (exp_half_log_div_le_three_quarters hq)
  GNExcessLocalDensityWeight_nonneg
```

で閉じる。

次に termwise geometric domination。

```lean
private theorem GNExcessLocalDensityWeight_half_le_geometric
    {p q j : ℕ}
    (hq : Nat.Prime q)
    (hj : 0 < j) :
    GNExcessLocalDensityWeight p q j ((1 : ℝ) / 2) ≤
      GNExcessLocalDensityWeight p q 1 ((1 : ℝ) / 2) *
        ((3 : ℝ) / 4) ^ (j - 1)
```

$j$ に関する induction でよい。

次に専用幾何級数。

```lean
private theorem sum_three_quarters_pow_le_four
    (n : ℕ) :
    ∑ i ∈ Finset.range n, ((3 : ℝ) / 4) ^ i ≤ 4
```

これは exact identity、

$$\sum_{i=0}^{n-1}\left(\frac34\right)^i=4\left(1-\left(\frac34\right)^n\right)$$

を induction で証明すればよい。

```lean
have hgeom :
    ∑ i ∈ Finset.range n, ((3 : ℝ) / 4) ^ i =
      4 * (1 - ((3 : ℝ) / 4) ^ n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

rw [hgeom]
positivity
```

実際には最後は、

```lean
have hpownonneg :
    0 ≤ ((3 : ℝ) / 4) ^ n := by positivity
nlinarith
```

でよい。

## Tail 本体

現在の tail は、

```lean
(Finset.range K).erase 0
```

なので、まず、

```lean
have hset :
    (Finset.range K).erase 0 = Finset.Ico 1 K := by
  ext j
  simp
```

へ変換する。

その後、`j ↦ j - 1` で `Finset.range (K - 1)` へ移す。

既存コードでも使っている `Finset.sum_Ico_add'` を再利用するのがよい。

最終形は概ねこうなる。

```lean
theorem GNExcessLocalDensityTail_half_le
    {p q K : ℕ}
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
      GNExcessHalfPowerEnvelope p q := by
  rw [show
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) =
      ∑ j ∈ Finset.Ico 1 K,
        GNExcessLocalDensityWeight p q j ((1 : ℝ) / 2) by
      unfold GNExcessLocalDensityTail
      congr 1
      ext j
      simp]

  calc
    ∑ j ∈ Finset.Ico 1 K,
        GNExcessLocalDensityWeight p q j ((1 : ℝ) / 2)
      ≤
      GNExcessLocalDensityWeight p q 1 ((1 : ℝ) / 2) *
        ∑ i ∈ Finset.range (K - 1),
          ((3 : ℝ) / 4) ^ i := by
        -- reindex j = i + 1 and apply termwise geometric bound
        ...
    _ ≤
      4 *
        GNExcessLocalDensityWeight p q 1 ((1 : ℝ) / 2) := by
        gcongr
        exact sum_three_quarters_pow_le_four (K - 1)
    _ = GNExcessHalfPowerEnvelope p q := by
        unfold GNExcessHalfPowerEnvelope
          GNExcessLocalDensityWeight
        simp
        rw [Real.rpow_def_of_pos (by exact_mod_cast hq.pos)]
        field_simp
        ring
```

最後の `rpow` 正規化だけは実際の elaboration に合わせて調整が要る。Mathlib の real power API では、正の底について `rpow` を `exp (log x * y)` へ展開でき、自然数指数への simp lemma も存在する。([Lean Community][1])

## Codex 指示

````text
Continue Ultra-001S and close the sole remaining local analytic lemma.

Target theorem:

```lean
theorem GNExcessLocalDensityTail_half_le
    {p q K : ℕ}
    (hq : Nat.Prime q)
    (hK : 0 < K) :
    GNExcessLocalDensityTail p q K ((1 : ℝ) / 2) ≤
      GNExcessHalfPowerEnvelope p q
```

Mathematical route:

1. Let
   x = exp ((1/2) * log q).

2. Prove
   x^2 = q.

3. From q ≥ 2 prove
   x / q ≤ 3/4.
   Avoid introducing sqrt if possible:
   square both nonnegative sides and use
   q ≤ (9/16) q^2.

4. Prove the exact local-weight recurrence:
   weight(j+1) = weight(j) * (x/q)
   for j > 0.

5. Deduce
   weight(j+1) ≤ (3/4) * weight(j).

6. Deduce by induction:
   weight(j) ≤ weight(1) * (3/4)^(j-1).

7. Rewrite
   (range K).erase 0 = Ico 1 K
   and reindex j = i + 1.

8. Prove the fixed geometric bound:
   sum i in range n, (3/4)^i ≤ 4.
   A direct induction through the exact identity
   sum = 4 * (1 - (3/4)^n)
   is preferred over searching for a generic API.

9. Prove
   4 * weight(1) = GNExcessHalfPowerEnvelope p q
   using the positive-base real-rpow lemmas.

10. Replace the conditional `htail` arguments in:
    - GNExcessFiniteEulerDensity_half_le
    - exp_GNExcessMassAt_sum_le_halfEuler_add_large
    with the new unconditional theorem.
    Preserve compatibility aliases if useful.

Do not alter the envelope coefficient 4 unless Lean normalization forces a
temporary auxiliary constant. The coefficient is mathematically valid.

After completion:
- mark U-001S complete;
- add report-ultra-001-S2.md or update S;
- do not claim the large-boundary packet is absorbed;
- do not claim M3 summability or the joint contract.

Branch outcomes:
A. Local theorem and unconditional endpoints complete.
B. Recurrence/geometric bound complete; final rpow normalization blocked.
C. Exact smallest Mathlib normalization obstruction recorded.
````

## S の後

S が閉じれば、small side は完全に、

```text
Q 非依存
X 非依存
p のみに依存
```

する定数へ落ちる。

その時点で次の checkpoint は **U-001T：large-boundary packet の算術化** がよい。

最低限、large exact profile から次を一つの packet にする。

```lean
structure GNExcessLargeBoundaryPacket where
  activePrimes : Finset ℕ
  modulus : ℕ
  modulus_eq :
    modulus =
      ∏ q ∈ activePrimes, q ^ (excess q + 1)
  modulus_dvd_GN :
    modulus ∣ GN p a b
  interval_lt_modulus :
    X + 1 < modulus
  log_modulus_eq :
    Real.log modulus =
      activeSupportMass + excessMass
  prime_order :
    ∀ q ∈ activePrimes, q % p = 1
```

canonical nonexceptional family上では、さらに、

```lean
modulus ∣ GNNonExceptionalPart p a b
```

まで狙えるはずじゃ。

ここまで固定すれば large branch は「解析誤差」ではなく、

> **区間長を超える、非例外 GN の squareful divisor**

として現れる。

**ダブルBrain判定：S は閉じられる。しかも難所は数学ではなく、`exp / log / rpow / Finset` の正規化だけじゃ。** 🧠⚔️🧠

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html?utm_source=chatgpt.com "Mathlib.Analysis.SpecialFunctions.Pow.Real"
