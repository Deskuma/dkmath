# M1-004 Report: 一般奇素数 GN valuation-one kernel

Date: 2026-07-26  
Outcome: **完了 — 任意の奇素数指数で局所 valuation / factorization が正確に 1**

## 1. 実装

変更ファイル:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

追加 import:

```lean
import DkMath.NumberTheory.WeightedGNBridge
```

この import から prime row の既存 GN 分解を再利用した。新しい neutral
helper module は作成していない。`GNExceptionalExcessFive.lean`、
`GNFinalBudgetBridge.lean`、aggregator、FLT module は変更していない。

## 2. 公開 theorem surface

追加した theorem は次の 4 本。

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)

theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a

theorem padicValNat_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1

theorem factorization_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    (GN p a b).factorization p = 1
```

positivity / nonzero 仮定は公開 surface に追加していない。

## 3. 採用した proof route

primary route を採用した。

```text
prime row GN congruence
  -> p ∣ GN implies p ∣ a
  -> Coprime a b implies p ∤ b and p ∤ a+b
  -> GN = geometric quotient
  -> emultiplicity_geom_sum₂_eq_one over ℤ
  -> Int / Nat emultiplicity bridge
  -> padicValNat = 1
  -> factorization = 1
```

LTE route は不要だった。

## 4. GN / geometric-sum bridge

既存恒等式:

```lean
cosmic_id_csr p a b
geom_sum₂_mul_add a b p
```

はいずれも、それぞれ `GN p a b` と geometric sum に `a` を掛けたものへ
同じ power gap を与える。`a ≠ 0` の場合は積の等式から Nat cancellation
で quotient を同一視した。

`a = 0` は positivity を追加せず明示分岐し、canonical zero evaluation:

```lean
DkMath.CosmicFormula.GN_zero_eval
```

と Mathlib:

```lean
geom_sum₂_self
```

により同じ値 `p * b^(p-1)` へ簡約した。したがって
`GN_eq_geom_sum₂` 自体が全自然数座標で成立する。

## 5. `p ∣ GN` から `p ∣ a`

既存 theorem:

```lean
DkMath.NumberTheory.prime_exists_GN_eq_mul_add_rightBoundary
```

の正確な形:

```lean
Nat.Prime p →
  ∃ B, GN p a b = p * B + a ^ (p - 1)
```

を使用した。`p ∣ GN` と `p ∣ p*B` から `p ∣ a^(p-1)` を得て、

```lean
Nat.Prime.dvd_of_dvd_pow
```

で `p ∣ a` へ着地した。有限列挙や固定指数展開は使用していない。

## 6. Coprimality と `p ∤ a+b`

`hcop : Nat.Coprime a b` と `p ∣ a` から:

```lean
hcop.coprime_dvd_left
Nat.Prime.coprime_iff_not_dvd
```

を用いて `p ∤ b` を得た。さらに `Nat.dvd_add_iff_left` により、
仮に `p ∣ a+b` なら `p ∣ b` となるため矛盾する。

整数へは:

```lean
Int.natCast_dvd_natCast
Nat.prime_iff_prime_int
```

で輸送した。

## 7. Mathlib multiplicity theorem と transfer

中心 theorem:

```lean
emultiplicity_geom_sum₂_eq_one
```

使用した specialization の正確な入力は:

```text
R = ℤ
x = (a+b : ℕ) cast to ℤ
y = b cast to ℤ
Prime (p : ℤ)
Odd p
(p : ℤ) ∣ x-y
¬ (p : ℤ) ∣ x
```

であり、結論は:

```lean
emultiplicity (p : ℤ)
  (∑ i ∈ range p, x^i * y^(p-1-i)) = 1
```

である。

`GN_eq_geom_sum₂` を cast し、次で自然数 multiplicity へ戻した。

```lean
Int.natCast_emultiplicity
```

得られた `emultiplicity p (GN p a b) = 1` から `GN ≠ 0` も内部導出し、
`Fact p.Prime` を局所供給して:

```lean
padicValNat_eq_emultiplicity
```

により `padicValNat = 1` を得た。最後に:

```lean
Nat.factorization_def
```

で factorization endpoint へ輸送した。

## 8. 検証

focused build:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
Build completed successfully (8326 jobs).
```

一時 audit module から追加 4 theorem に `#print axioms` を実行した。
全 theorem の依存は:

```text
propext
Classical.choice
Quot.sound
```

のみであり、新規 project axiom はない。`sorry`、`axiom`、
`native_decide`、有限列挙による一般証明は追加していない。

## 9. Stop boundary

M1-004 の local odd-prime kernel は完成した。指示どおり、

```text
M1-005 odd-prime exceptional finite-sum closure
M1-006 integration
M2 / M3
aggregator changes
```

には進んでいない。

