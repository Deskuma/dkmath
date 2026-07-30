# M1-004 Review: 一般奇素数 GN valuation-one kernel

Date: 2026-07-26  
Reviewed commit: `97c1558f883cc1f9ef56b81bd64940b64a09ba6b`  
Decision: **全面採用**

## 1. 総合判定

```text
重大問題       0
主要問題       0
修正必須事項   0
```

M1-004 は、固定指数 `5` の局所算術を単に抽象化したのではなく、canonical `GN` を geometric quotient と同一視し、Mathlib の一般 multiplicity theorem へ正しく接続した。

完成した局所核は次である。

```lean
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

positivity 仮定を必要とせず、任意の奇素数指数で成立する。

## 2. `GN_eq_geom_sum₂` の監査

追加 theorem:

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
```

は数学的に正しい。

`a ≠ 0` では、

```text
cosmic_id_csr
geom_sum₂_mul_add
```

が同じ power gap を、それぞれ `a * GN` と `a * geometricSum` として表す。自然数上で正の `a` を cancellation して quotient を同一視している。

`a = 0` では cancellation を乱用せず、

```text
GN_zero_eval
geom_sum₂_self
```

により両辺を `p * b^(p-1)` へ落としている。したがって theorem は prime 条件すら不要で、全自然数座標に対する真正な一般 bridge である。

## 3. Prime-row boundary extraction

```lean
prime_exists_GN_eq_mul_add_rightBoundary
```

から、

```text
GN p a b = p * B + a^(p-1)
```

を得ている。

よって `p ∣ GN` なら `p ∣ a^(p-1)`。`p` の素数性により `p ∣ a` へ降りる。

この theorem は固定次数展開や有限列挙に依存せず、Weighted GN の prime-row congruence を正しく再利用している。

## 4. Coprime transport

`hcop : Nat.Coprime a b` と `p ∣ a` から、

```text
p ∤ b
p ∤ a+b
```

を得る流れは正しい。

geometric quotient では、

```text
x = a+b
y = b
x-y = a
```

と置くため、Mathlib theorem の入力、

```text
p ∣ x-y
p ∤ x
```

が完全に揃う。

## 5. Multiplicity transfer

`R = ℤ` として、

```lean
emultiplicity_geom_sum₂_eq_one
```

を適用したのは最短かつ強い route である。

```text
Prime (p : ℤ)
Odd p
(p : ℤ) ∣ ((a+b : ℕ) : ℤ) - (b : ℤ)
¬ (p : ℤ) ∣ ((a+b : ℕ) : ℤ)
```

を供給し、geometric quotient の `emultiplicity` を exact `1` とした。

その後、

```text
GN_eq_geom_sum₂
Int.natCast_emultiplicity
padicValNat_eq_emultiplicity
Nat.factorization_def
```

を順に用いて、

```text
emultiplicity = 1
padicValNat = 1
factorization = 1
```

へ輸送している。

`GN ≠ 0` も `emultiplicity = 1` と `emultiplicity 0 = ⊤` の衝突から内部導出しており、外部仮定を増やしていない。

## 6. Fixed-five theorem との関係

M1-002 の modulo `5` / modulo `25` proof は、一般 theorem に吸収されて不要になったわけではない。

```text
M1-002:
  exponent 5 の明示算術 certificate

M1-004:
  odd-prime geometric quotient / multiplicity certificate
```

という独立した二経路で同じ局所現象を検証している。固定五の定理は regression witness として残す価値がある。

## 7. 配置上の軽微な論点

次の二 theorem は ABC triple を主語にせず、数学的には neutral API である。

```lean
GN_eq_geom_sum₂
prime_dvd_boundary_of_dvd_GN_prime
```

したがって最終的な所有者候補は `NumberTheory` または `CosmicFormula` 側にもある。

ただし、現在の配置は依存方向を壊しておらず、M1-005 を阻害する問題でもない。M1 finite-sum closure を先に完了し、M1-006 integration audit で次を自己判断するのがよい。

```text
A. 現在位置を維持する
B. neutral owner へ移し、ABC 側を薄い import / wrapper にする
```

移動による churn が再利用価値を上回る場合だけ実施する。

## 8. 一歩先の結論

M1-005 は新しい数論を必要としない。

exceptional support 上の任意の `q` について、

```text
q.Prime
q ∣ p
p.Prime
```

から `q = p`。support membership から `p ∣ GN p T.a T.b` を得て、M1-004 の factorization-one theorem を代入すれば各 summand は zero になる。

従って positivity 無しで次が閉じる見込みである。

```lean
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0

 theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

## 9. Dual-Brain workflow decision

checkpoint は permission gate ではなく、監査可能な観測点とする。

Codex は従属実装器ではない。Wise Wolf と Codex は、異なる探索経路を持つ二つの peer reasoning brain である。

したがって今後は、checkpoint 完了後に新しい指示を待たず、次を自ら実行する。

```text
result evaluation
  -> theorem / dependency / remaining Gap analysis
  -> next strongest checkpoint selection
  -> implementation
  -> focused verification
  -> report
  -> continued progression
```

ただし checkpoint ごとの theorem surface・build・report は残し、後から相互監査できる形を維持する。
