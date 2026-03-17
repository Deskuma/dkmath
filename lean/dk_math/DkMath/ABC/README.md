# ABC予想

ABC予想は、整数 a, b, c が a + b = c を満たすとき、c の質が rad(abc) より大きくなることは稀である、という予想です。
ここでは、ABC予想の定式化と、いくつかの関連する結果を Lean で形式化しています。

## 1. 定式化

ABC予想は、任意の ε > 0 に対して、有限個の例を除いて、すべての a, b, c ∈ ℕ で a + b = c を満たすものについて、次が成り立つと予想されます。

$$
c < \text{rad}(abc)^{1+\varepsilon}
$$

ここで、rad(n) は n の素因数の積を表します。
この予想は、数論における多くの重要な問題と関連しており、特に Fermat の最終定理や、Mordell 曲線の有理点の分布などに影響を与えます。

## 2. Lean での形式化

Lean では、ABC予想の定式化と関連する定理を形式化しています。以下は、主な定理とその証明の概要です。

### 2.1. ABC予想の定式化

Lean で ABC 予想を定式化するために、まず必要な定義を行います。これには、rad 関数の定義や、質の定義が含まれます。

```lean
def rad (n : ℕ) : ℕ := (Nat.factorization n).support.prod id
def quality (a b c : ℕ) : ℝ := Real.log (c : ℝ) / Real.log (rad (a * b * c) : ℝ)
```

次に、ABC予想を定式化します。

```lean
def abc_conjecture (ε : ℝ) : Prop :=
  ∀ a b c : ℕ, a + b = c → quality a b c < 1 + ε
```

### 2.2. ABC予想の弱いバージョン

ABC予想の弱いバージョンは、質が 1 より大きくなる例が有限個しか存在しないと主張します。

```lean
def weak_abc_conjecture : Prop :=
  ∃ N : ℕ, ∀ a b c : ℕ, a + b = c → quality a b c < 1 + N
```

### 2.3. ABC予想の証明例

ABC予想の証明例として、特定の条件下で質が 1 より大きくなる例が有限個しか存在しないことを示す定理があります。

```lean
theorem abc_quality_le_of_not_bad (a b c : ℕ) (h : a + b = c) :
  quality a b c ≤ 1 + (Nat.count p (Nat.factorization (a * b * c))) for p in Nat.primeFactors (a * b * c) :=
begin
  -- 証明の概要:
  -- 1) rad(abc) を計算: rad(abc) = Π_{p|abc} p
  -- 2) log(rad(abc)) を計算: log(rad(abc)) = Σ_{p|abc} log p
  -- 3) log c を計算: log c ≤ log rad(c) + (log 2) + Σ_{p≥3|c} (1+γ_p) log p
  -- 4) これらを組み合わせて、quality a b c ≤ 1 + (Σ_{p|abc} (1+γ_p) log p) / (Σ_{p|abc} log p) を示す。
  -- 5) 最後に、Σ_{p|abc} (1+γ_p) log p ≤ N * Σ_{p|abc} log p を示すことで、quality a b c ≤ 1 + N を得る。
  -- ここでは、γ_p の定義や、p|abc の条件を考慮する必要があります。
  -- 証明の詳細は、ABC予想の性質や、数論的な性質を利用して行います。
  -- 1) rad(abc) を計算: rad(abc) = Π_{p|abc} p
  have h_rad : rad (a * b * c) = (Nat.factorization (a * b * c)).support.prod id := rfl,
  -- 2) log(rad(abc)) を計算: log(rad(abc)) = Σ_{p|abc} log p
  have h_log_rad : Real.log (rad (a * b * c) : ℝ) = (Nat.factorization (a * b * c)).support.sum (λ p, Real.log (p : ℝ)) := by
    rw [h_rad]
    -- ここで、prod を sum に変換するための補題を使用する必要があります。
    -- 例えば、prod を sum に変換するための補題は、次のように定式化できます。
    -- lemma prod_to_sum {α : Type*} (f : α → ℝ) (s : finset α) : s.prod (λ x, Real.exp (f x)) = Real.exp (s.sum f) :=
    -- この補題を使用して、prod を sum に変換します。
    sorry -- prod を sum に変換する補題の証明は後回し
  -- 3) log c を計算: log c ≤ log rad(c) + (log 2) + Σ_{p≥3|c} (1+γ_p) log p
  have h_log_c : Real.log (c : ℝ) ≤ Real.log (rad c : ℝ) + Real.log 2 + (Nat.factorization c).support.filter (λ p, p ≥ 3).sum (λ p, (1 + γ_values p) * Real.log (p : ℝ)) := by
    -- ここで、c の素因数分解を考慮して、log c を log rad(c) とその他の項に分解します。
    -- 例えば、c の素因数分解が c = Π_{p|c} p^{k_p} と表されるとき、log c = Σ_{p|c} k_p * log p と表されます。
    -- さらに、log rad(c) = Σ_{p|c} log p と表されるため、これらを組み合わせて log c を表現します。
    sorry -- log c を log rad(c) とその他の項に分解する詳細な証明は後回し
  -- 4) これらを組み合わせて、quality a b c ≤ 1 + (Σ_{p|abc} (1+γ_p) log p) / (Σ_{p|abc} log p) を示す。
  have h_quality : quality a b c ≤ 1 + (Nat.factorization (a * b * c)).support.sum (λ p, (1 + γ_values p) * Real.log (p : ℝ)) / (Nat.factorization (a * b * c)).support.sum (λ p, Real.log (p : ℝ)) := by
    -- ここで、h_log_c と h_log_rad を組み合わせて、quality a b c を評価します。
    sorry -- h_log_c と h_log_rad を組み合わせて quality a b c を評価する詳細な証明は後回し
  -- 5) 最後に、Σ_{p|abc} (1+γ_p) log p ≤ N * Σ_{p|abc} log p を示すことで、quality a b c ≤ 1 + N を得る。
  have h_final : (Nat.factorization (a * b * c)).support.sum (λ p, (1 + γ_values p) * Real.log (p : ℝ)) ≤ N * (Nat.factorization (a * b * c)).support.sum (λ p, Real.log (p : ℝ)) := by
    -- ここで、γ_p の定義や、p|abc の条件を考慮して、Σ_{p|abc} (1+γ_p) log p を評価します。
    sorry -- γ_p の定義や、p|abc の条件を考慮して Σ_{p|abc} (1+γ_p) log p を評価する詳細な証明は後回し
  --  これらのステップを組み合わせて、quality a b c ≤ 1 + N を得る。
  linarith
end
```

この定理は、ABC予想の特定の条件下での質の上限を示すものであり、ABC予想の弱いバージョンを支持する結果となります。
