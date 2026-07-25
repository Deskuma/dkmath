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
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0
```

Budget wrapper:

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

M1-002〜004 の結果により positivity は不要である。

## 2. Mathematical reduction

Exceptional support 上の `q` は:

```text
q ∈ (GN p T.a T.b).factorization.support
q ∣ p
```

を満たす。

factorization support から `q.Prime`、さらに `p.Prime` と `q ∣ p` から:

```text
q = p
```

を得る。

したがって M1 全体は次の一局所命題へ圧縮される。

```text
p ∣ GN p a b
  -> (GN p a b).factorization p = 1
```

その後、各 exceptional summand は:

```text
((1 - 1 : ℕ) : ℝ) * Real.log p = 0
```

となる。

## 3. Existing and completed API

### 3.1. Boundary–GN overlap

既存 theorem:

```lean
Triple.gcd_boundary_GN_dvd_exp
Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
```

意味:

$$q\mid T.a\quad\land\quad q\mid GN_n(T.a,T.b)\quad\Longrightarrow\quad q\mid n$$

### 3.2. Prime-row GN congruence

`DkMath.NumberTheory.WeightedGNBridge` は:

```lean
prime_exists_GN_eq_mul_add_rightBoundary
```

を供給する。

```text
GN p a b = p * B + a^(p-1)
```

従って:

```text
p ∣ GN -> p ∣ a^(p-1) -> p ∣ a
```

M1-004 では次を完成した。

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

### 3.3. GN/geometric quotient bridge

M1-004 は全自然数座標で:

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b)^i * b^(p - 1 - i)
```

を証明した。

`a ≠ 0` では `cosmic_id_csr` と `geom_sum₂_mul_add` の cancellation、`a = 0` では `GN_zero_eval` と `geom_sum₂_self` を使う。

### 3.4. Odd-prime exact valuation

M1-004 の主結果:

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

Proof route:

```text
p ∣ GN
  -> p ∣ a
  -> Coprime a b gives p ∤ a+b
  -> GN = geometric quotient
  -> emultiplicity_geom_sum₂_eq_one over ℤ
  -> Int/Nat multiplicity transfer
  -> padicValNat = 1
  -> factorization = 1
```

## 4. Fixed exponent five certificate

M1-002 は一般 theorem とは独立に、指数 `5` の明示算術 certificate を作った。

$$GN_5(a,b)=a^4+5a^3b+10a^2b^2+10ab^3+5b^4$$

mod `5`:

$$GN_5(a,b)\equiv a^4\pmod5$$

`5 ∣ a` の下で mod `25`:

$$GN_5(a,b)\equiv5b^4\pmod{25}$$

`Coprime a b` より:

```text
5 ∣ GN
25 ∤ GN
v_5(GN) = 1
```

この fixed-five proof は general multiplicity proof の regression certificate として残す。

## 5. M1-005 finite-sum closure

Preferred module:

```text
DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

Expected imports:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

Target proof:

```lean
classical
unfold GNExceptionalValuationExcess
apply Finset.sum_eq_zero
intro q hq
```

Then:

```text
hq
  -> hqSupport and hqDvdP
  -> q.Prime
  -> q = p
  -> support gives p ∣ GN
  -> factorization_GN_prime_eq_one_of_dvd hp hpOdd T.hcop hpGN
  -> simp
```

No positivity hypotheses are required.

## 6. Budget bridge

Zero theoremから:

```lean
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

を thin wrapper として得る。

定義展開後は:

$$0\le0\cdot\log\operatorname{rad}(abc)+0$$

となる。

Optional caller-facing wrapper:

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (T : Triple) {p : ℕ} {τn Dn : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

これは:

```lean
GNValuationExcessBudgetAffine.of_split
```

へ exceptional zero budget と `hn` を投入する薄い theorem に限定する。

## 7. Contract consequence

M1 討伐前:

```text
σ + (τe + τn)
```

M1 討伐後:

```text
τe = 0
De = 0
σ + τn
```

したがって残る敵は:

```text
M2 lifted-radical support growth
M3 non-exceptional valuation excess
```

## 8. Module ownership audit

Current local arithmetic owner:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

次は ABC triple を主語にしない neutral theorem である。

```lean
GN_eq_geom_sum₂
prime_dvd_boundary_of_dvd_GN_prime
```

M1-006 で次を自己判断する。

```text
A. 現在の ABC owner を維持
B. NumberTheory / CosmicFormula owner へ移動し ABC 側を薄くする
```

移動は、再利用・依存方向・API discoverability の利得が churn を上回る場合だけ行う。

## 9. Verification

Focused builds:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
lake build DkMath.ABC.GNExceptionalExcessOddPrime
lake build DkMath.ABC.GNFinalBudgetBridge
```

Public aggregator を変更した場合のみ broader build を追加する。

Axiom audit:

```lean
#print axioms DkMath.ABC.Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
#print axioms DkMath.ABC.Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

Trust boundary:

```text
no new axiom
no sorry
no native_decide
```

## 10. Dual-Brain execution model

Codex と Wise Wolf は peer reasoning agents である。

```text
not master/subordinate
not planner/transcriber
two search paths
one Lean kernel judge
```

設計書は地図であり、固定命令列ではない。

Codex は repository evidence に基づき:

```text
theorem name を改善
module owner を変更
micro-checkpoint を挿入
機械的に連続する checkpoint を融合
planned route より強い route を採用
```

できる。

checkpoint は report と theorem surface を固定する監査点であり、permission gate ではない。

完了後は:

```text
result evaluation
remaining Gap analysis
next strongest action
implementation
verification
report
continued progression
```

を自律的に続ける。

M1-005 後は M1-006 integration/audit へ直ちに進む。

## 11. Post-M1 route

M1 完了後、Codex は M2/M3 の現在地を調査し、次の最大 leverage route を選定する。

候補:

```text
M2 support-growth reconnaissance
M3 non-exceptional depth reconnaissance
support-depth combined tradeoff
shared neutral valuation/support lemma
```

元の順序ではなく数学的 leverage で決める。

Branch hygiene:

```text
M1 implementation remains in M1 branch
M2/M3 implementation belongs to a new campaign branch
neutral prerequisites may be factored when ownership is clear
```

## 12. Absolute boundaries

```text
no abc_main_axiom modification
no ABC -> FLT.Five production dependency
no FLT7 WIP dependency
no unrelated refactor
no new axiom
no sorry
no native_decide proof
no finite enumeration as general proof
```

これらは trust/dependency invariant であり、主従関係による停止命令ではない。
