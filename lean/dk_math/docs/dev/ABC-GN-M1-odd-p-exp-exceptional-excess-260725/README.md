# ABC–GN M1: Odd-Prime Exponent Exceptional Excess

作成日: 2026-07-25  
Status: **M1 complete / odd-prime exceptional excess defeated**

Repository: `Deskuma/dkmath`  
Base branch: `feature/ABC-GN-valuation-excess-260724-v0`  
Work branch: `wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0`

## 1. Mission

ABC–GN deterministic spine が残した三つの一様予算のうち、第一魔核 M1 を討伐する。

```text
M1  uniform exponent-exceptional valuation excess
M2  uniform lifted-radical support growth
M3  uniform non-exceptional valuation excess
```

本プロジェクトの目標は、指数を奇素数 `p` に固定したとき、指数例外 prime channel の valuation excess が完全に消えることを Lean で証明することである。

最終目標:

```lean
GNExceptionalValuationExcess p T.a T.b = 0
GNExceptionalExcessBudgetAffine T p 0 0
```

すなわち、最終 budget contract の第一成分を:

```text
τe = 0
De = 0
```

へ固定する。

## 2. Current campaign state

```text
M1-000  campaign initialization                              complete
M1-001  theorem/API reconnaissance                           complete / Outcome B
M1-002  exponent-five divisibility and no-lift kernel        complete
M1-003  exponent-five exceptional excess = 0                 complete / minimum victory
M1-004  odd-prime general local valuation-one theorem        complete
M1-005  odd-prime exceptional excess = 0 and budget bridge   complete
M1-006  integration, audit, documentation closure            complete
```

## 3. Existing deterministic spine

基底ブランチには次が実装されている。

```text
DkMath/ABC/GNExceptionalSplit.lean
  Triple.gcd_boundary_GN_dvd_exp
  Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
  Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN

DkMath/ABC/GNValuationExcess.lean
  GNExceptionalValuationExcess
  GNNonExceptionalValuationExcess
  GNValuationExcess_eq_exceptional_add_nonExceptional

DkMath/ABC/GNFinalBudgetBridge.lean
  GNExceptionalExcessBudgetAffine
  GNNonExceptionalExcessBudgetAffine
  GNValuationExcessBudgetAffine.of_split
  ABCGNFinalBudgetContract
```

`GNExceptionalValuationExcess p a b` は、`GN p a b` の factorization support のうち `q ∣ p` を満たす prime `q` に対し、

$$\bigl(v_q(GN_p(a,b))-1\bigr)\log q$$

を合計する。

`p` が素数なら exceptional support は `q = p` の一箇所に潰れる。M1 の核心は、`p` が GN に現れた場合の valuation が正確に一であることを示す点にある。

## 4. Fixed-five minimum victory

M1-002 は一般 `GN` の指数 `5` を明示展開し、

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
  -> factorization 5 = 1
```

を証明した。

M1-003 は finite exceptional support へ接続し、positivity 無しで:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

を完成した。

したがって固定指数 `5` では:

```text
τe = 0
De = 0
```

が確定している。

## 5. General odd-prime local victory

M1-004 は canonical `GN` と geometric quotient の一般 bridge を証明した。

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
```

さらに prime-row boundary congruence から:

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

を得た。

奇素数 `p` と coprime 境界について、Mathlib の `emultiplicity_geom_sum₂_eq_one` を経由し:

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

を完成した。

この theorem も positivity を必要としない。

## 6. Completed odd-prime victory

一般奇素数の local factorization-one theorem を exceptional finite sum へ接続した。

完成 theorem:

```lean
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalValuationExcess p T.a T.b = 0

 theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

証明核:

```text
q in exceptional support
  -> q.Prime
  -> q ∣ p
  -> q = p
  -> support gives p ∣ GN
  -> factorization p = 1
  -> summand = 0
  -> finite sum = 0
```

さらに非例外 budget だけから full valuation budget を供給する production-facing
wrapper も完成した。

```lean
Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
```

公開入口 `DkMath.ABC` は `GNExceptionalExcessOddPrime` を import する。

## 7. Dual-Brain campaign doctrine

Codex と Wise Wolf は、主従関係ではない。

```text
two peer reasoning agents
two search paths
one Lean kernel judge
```

checkpoint は、後から相互監査するための観測点であり、次へ進む許可待ちの関所ではない。

checkpoint 完了後、Codex は次を自己判断する。

```text
結果の数学的意味
新しく確定した Core
残った Gap
依存関係と theorem ownership
次の最有力 route
必要な micro-checkpoint
```

そして新しい指示を待たず、campaign 内の次 checkpoint へ進む。

ただし、次は維持する。

```text
coherent theorem layer
focused build
checkpoint report
reviewable change boundary
```

M1-005 と M1-006 は完了した。M1 は閉じた Core とし、次戦線は M2/M3
専用 campaign で扱う。

## 8. Planned implementation surface

局所 arithmetic owner:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

finite-sum / budget bridge candidate:

```text
DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

配置原則:

```text
一般 GN の合同・geometric quotient・valuation 定理
  -> NumberTheory / CosmicFormula owner も候補

ABC Triple wrapper と budget bridge
  -> DkMath.ABC
```

`GN_eq_geom_sum₂` と prime boundary theorem の最終 ownership は M1-006 で監査する。再利用・依存方向の利得が churn を上回る場合だけ移動する。

## 9. Completion criteria

M1 完了条件:

```text
1. odd-prime exceptional support が singleton 以下へ潰れる
2. support 上の exceptional valuation が exact 1
3. GNExceptionalValuationExcess = 0
4. GNExceptionalExcessBudgetAffine T p 0 0
5. split budget への無損失接続
6. focused build
7. representative endpoint axiom audit
8. dependency and ownership audit
9. FINAL_REPORT
```

## 10. Scope and trust boundary

本プロジェクトは次を主張しない。

```text
ABC conjecture is proved
M2 support-growth budget is solved
M3 non-exceptional high-lift budget is solved
GN is generally squarefree
all composite exponents have zero exceptional excess
prime exponent p = 2 is covered
```

絶対境界:

```text
no modification of abc_main_axiom
no ABC -> FLT.Five production dependency
no FLT7 WIP dependency
no unrelated refactor
no new axiom
no sorry
no native_decide proof
no finite enumeration as general proof
```

これらは主従命令ではなく、Lean trust boundary と repository dependency boundary である。

## 11. Documents

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
CODEX_START.md
report-M1-001.md
report-M1-002.md
review-M1-002.md
report-M1-003.md
review-M1-003.md
report-M1-004.md
review-M1-004.md
instruction-M1-005.md
```

現在の入口は:

```text
CODEX_START.md
```
