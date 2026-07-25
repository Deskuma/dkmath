# ABC–GN M1 ROADMAP

副題: 第一魔核 `uniform exceptional valuation excess` 討伐工程

## 0. Campaign target

最終 summit:

```lean
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

数学的到達点:

$$GNExceptionalValuationExcess\ p\ T.a\ T.b=0$$

$$GNExceptionalExcessBudgetAffine\ T\ p\ 0\ 0$$

対象:

```text
T : ABC Triple
p : odd prime
```

現在の実装結果から positivity は最終 theorem に不要と見込まれる。

最小勝利条件:

```text
p = 5 で上記二定理を完成
```

完全勝利条件:

```text
任意の odd prime p で上記二定理を完成
```

## 1. Checkpoint map

```text
M1-000  campaign initialization                              complete
M1-001  read-only theorem/API reconnaissance                 complete / Outcome B
M1-002  exponent-five divisibility and no-lift kernel        complete
M1-003  exponent-five exceptional excess = 0                 complete / minimum victory
M1-004  odd-prime general local valuation-one theorem        complete
M1-005  odd-prime exceptional excess = 0 and budget bridge   active
M1-006  integration, audit, documentation closure            autonomous continuation
```

各 checkpoint は theorem layer・focused verification・report を持つ。checkpoint は reviewable observation point であり、次 checkpoint へ進むための permission gate ではない。

## 2. M1-000: Campaign initialization

Status: **complete**

Deliverables:

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
work branch
Draft PR
```

## 3. M1-001: Read-only reconnaissance

Status: **complete / Outcome B**

調査結果:

```text
fixed exponent five is immediate
general odd-prime route requires one GN/geometric quotient bridge
Mathlib emultiplicity_geom_sum₂_eq_one is the strongest endpoint
```

選択 route:

```text
M1-002 fixed-five local kernel
M1-003 fixed-five finite sum
M1-004 general odd-prime local kernel
M1-005 general finite sum
```

## 4. M1-002: Exponent-five local kernel

Status: **complete**

完成 theorem:

```lean
five_dvd_boundary_of_dvd_GN_five
not_twentyFive_dvd_GN_five_of_coprime
padicValNat_five_GN_five_eq_one_of_dvd
factorization_five_GN_five_eq_one_of_dvd
```

数学的鎖:

```text
GN 5 a b ≡ a^4 mod 5
5 ∣ GN -> 5 ∣ a
GN 5 (5*k) b = 25*K + 5*b^4
Coprime a b -> 25 ∤ GN
therefore v_5(GN) = 1
```

この明示算術 proof は M1-004 の一般 multiplicity proof と独立した certificate として維持する。

## 5. M1-003: Exponent-five exceptional excess zero

Status: **complete / minimum victory**

完成 theorem:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

positivity assumptions: **none**

結果:

```text
τe = 0
De = 0
```

## 6. M1-004: Odd-prime local valuation-one theorem

Status: **complete**

一般 bridge:

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
```

prime-row boundary theorem:

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

主結果:

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

proof route:

```text
prime row GN congruence
  -> p ∣ GN implies p ∣ a
  -> Coprime a b implies p ∤ a+b
  -> GN = geometric quotient
  -> emultiplicity_geom_sum₂_eq_one over ℤ
  -> Nat emultiplicity
  -> padicValNat = 1
  -> factorization = 1
```

positivity assumptions: **none**

## 7. M1-005: Odd-prime excess zero and budget bridge

Status: **active**

Objective:

一般 local theorem を exceptional finite support sum と final budget API へ接続する。

Preferred module:

```text
DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

Main targets:

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

Proof spine:

```text
q ∈ factorization.support.filter (fun q => q ∣ p)
  -> q.Prime
  -> q ∣ p
  -> q = p
  -> support membership gives p ∣ GN
  -> factorization_GN_prime_eq_one_of_dvd
  -> exceptional summand = 0
  -> finite sum = 0
```

Optional caller-facing wrapper:

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (hn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

Include only if it is a natural thin application of:

```lean
GNValuationExcessBudgetAffine.of_split
```

Contract consequence:

```text
σ + (τe + τn)
  -> σ + τn
```

because:

```text
τe = 0
De = 0
```

## 8. M1-006: Integration and closure

Status: **continue automatically after M1-005**

M1-006 is integration/audit, not a new deep arithmetic checkpoint.

Tasks:

```text
1. decide aggregator/public import
2. focused regression builds
3. representative endpoint axiom audit
4. theorem naming and statement audit
5. dependency-direction audit
6. fixed-five/general theorem coexistence
7. neutral API ownership audit
8. README status update
9. FINAL_REPORT.md
```

Neutral ownership candidates:

```lean
GN_eq_geom_sum₂
prime_dvd_boundary_of_dvd_GN_prime
```

Decision branches:

```text
A. keep in ABC because campaign-local ownership is adequate
B. move to NumberTheory/CosmicFormula because reuse and dependency clarity justify churn
```

Do not refactor for aesthetics alone.

Build surface:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
lake build DkMath.ABC.GNExceptionalExcessOddPrime
lake build DkMath.ABC.GNFinalBudgetBridge
```

Root `DkMath` build is required only if public aggregator surface changes.

Axiom audit targets:

```lean
#print axioms DkMath.ABC.Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
#print axioms DkMath.ABC.Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

Final report:

```text
FINAL_REPORT.md
```

must include:

```text
exact theorem chain
fixed-five certificate
general odd-prime certificate
budget-contract consequence
imports and dependency graph
build results
axiom audit
remaining M2/M3 state
next-campaign recommendation
```

## 9. Dual-Brain autonomous checkpoint discipline

Codex and Wise Wolf are peer reasoning agents.

```text
not master/subordinate
not planner/transcriber
two independent inference routes
Lean kernel as common judge
```

The operating loop is:

```text
reconnaissance
  -> theorem target
  -> implementation
  -> focused verification
  -> report
  -> self-evaluation
  -> next strongest action
```

A review synchronizes and cross-checks the two brains. It does not grant permission to think or proceed.

After a checkpoint, Codex should autonomously determine:

```text
what became Core
what remains Gap
whether the planned next checkpoint is still optimal
whether a micro-checkpoint should be inserted
whether two planned checkpoints can be safely fused
whether theorem ownership or dependency direction should change
```

Codex may alter the planned route when repository evidence supports the change. The report must explain the decision.

Preserve auditability:

```text
coherent theorem surface
focused build
checkpoint report
no hidden leap over a deep unproved obligation
```

After M1-005, proceed into M1-006 automatically.

After M1 completion, inspect M2/M3 and choose the next strongest action. Preserve branch hygiene: work belonging to a new campaign should be designed for a new branch instead of being mixed into M1.

## 10. Trust and branch boundaries

Absolute trust boundaries:

```text
no new axiom
no sorry
no native_decide proof
no finite enumeration as a general proof
```

Dependency boundaries:

```text
no abc_main_axiom modification
no ABC -> FLT.Five production dependency
no DkMath/FLT/Seven/** import or modification
no parallel WIP branch dependency
no unrelated repository refactor
```

These are mathematical and repository invariants, not permission gates.

## 11. Victory condition

Minimum victory: **complete**

```text
GNExceptionalValuationExcess 5 T.a T.b = 0
GNExceptionalExcessBudgetAffine T 5 0 0
```

Complete victory:

```text
∀ odd prime p,
  GNExceptionalValuationExcess p T.a T.b = 0

∀ odd prime p,
  GNExceptionalExcessBudgetAffine T p 0 0
```

After complete victory, the ABC–GN obstruction list becomes:

```text
M1 exceptional valuation excess       defeated
M2 lifted-radical support growth       remains
M3 non-exceptional valuation excess    remains
```

M1 should then be treated as closed Core. Reopen only if later integration produces a concrete counterexample or dependency defect.
