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
0 < T.a
0 < T.b
```

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
M1-000  campaign initialization
M1-001  read-only theorem/API reconnaissance
M1-002  exponent-five divisibility and no-lift kernel
M1-003  exponent-five exceptional excess = 0
M1-004  odd-prime general local valuation-one theorem
M1-005  odd-prime exceptional excess = 0 and budget bridge
M1-006  integration, audit, documentation closure
```

各 checkpoint は独立 commit と report を持たせる。大きな一般化を一つの commit に詰め込まない。

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

No Lean source change at this checkpoint.

## 3. M1-001: Read-only reconnaissance

### Objective

実装前に、Mathlib と DkMath の既存 API で次を確認する。

```text
A. GN p a b の general binomial representation
B. prime exponent modulo-p congruence
C. odd-prime LTE theorem availability and exact signature
D. padicValNat and Nat.factorization equality bridge
E. factorization supportから prime/dvd を得る canonical lemmas
F. p = 5 specializationを一般 GN で簡約する最短 route
```

### Required inspection targets

```text
DkMath/ABC/GNExceptionalSplit.lean
DkMath/ABC/GNValuationExcess.lean
DkMath/ABC/GNFinalBudgetBridge.lean
DkMath/ABC/PadicValNat.lean
DkMath/FLT/Five/GN5.lean                 read-only comparison
DkMath/NumberTheory/Gcd/GN.lean
CosmicFormulaBinom GN / GTail owner files
Mathlib LTE / padicValNat / factorization APIs
```

### Outcome branches

#### Outcome A: direct general route exists

既存 LTE または binomial API で odd-prime theorem を直接構成できる。

```text
M1-002 may be folded into a smoke theorem
proceed rapidly to M1-004
```

#### Outcome B: fixed five is easy, general route requires new local lemma

```text
complete M1-002 and M1-003 first
then design one reusable general GN lemma for M1-004
```

#### Outcome C: foundational bridge missing

例:

```text
padicValNat = factorization multiplicity bridge is absent
GN prime-exponent congruence owner is unclear
```

この場合は小さな foundational checkpoint を挿入する。ABC final bridge や unrelated modules を変更しない。

### Report

```text
report-M1-001.md
```

Report must record:

```text
selected proof route
exact existing theorem names
new theorem surface
import boundary
rejected alternatives and reason
```

## 4. M1-002: Exponent-five local kernel

### Objective

一般 `GN` の指数 `5` について、exceptional prime `5` の divisibility と no-lift を証明する。

### Target theorem candidates

```lean
theorem five_dvd_boundary_of_dvd_GN_five
    {a b : ℕ}
    (h5GN : 5 ∣ GN 5 a b) :
    5 ∣ a

theorem not_twentyFive_dvd_GN_five_of_coprime
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    ¬ 25 ∣ GN 5 a b

theorem padicValNat_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    padicValNat 5 (GN 5 a b) = 1
```

Exact names may change after reconnaissance.

### Proof obligations

```text
GN 5 a b mod 5 = a^4
5 | GN -> 5 | a
Coprime a b -> 5 ∤ b
GN 5 a b mod 25 = 5*b^4 when 5 | a
5 ∤ b -> 25 ∤ GN
```

### Placement

Prefer:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

If arithmetic theorem is clearly reusable outside ABC:

```text
DkMath/NumberTheory/GN/OddPrimeExceptional.lean
```

### Stop gate

Do not proceed to general prime until focused build passes.

```text
lake build <new module>
```

## 5. M1-003: Exponent-five exceptional excess zero

### Objective

Local valuation-one theoremを、既存の filtered finite sumへ接続する。

### Target

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalValuationExcess 5 T.a T.b = 0
```

Positivity assumptions are retained only if required by existing GN nonzero or valuation APIs.

### Sum proof plan

```text
unfold GNExceptionalValuationExcess
for q in filtered support:
  q prime
  q | 5
  therefore q = 5
  factorization multiplicity at 5 = 1
  q-summand = 0
sum = 0
```

### Budget target

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalExcessBudgetAffine T 5 0 0
```

### Milestone decision

M1-003 completion is already a mathematical victory for the `n = 5` ABC–GN final contract route.

At this point:

```text
M1 minimum victory achieved
τe = 0
De = 0
```

A checkpoint review must decide whether to continue immediately to general odd prime or seal the fixed-five theorem first.

## 6. M1-004: Odd-prime local valuation-one theorem

### Objective

M1-002 の局所算術を任意の奇素数へ一般化する。

### Preferred theorem

```lean
theorem padicValNat_GN_prime_exp_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpodd : 2 < p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1
```

Equivalent no-lift form is acceptable as the primitive theorem:

```lean
¬ p ^ 2 ∣ GN p a b
```

provided valuation exactness is then derived cleanly.

### Proof route priority

```text
1. existing odd-prime LTE API
2. existing general binomial congruence API
3. new minimal modulo-p² GN theorem
```

Avoid a large polynomial or cyclotomic abstraction unless the proof genuinely requires it.

### Validation examples

Add small theorem examples or `example` blocks only when useful for type checking.

```text
p = 3
p = 5
p = 7
```

Do not use finite enumeration as proof of the general theorem.

## 7. M1-005: Odd-prime excess zero and budget bridge

### Objective

一般 local theorem を既存 finite support sum と final budget API へ接続する。

### Main targets

```lean
theorem Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalValuationExcess p T.a T.b = 0

theorem Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : 2 < p)
    (ha : 0 < T.a) (hb : 0 < T.b) :
    GNExceptionalExcessBudgetAffine T p 0 0
```

### Optional caller-facing wrapper

```lean
theorem Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
    (hexn : GNNonExceptionalExcessBudgetAffine T p τn Dn) :
    GNValuationExcessBudgetAffine T p τn Dn
```

This wrapper must be a thin use of:

```lean
GNValuationExcessBudgetAffine.of_split
```

No duplication of final bridge proof.

### Contract impact

For odd-prime exponent `p`, the remaining margin simplifies from

$$\sigma+(\tau_e+\tau_n)$$

to

$$\sigma+\tau_n$$

because

$$\tau_e=0$$

and

$$D_e=0$$

This simplification should be documented, but the global ABC contract structure need not be changed in this branch.

## 8. M1-006: Integration and closure

### Objective

M1 theorem を public route へ安全に接続し、討伐記録を閉じる。

### Tasks

```text
1. decide aggregator import
2. focused module build
3. GNFinalBudgetBridge regression build
4. axiom audit
5. theorem statement audit
6. dependency-direction audit
7. final report
8. README status update
```

### Build gates

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
lake build DkMath.ABC.GNFinalBudgetBridge
```

Root `DkMath` build is optional unless import surface is changed.

### Axiom audit

```lean
#print axioms DkMath.ABC.Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
#print axioms DkMath.ABC.Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
```

No new:

```text
axiom
sorry
native_decide
```

### Final document

```text
FINAL_REPORT.md
```

Final report must include:

```text
exact theorem chain
fixed-five result
odd-prime result or stop boundary
budget-contract consequence
imports and dependency graph
build results
axiom audit
remaining M2/M3 state
```

## 9. Checkpoint discipline

Each implementation checkpoint follows:

```text
read-only reconnaissance
  -> one local theorem target
  -> focused build
  -> report
  -> review
  -> next instruction
```

Codex must not skip directly from M1-001 to final theorem without exposing the local valuation-one kernel.

## 10. Branch boundaries

```text
feature/ABC-GN-valuation-excess-260724-v0
  └─ wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0
```

Do not import or modify:

```text
DkMath/FLT/Seven/**
parallel WIP branches
unmerged experimental work
```

Read-only comparison with FLT5 is allowed, but production dependency from ABC to FLT5 is forbidden.

## 11. Victory condition

### Minimum victory

```text
GNExceptionalValuationExcess 5 T.a T.b = 0
GNExceptionalExcessBudgetAffine T 5 0 0
```

### Complete victory

```text
∀ odd prime p,
  GNExceptionalValuationExcess p T.a T.b = 0

∀ odd prime p,
  GNExceptionalExcessBudgetAffine T p 0 0
```

When complete, the ABC–GN final obstruction list becomes:

```text
M1 exceptional valuation excess       defeated
M2 lifted-radical support growth       remains
M3 non-exceptional valuation excess    remains
```

討伐後は、M1 の証明を再び開かず、M2/M3 の support–depth tradeoff 戦線へ進む。