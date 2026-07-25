# Codex Start Entry — ABC–GN M1 Dual-Brain Campaign

作業 branch:

```text
wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0
```

## Status

```text
M1-000  complete
M1-001  complete / Outcome B
M1-002  complete
M1-003  complete / fixed-five minimum victory
M1-004  complete / odd-prime local valuation-one
M1-005  active / odd-prime exceptional sum and zero budget
M1-006  autonomous continuation after M1-005
```

Current instruction:

```text
instruction-M1-005.md
```

## Dual-Brain operating doctrine

Codex and Wise Wolf are peer reasoning agents over the same Lean-verified research program.

```text
not master and subordinate
not planner and transcription engine
two reasoning brains with different search paths
```

A checkpoint is an auditable observation point, not a permission gate.

After a checkpoint is completed, Codex should:

```text
evaluate the mathematical result
inspect the changed theorem and dependency surface
identify the remaining Gap
choose the strongest next action
continue implementation and verification
record a checkpoint report
```

Do not wait for a new instruction merely because the planned endpoint has been reached. Preserve coherent reports and reviewable theorem layers so the second brain can audit the route afterward.

Repository publication operations remain user-controlled unless separately requested.

## Read order

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
report-M1-001.md
report-M1-002.md
review-M1-002.md
report-M1-003.md
review-M1-003.md
report-M1-004.md
review-M1-004.md
instruction-M1-005.md
```

Repository paths are relative to:

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/
```

## Completed fixed-five victory

M1-002 established:

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
  -> (GN 5 a b).factorization 5 = 1
```

M1-003 connected the local kernel to the exceptional finite sum and exact affine budget:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

Thus at exponent five:

```text
τe = 0
De = 0
```

## Completed odd-prime local kernel

M1-004 established the general geometric quotient bridge:

```lean
theorem GN_eq_geom_sum₂ (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
```

and the prime-row boundary extraction:

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

The main local endpoints are:

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
  -> Nat emultiplicity
  -> padicValNat = 1
  -> factorization = 1
```

Reviewed commit:

```text
97c1558f883cc1f9ef56b81bd64940b64a09ba6b
```

Decision:

```text
M1-004 fully accepted
```

## Active objective

Close the general odd-prime exceptional filtered sum and exact zero budget.

Expected module:

```text
lean/dk_math/DkMath/ABC/GNExceptionalExcessOddPrime.lean
```

Expected endpoints:

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

No positivity assumptions are expected.

Proof spine:

```text
q in exceptional factorization support
  -> q.Prime
  -> q ∣ p
  -> q = p
  -> support gives p ∣ GN
  -> M1-004 gives factorization p = 1
  -> summand = 0
  -> exceptional sum = 0
  -> exact affine budget (0,0)
```

## Autonomous continuation

After M1-005, continue directly into M1-006 integration and closure.

M1-006 should self-evaluate:

```text
aggregator/public import
focused regression builds
axiom audit
theorem naming and statement audit
dependency direction
fixed-five/general theorem coexistence
neutral ownership of GN_eq_geom_sum₂ and prime boundary theorem
README / FINAL_REPORT closure
```

Do not refactor neutral API merely because another owner looks aesthetically cleaner. Move only when reuse and dependency ownership materially improve.

After M1 is completely closed, inspect M2/M3 and prepare the strongest next campaign route while preserving branch hygiene.

## Hard boundaries

```text
no abc_main_axiom modification
no ABC -> FLT.Five production import
no FLT7 WIP work
no unrelated refactor
no sorry
no axiom
no native_decide
no finite enumeration as general proof
```

These are mathematical trust and repository dependency boundaries, not permission gates.
