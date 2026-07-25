# Codex Start Entry — ABC–GN M1 Active

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
M1-004  active
```

Current instruction:

```text
instruction-M1-004.md
```

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
instruction-M1-004.md
```

Repository paths are relative to:

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/
```

## Completed fixed-five victory

M1-002 established the local exponent-five valuation-one theorem:

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
  -> (GN 5 a b).factorization 5 = 1
```

M1-003 connected it to the exceptional finite sum and exact affine budget:

```lean
Triple.GNExceptionalValuationExcess_five_eq_zero
Triple.GNExceptionalExcessBudgetAffine_five_zero
```

Thus, at exponent five:

```text
τe = 0
De = 0
```

Implementation:

```text
lean/dk_math/DkMath/ABC/GNOddPrimeExceptionalExcess.lean
lean/dk_math/DkMath/ABC/GNExceptionalExcessFive.lean
```

Reviewed commits:

```text
3fa7baceb34f7b184168e68fb16b9d76bf4d122b
8a9690b41be321fed2b15dc9d578512388322a0d
```

Decision:

```text
M1-002 fully accepted
M1-003 fully accepted
```

## Active objective

Generalize the local valuation-one theorem from exponent five to every odd prime exponent.

Required endpoints:

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

Primary route:

```text
p ∣ GN -> p ∣ a
Coprime a b -> p ∤ a+b
GN = geometric quotient
emultiplicity_geom_sum₂_eq_one
transfer to padicValNat / factorization
```

Alternative route:

```text
odd-prime LTE on (a+b)^p - b^p
plus the exact boundary * GN product split
```

No positivity assumptions should be introduced unless Lean genuinely requires them.

## Stop boundary

M1-004 ends after:

```text
odd-prime local valuation-one theorem
odd-prime local factorization-one theorem
focused build
report-M1-004.md
commit
```

Do not automatically start:

```text
M1-005 odd-prime exceptional finite-sum closure
M1-006 integration/audit closure
M2 or M3 work
aggregator/public import changes
```

## Forbidden scope

```text
no abc_main_axiom modification
no ABC -> FLT.Five production import
no FLT7 work
no unrelated refactor
no sorry
no axiom
no native_decide
no finite enumeration as general proof
```

The detailed implementation contract is `instruction-M1-004.md`.
