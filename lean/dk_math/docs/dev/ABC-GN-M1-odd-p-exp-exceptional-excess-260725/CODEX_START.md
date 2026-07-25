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
M1-003  active
```

Current instruction:

```text
instruction-M1-003.md
```

## Read order

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
report-M1-001.md
instruction-M1-002.md
report-M1-002.md
review-M1-002.md
instruction-M1-003.md
```

Repository paths are relative to:

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/
```

## Completed local kernel

M1-002 established:

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
  -> (GN 5 a b).factorization 5 = 1
```

Implementation:

```text
lean/dk_math/DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

Reviewed commit:

```text
3fa7baceb34f7b184168e68fb16b9d76bf4d122b
```

Decision:

```text
M1-002 fully accepted
```

## Active objective

Connect the local factorization-one theorem to the existing exceptional filtered sum and exact zero budget.

Preferred new module:

```text
lean/dk_math/DkMath/ABC/GNExceptionalExcessFive.lean
```

Required endpoints:

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0

theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple) :
    GNExceptionalExcessBudgetAffine T 5 0 0
```

No positivity assumptions should be introduced unless Lean genuinely requires them.

## Stop boundary

M1-003 ends after:

```text
finite exceptional sum = 0
exact affine budget = 0
focused build
report-M1-003.md
commit
```

Do not automatically start:

```text
M1-004 odd-prime generalization
M1-005 odd-prime finite-sum closure
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
```

The detailed implementation contract is `instruction-M1-003.md`.
