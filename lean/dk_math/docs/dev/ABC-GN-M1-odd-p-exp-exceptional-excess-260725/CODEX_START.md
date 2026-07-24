# Codex Start Entry — ABC–GN M1 Active

作業 branch:

```text
wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0
```

## Status

```text
M1-000  complete
M1-001  complete / Outcome B
M1-002  active
```

Current instruction:

```text
instruction-M1-002.md
```

## Read order

```text
README.md
ABC-GN-M1-IMPLEMENTATION-DESIGN.md
ABC-GN-M1-ROADMAP.md
report-M1-001.md
instruction-M1-002.md
```

Repository paths are relative to:

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/
```

## Active objective

Implement only the fixed exponent-five local kernel:

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 5 ∤ b
  -> 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
```

Preferred new module:

```text
lean/dk_math/DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

## Stop boundary

M1-002 ends after:

```text
local valuation-one theorem
focused build
report-M1-002.md
commit
```

Do not automatically start:

```text
M1-003 exceptional finite-sum closure
M1-004 odd-prime generalization
M2 or M3 work
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

The detailed implementation contract is `instruction-M1-002.md`.