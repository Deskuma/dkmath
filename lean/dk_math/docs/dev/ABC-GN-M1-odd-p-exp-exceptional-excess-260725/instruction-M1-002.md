# Codex Instruction M1-002

## Mission

Implement the fixed exponent-five local kernel for M1.

Do not close the full exceptional finite sum in this checkpoint. The target is only the local arithmetic chain:

```text
5 ∣ GN 5 a b
  -> 5 ∣ a
  -> Coprime a b gives 5 ∤ b
  -> 25 ∤ GN 5 a b
  -> padicValNat 5 (GN 5 a b) = 1
```

## Branch

```text
wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0
```

## Read first

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/README.md
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/ABC-GN-M1-IMPLEMENTATION-DESIGN.md
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/ABC-GN-M1-ROADMAP.md
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/report-M1-001.md

lean/dk_math/DkMath/ABC/GNValuationExcess.lean
lean/dk_math/DkMath/ABC/PadicValNat.lean
lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean
```

Read-only comparison only:

```text
lean/dk_math/DkMath/FLT/Five/GN5.lean
```

Do not import `DkMath.FLT.Five.*` into the new ABC module.

## Create

Preferred file:

```text
lean/dk_math/DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

Initial imports should be minimal. Prefer starting from:

```lean
import DkMath.ABC.GNValuationExcess
```

Add another import only when the used theorem requires it.

## Required theorem surface

Exact names may be adjusted for local naming conventions, but preserve this mathematical decomposition.

### 1. Explicit general-GN specialization at exponent five

```lean
theorem GN_five_eq_explicit (a b : ℕ) :
    GN 5 a b =
      a ^ 4 + 5 * a ^ 3 * b + 10 * a ^ 2 * b ^ 2 +
        10 * a * b ^ 3 + 5 * b ^ 4 := by
  ...
```

Use canonical `GN_eq_sum` or unfold the canonical `GN`/`GTail` definition only as far as necessary. Do not duplicate the FLT5 `GN5` definition in production code.

### 2. Divisibility detection

```lean
theorem five_dvd_boundary_of_dvd_GN_five
    {a b : ℕ}
    (h5GN : 5 ∣ GN 5 a b) :
    5 ∣ a := by
  ...
```

Recommended route:

```text
GN 5 a b = a^4 + 5*K
5 ∣ GN -> 5 ∣ a^4
Nat.Prime.dvd_of_dvd_pow prime_five -> 5 ∣ a
```

A small auxiliary decomposition theorem is acceptable:

```lean
GN 5 a b = a ^ 4 + 5 * K
```

### 3. No square lift under coprimality

```lean
theorem not_twentyFive_dvd_GN_five_of_coprime
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    ¬ 25 ∣ GN 5 a b := by
  ...
```

Required arithmetic meaning:

```text
5 | a
5 ∤ b
GN 5 a b ≡ 5*b^4 mod 25
5*b^4 is not divisible by 25
```

Choose the shortest stable Lean route:

```text
explicit quotient witnesses and omega/ring
Nat.ModEq
prime-power divisibility lemmas
padicValNat upper-bound contradiction
```

Do not use brute-force finite enumeration.

### 4. Exact p-adic valuation one

```lean
theorem padicValNat_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b)
    (hGN0 : GN 5 a b ≠ 0) :
    padicValNat 5 (GN 5 a b) = 1 := by
  ...
```

Try to remove `hGN0` if it follows automatically from `h5GN` and the contradiction with zero / no-square-lift. The final theorem should have the weakest natural assumptions.

Suggested proof:

```text
1 ≤ valuation from 5 | GN
valuation < 2 from ¬ 5^2 | GN
omega
```

Use existing:

```lean
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
```

or direct Mathlib equivalents.

### 5. Factorization wrapper

If it is short and useful for M1-003, add:

```lean
theorem factorization_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    (GN 5 a b).factorization 5 = 1 := by
  ...
```

Use:

```lean
Nat.factorization_def _ prime_five
```

Do not implement the filtered-sum theorem yet.

## Scope restrictions

Do not:

```text
prove GNExceptionalValuationExcess 5 ... = 0 yet
change GNExceptionalValuationExcess definition
change GNFinalBudgetBridge
modify abc_main_axiom
import FLT.Five into ABC
start odd-prime generalization
change aggregators unless required for the focused build
add sorry, axiom, native_decide
modify unrelated files
```

## Validation

Run the narrowest build first.

```text
cd lean/dk_math
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
```

If the module is not yet in an aggregator, build it by module name directly.

Then run:

```text
git diff --check
```

## Report

Create:

```text
lean/dk_math/docs/dev/ABC-GN-M1-odd-p-exp-exceptional-excess-260725/report-M1-002.md
```

Report:

```text
exact theorem names
proof route selected
imports added
build result
whether hGN0 was necessary
whether factorization wrapper was included
remaining obstacle for M1-003
```

## Stop condition

After the local valuation-one theorem and focused build pass, stop.

Do not proceed automatically to M1-003. Commit and report the checkpoint for review.