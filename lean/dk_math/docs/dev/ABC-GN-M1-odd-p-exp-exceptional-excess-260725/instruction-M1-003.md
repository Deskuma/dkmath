# Codex Instruction M1-003

## Mission

Close the exponent-five exceptional finite sum and expose the exact zero affine budget.

M1-002 is complete at commit:

```text
3fa7baceb34f7b184168e68fb16b9d76bf4d122b
```

Review:

```text
review-M1-002.md
```

This checkpoint must use the local factorization-one theorem already proved in:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

Do not reprove the modulo-5 or modulo-25 arithmetic.

## Branch

```text
wip/ABC-GN-M1-odd-p-exp-exceptional-excess-260725-v0
```

## Preferred new module

Create:

```text
lean/dk_math/DkMath/ABC/GNExceptionalExcessFive.lean
```

Preferred imports:

```lean
import DkMath.ABC.GNOddPrimeExceptionalExcess
import DkMath.ABC.GNFinalBudgetBridge
```

Reason: preserve `GNOddPrimeExceptionalExcess.lean` as the low-dependency local arithmetic kernel. The new file is the thin finite-sum / final-budget connection layer.

## Required theorem 1

Prefer the strongest theorem without unnecessary positivity assumptions:

```lean
theorem Triple.GNExceptionalValuationExcess_five_eq_zero
    (T : Triple) :
    GNExceptionalValuationExcess 5 T.a T.b = 0
```

Do not add `0 < T.a` or `0 < T.b` unless Lean forces them. Current local theorem requires only `T.hcop` and divisibility of the GN kernel.

## Finite-sum proof route

Unfold only the exceptional finite sum.

```text
GNExceptionalValuationExcess 5 T.a T.b
  = sum over
      (GN 5 T.a T.b).factorization.support.filter (fun q => q ∣ 5)
```

For each `q` in the filtered support:

```text
1. split Finset.mem_filter into:
     hqSupport : q ∈ factorization.support
     hqDvdFive : q ∣ 5

2. derive q.Prime canonically from factorization support:
     convert support membership to primeFactors membership using
     Nat.support_factorization
     then use Nat.prime_of_mem_primeFactors

3. derive q = 5:
     q ∣ 5 and prime q
     exclude q = 1

4. substitute q = 5

5. derive 5 ∣ GN 5 T.a T.b from hqSupport:
     Finsupp.mem_support_iff.mp hqSupport gives nonzero factorization
     Nat.dvd_of_factorization_pos is the preferred bridge if its signature fits

6. use:
     factorization_five_GN_five_eq_one_of_dvd T.hcop h5GN

7. simplify:
     ((1 - 1 : ℕ) : ℝ) * Real.log (5 : ℝ) = 0
```

Preferred outer pattern:

```lean
classical
unfold GNExceptionalValuationExcess
apply Finset.sum_eq_zero
intro q hq
...
```

Use canonical existing lemmas. Do not introduce a custom support structure or enumerate the filtered set manually.

## Required theorem 2

Expose the exact zero budget:

```lean
theorem Triple.GNExceptionalExcessBudgetAffine_five_zero
    (T : Triple) :
    GNExceptionalExcessBudgetAffine T 5 0 0
```

This should be a thin consequence of theorem 1.

Expected shape:

```text
unfold GNExceptionalExcessBudgetAffine
rw [T.GNExceptionalValuationExcess_five_eq_zero]
simp
```

Exact syntax may vary.

## Optional theorem

Only if it materially simplifies theorem 1, a tiny support-collapse lemma is allowed:

```lean
q ∈ (GN 5 a b).factorization.support.filter (fun q => q ∣ 5) → q = 5
```

Do not build a larger singleton-set API unless needed.

## Validation

Run focused builds for the new module.

```text
lake build DkMath.ABC.GNExceptionalExcessFive
```

Audit the two endpoint theorems with `#print axioms` from a temporary audit module or existing audit workflow.

Report:

```text
report-M1-003.md
```

The report must record:

```text
exact theorem statements
whether positivity assumptions were avoided
canonical support -> prime -> q=5 route
support -> 5 ∣ GN route
zero-budget wrapper
focused build result
axiom audit result
```

## Stop boundary

Stop after:

```text
GNExceptionalValuationExcess 5 T.a T.b = 0
GNExceptionalExcessBudgetAffine T 5 0 0
focused build
report-M1-003.md
commit
```

Do not automatically begin:

```text
M1-004 odd-prime generalization
M1-005 general odd-prime sum closure
M2 support-growth work
M3 non-exceptional excess work
aggregator/public import changes
```

The checkpoint review will decide whether to seal the fixed-five minimum victory or continue immediately to M1-004.

## Forbidden scope

```text
no abc_main_axiom modification
no ABC -> FLT.Five import
no FLT7 work
no unrelated refactor
no sorry
no axiom
no native_decide
```
