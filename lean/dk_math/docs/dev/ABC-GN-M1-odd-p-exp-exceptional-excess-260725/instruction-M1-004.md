# Codex Instruction M1-004: odd-prime local exceptional valuation-one theorem

## 0. Objective

Generalize the completed exponent-five local kernel to an arbitrary odd prime exponent.

Implement only the local theorem:

```lean
theorem padicValNat_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    padicValNat p (GN p a b) = 1
```

An equivalent theorem using `2 < p` instead of `Odd p` is acceptable if it fits the available API better.

Also expose the direct factorization wrapper:

```lean
theorem factorization_GN_prime_eq_one_of_dvd
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (hcop : Nat.Coprime a b)
    (hpGN : p ∣ GN p a b) :
    (GN p a b).factorization p = 1
```

Do not close the exceptional filtered sum in this checkpoint. That belongs to M1-005.

## 1. Current completed base

M1-002 established the exponent-five local theorem in:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

M1-003 established the fixed-five finite-sum and exact-zero budget in:

```text
DkMath/ABC/GNExceptionalExcessFive.lean
```

Reviewed commits:

```text
3fa7baceb34f7b184168e68fb16b9d76bf4d122b
8a9690b41be321fed2b15dc9d578512388322a0d
```

M1-003 is fully accepted. The fixed-five minimum victory is complete:

```text
GNExceptionalValuationExcess 5 T.a T.b = 0
GNExceptionalExcessBudgetAffine T 5 0 0
```

## 2. Required mathematical chain

For an odd prime `p`, coprime `a,b`, and `p ∣ GN p a b`, establish:

```text
p ∣ GN p a b
  -> p ∣ a
  -> p ∤ b
  -> p ∤ a + b
  -> the p-multiplicity of the geometric quotient is exactly one
  -> padicValNat p (GN p a b) = 1
```

The first implication should be exposed as a reusable local theorem if practical:

```lean
theorem prime_dvd_boundary_of_dvd_GN_prime
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpGN : p ∣ GN p a b) :
    p ∣ a
```

No positivity assumptions on `a` or `b` should be introduced unless Lean genuinely requires them. The case `a = 0` is mathematically valid and should not be discarded without reason.

## 3. Primary proof route

Use the exact Mathlib theorem:

```lean
emultiplicity_geom_sum₂_eq_one
```

from:

```text
Mathlib/NumberTheory/Multiplicity.lean
```

Its conceptual specialization is:

```text
R = ℤ
x = a + b
y = b
x - y = a
```

The theorem requires:

```text
Prime (p : ℤ)
Odd p
(p : ℤ) ∣ x - y
¬ (p : ℤ) ∣ x
```

The intended input construction is:

```text
p ∣ a
Coprime a b -> p ∤ b
p ∣ a and p ∤ b -> p ∤ a+b
```

Then the geometric quotient

```lean
∑ i ∈ Finset.range p,
  (a + b) ^ i * b ^ (p - 1 - i)
```

has exact `p`-multiplicity one.

## 4. GN / geometric-sum bridge

A bridge is required between canonical `GN` and the geometric quotient.

Preferred statement:

```lean
theorem GN_eq_geom_sum₂
    (p a b : ℕ) :
    GN p a b =
      ∑ i ∈ Finset.range p,
        (a + b) ^ i * b ^ (p - 1 - i)
```

Equivalent orientation or an integer-cast form is acceptable.

Do not prove this identity by expanding a fixed exponent. It must be general in `p`.

Recommended routes, in order:

```text
A. existing `geom_sum₂_mul` plus the canonical GN power-gap identity
B. cast the product identities to ℤ and cancel the boundary factor
C. prove a short recurrence shared by GN and the geometric sum
D. direct finite-sum reindexing only if the previous routes are genuinely worse
```

If cancellation requires `a ≠ 0`, split the `a = 0` case explicitly rather than adding positivity to the public theorem.

Ownership rule:

```text
Keep the bridge in GNOddPrimeExceptionalExcess.lean for this checkpoint
unless it is clearly import-neutral and immediately reusable.
```

Do not create a large new abstraction tower merely to relocate one identity.

## 5. Boundary divisibility `p ∣ GN -> p ∣ a`

Prove the general prime-exponent congruence needed to derive the boundary divisibility.

Acceptable forms include:

```lean
GN p a b % p = a ^ (p - 1) % p
```

or directly:

```lean
p ∣ GN p a b -> p ∣ a
```

Possible routes:

```text
A. prime divisibility of intermediate binomial coefficients in GN_eq_sum
B. prime-power freshman-dream congruence applied to
   a * GN p a b + b^p = (a+b)^p
C. an existing Mathlib theorem giving the same congruence
```

Prefer the shortest kernel-stable route. Do not use finite enumeration.

## 6. Multiplicity transfer

After obtaining exact geometric-sum multiplicity one, transfer it to:

```text
padicValNat p (GN p a b) = 1
```

and then to:

```text
(GN p a b).factorization p = 1
```

Useful existing bridge:

```lean
Nat.factorization_def
```

Inspect the exact current signatures before committing. Avoid introducing a new general multiplicity framework if the existing `emultiplicity` / `padicValNat` bridge is sufficient.

## 7. Alternative route if the primary bridge becomes costly

A local LTE route is acceptable:

```text
(a+b)^p - b^p = a * GN p a b
```

combine:

```lean
Nat.emultiplicity_pow_sub_pow
```

with the exact multiplicity of `p` in the exponent `p`, and compare the product multiplicity with the boundary-plus-GN split.

Use this route only if it gives a smaller proof surface than `GN_eq_geom_sum₂` plus `emultiplicity_geom_sum₂_eq_one`.

The endpoint must remain the same.

## 8. Outcome branches

### Outcome A: direct general theorem closes

Deliver:

```text
prime boundary divisibility
GN/geometric-sum bridge or equivalent
padicValNat exact one
factorization exact one
```

Then stop and report success.

### Outcome B: multiplicity theorem applies, but one transfer bridge is missing

Implement the strongest completed neutral bridge and report the exact remaining type mismatch.

Do not replace it with an axiom or a stronger assumption.

### Outcome C: `GN = geom_sum₂` is unexpectedly costly

Try the LTE/product-split route before proposing a foundational refactor.

Record the obstruction precisely, including exact goal and theorem signatures.

## 9. Preferred file scope

First preference:

```text
modify:
  DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

A small neutral helper module is allowed only if dependency ownership clearly improves:

```text
DkMath/NumberTheory/GN/OddPrimeExceptional.lean
```

If a neutral helper is created, the ABC module should contain only thin wrappers.

Do not modify:

```text
DkMath/ABC/GNExceptionalExcessFive.lean
DkMath/ABC/GNFinalBudgetBridge.lean
abc_main_axiom or legacy ABC prototype axioms
FLT5 or FLT7 modules
aggregators
```

## 10. Validation

Run a focused build for every changed/new module.

Minimum required build:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
```

If a neutral helper module is added, build it separately first.

Audit the final local endpoints with `#print axioms` from a temporary audit file.

Forbidden:

```text
sorry
new axiom
native_decide
finite enumeration as proof
```

## 11. Report

Create:

```text
report-M1-004.md
```

The report must state:

```text
selected proof route
exact Mathlib theorem signatures used
GN/geometric-sum or LTE bridge obtained
how p ∣ GN implies p ∣ a
how coprimality gives p ∤ a+b
how emultiplicity is transferred to padicValNat
public theorem surface
focused build result
axiom audit result
```

## 12. Stop boundary

M1-004 ends after the general local factorization-one theorem, focused build, report, and commit.

Do not automatically start:

```text
M1-005 odd-prime exceptional finite-sum closure
M1-006 integration/audit closure
M2 support-growth work
M3 non-exceptional valuation work
aggregator changes
```
