# Codex Instruction — GNPC-001 GN Prime Product Closure / Boundary-One Characterization

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Base: `develop` @ `12c1476f156de4eba9009ac264385820d6d52354`

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
```

## Current state

This project begins as a documentation-first checkpoint.

No Lean implementation has yet been added on this branch.

The current repository already has the algebraic and arithmetic source layers needed for this task.

Important existing anchors include:

```text
DkMath/CosmicFormula/CosmicFormulaBinom.lean
DkMath/NumberTheory/Gcd/GN.lean
DkMath/NumberTheory/UniqueFactorizationGN.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Relevant declarations observed before branch creation include:

```text
DkMath.CosmicFormulaBinom.GN
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le
DkMath.NumberTheory.Gcd.coprime_boundary_GN_of_coprime_add_of_coprime_exp
prime_iff_large_prime_cofactor_eq_one
```

The implementation must re-check current source and Mathlib before choosing exact proof terms or declaration names.

Do not assume the GitHub code-search index is perfectly synchronized with the branch.

---

# Goal

Formalize the elementary prime-product closure attached to the canonical GN factorization

$$
(x+u)^d-u^d=x\,GN_d(x,u).
$$

The central structural statement is not a new primality criterion for GN.

It is the factor-one dichotomy:

$$
\operatorname{Prime}(xG)
\iff
(x=1\land\operatorname{Prime}(G))
\lor
(G=1\land\operatorname{Prime}(x)),
$$

specialized to

$$
G=GN_d(x,u).
$$

Then derive the GN-prime specialization

$$
GN_d(x,u)\text{ prime}
\Longrightarrow
\left(
  x\,GN_d(x,u)\text{ prime}
  \iff x=1
\right).
$$

The checkpoint should be thin.

Do not solve a harder GN problem merely because more arithmetic infrastructure exists.

---

# Mandatory reconnaissance

Before editing Lean source, perform all of the following.

## 1. Search DkMath for exact duplicates

Search at least for concepts equivalent to:

```text
Prime (a * b)
prime_mul
mul_prime
cofactor_eq_one
prime_iff_*_eq_one
x * GN
boundary * GN
GN prime
```

If an exact generic DkMath theorem already exists, do not duplicate it.
Use it to build only the GN-facing wrapper that is missing.

Record the search result in `report-001.md`.

## 2. Identify the canonical Mathlib prime-product API

Do not guess theorem names.

Find the current Mathlib theorem(s) for prime multiplication / prime factorization over `ℕ`.

Preferred strategy:

```text
Nat.Prime (a*b)
  ↓ canonical Mathlib theorem
factor-one alternatives
  ↓ simpa / constructor cleanup
GN wrapper
```

Avoid proving primality facts manually from the divisor definition unless the current Mathlib API genuinely lacks the needed result.

In the report, record the exact Mathlib declaration reused.

## 3. Confirm canonical GN identity ownership

Find the current theorem proving, for natural numbers,

```text
(x + u)^d - u^d = x * GN d x u
```

or an equivalent orientation.

Do not re-expand the binomial theorem.

The Body wrapper in this checkpoint is permitted only if the existing theorem rewrites cleanly.

## 4. Check public ownership

Inspect the current `DkMath/NumberTheory` structure.

Preferred new module is:

```text
DkMath/NumberTheory/GNPrimeClosure.lean
```

but if a clearly better existing owner exists, use it and explain why.

Do not place this theorem in an application module such as ABC, FLT, Legendre, or Collatz.

---

# Required implementation surface

Names below are preferred, not mandatory.
Report final declaration names exactly.

## 1. Symmetric GN factor-one theorem

This is the primary theorem of GNPC-001.

Preferred shape:

```lean
theorem prime_boundary_mul_GN_iff
    {d x u : ℕ} :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      (x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) ∨
      (DkMath.CosmicFormulaBinom.GN d x u = 1 ∧ Nat.Prime x) := by
  ...
```

Equivalent conjunction / disjunction order is acceptable if it follows the canonical Mathlib normal form more naturally.

If the theorem is stated in Mathlib in the order

```text
Prime x ∧ GN = 1
or
x = 1 ∧ Prime GN
```

it is acceptable to keep that orientation if it avoids pointless theorem gymnastics.

The docstring must explain both channels:

```text
boundary channel x
GN kernel channel GN d x u
```

and state that primality of the product forces exactly one channel to be the multiplicative unit.

### Important edge case

Do not assume `2 ≤ d` here.

For `d = 1`, the GN kernel can be `1`, and the second branch is mathematically real.

The symmetric theorem should preserve this case rather than hide it behind positivity assumptions.

---

## 2. GN-prime specialization

Derive the theorem corresponding directly to the numerical experiment.

Preferred shape:

```lean
theorem prime_boundary_mul_GN_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔ x = 1 := by
  ...
```

Intended proof:

```text
symmetric factor-one theorem
  ↓
GN prime implies GN ≠ 1
  ↓
second branch disappears
```

Do not introduce assumptions `0 < x`, `0 < u`, or `2 ≤ d` unless Lean truly requires them.
They are not mathematically necessary once `hGN` is assumed.

The reverse direction should reduce to

```text
x = 1
→ 1 * GN = GN
→ hGN
```

without extra arithmetic machinery.

---

## 3. Optional direct implication aliases

If useful for downstream rewriting, thin one-way aliases are acceptable:

```lean
theorem boundary_eq_one_of_prime_mul_GN_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u))
    (hBody : Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u)) :
    x = 1
```

and/or

```lean
theorem prime_mul_GN_of_boundary_eq_one_of_GN_prime
    ...
```

Do not add aliases merely to increase theorem count.
Add them only if they make common downstream use materially simpler.

---

## 4. Cosmic Formula Body wrapper

If reconnaissance finds a clean existing identity rewriting

```text
(x + u)^d - u^d
```

to

```text
x * GN d x u
```

then add the wrapper.

Preferred shape:

```lean
theorem prime_shifted_pow_sub_gap_iff_boundary_eq_one_of_GN_prime
    {d x u : ℕ}
    (hGN : Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u)) :
    Nat.Prime ((x + u) ^ d - u ^ d) ↔ x = 1 := by
  ...
```

This theorem is useful because it returns from the factorized GN coordinate to the original Cosmic Formula Body.

### Restriction

Do not duplicate the binomial proof.

If current Nat subtraction normal forms make this wrapper disproportionately awkward, stop after items 1 and 2 and report it as deferred.

GNPC-001 is successful without this wrapper.

---

# Optional strengthening — only if trivial after required work

The mathematical observation is that for

```text
2 ≤ d
0 < x
0 < u
```

we in fact have

```text
1 < GN d x u
```

so the `GN = 1` branch cannot occur even without assuming `GN` is prime.

A useful stronger theorem would be:

```lean
theorem prime_boundary_mul_GN_iff_of_two_le
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    Nat.Prime (x * DkMath.CosmicFormulaBinom.GN d x u) ↔
      x = 1 ∧ Nat.Prime (DkMath.CosmicFormulaBinom.GN d x u) := by
  ...
```

Current source already has at least:

```text
GN_ne_zero_nat_of_two_le
one_le_GN_nat_of_two_le
```

but `1 ≤ GN` alone does not eliminate `GN = 1`.

Only implement this strengthening if a short proof of

```text
2 ≤ GN d x u
```

or

```text
GN d x u ≠ 1
```

is available from existing terms with little new infrastructure.

Do not expand the checkpoint into a new theory of lower bounds for GN.

---

# Explicitly forbidden scope expansion

Do not implement any of the following in GNPC-001:

```text
GN prime → exponent prime
composite exponent decomposition
cyclotomic factorization of GN
nested GN composition identity
Zsigmondy strengthening
primitive-prime existence
Legendre application
ABC application
FLT application
PHZ / primorial application
repository-wide GN rename or refactor
```

In particular, do not implement yet:

$$
GN_{ab}(x,u)
=
GN_a(x,u)\,
GN_b(x\,GN_a(x,u),u^a).
$$

That identity is a future candidate and requires a separate review boundary.

---

# Dependency discipline

Prefer the smallest import set that supports the theorem.

The new module should ideally depend on the canonical GN source plus Mathlib prime arithmetic only.

Do not import these merely because they are related:

```text
DkMath.NumberTheory.Gcd.GN
DkMath.NumberTheory.UniqueFactorizationGN
DkMath.NumberTheory.PrimitiveBeam
DkMath.ABC.*
DkMath.FLT.*
DkMath.NumberTheory.Legendre.*
```

unless a required existing theorem genuinely lives there and reusing it is cleaner than a lightweight Mathlib proof.

The point of this checkpoint is to expose an elementary closure layer, not to inherit the full DkMath number-theory dependency graph.

---

# Public import policy

Do not automatically edit a top-level aggregator before confirming repository convention.

If a suitable public NumberTheory aggregator exists and this module belongs there, add one thin import.

If no such aggregator exists, it is acceptable for GNPC-001 to finish with only the standalone module.

Report the decision.

---

# Proof-quality requirements

## Use existing theory

Prefer:

```text
canonical Mathlib prime multiplication theorem
existing GN definition
existing Cosmic Formula factorization theorem
```

over custom divisor arguments.

## Preserve degenerate cases honestly

Do not hide `d = 1` merely because the original numerical experiment focused on higher GN.

## No accidental stronger claim

The theorem does **not** say:

```text
GN d x u is always prime
```

nor:

```text
x * GN d x u is prime iff x = 1
```

without either an `hGN` assumption or a condition excluding `GN = 1`.

Docstrings must make this distinction explicit.

## No new axioms

Do not introduce:

```text
sorry
axiom
opaque research provider
```

for this elementary theorem.

---

# Tests / examples

Add a few very small `example` declarations only if they materially document the edge cases.

Useful cases include:

```text
d = 1:
  GN = 1
  product primality can come from x

d = 2, x = 1, u = 1:
  GN = 3
  x*GN = 3

d = 2, x = 3, u = 1:
  GN = 5
  x*GN = 15, not prime
```

Do not add a large `native_decide` table or numerical-search harness in the Lean source.
The numerical experiment already motivated the theorem; the Lean theorem should be structural.

---

# Validation

At minimum run:

```text
lake build DkMath.NumberTheory.GNPrimeClosure
```

or the final chosen module name.

If a public aggregator is modified, build that aggregator too.

Also check the new module for:

```text
sorry
axiom
```

and confirm that no project-specific assumption was introduced.

Do not spend this checkpoint on repository-wide full build unless required by the actual changed public surface.

---

# Required report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-001.md
```

The report must include:

## Outcome

Use one of:

```text
Outcome A — required theorem surface completed
Outcome B — exact theorem already existed; GN facade only / no implementation needed
Outcome C — blocked by an actual API or ownership issue
```

Do not report an engineering inconvenience as a mathematical obstruction.

## Repository reconnaissance

Record:

- exact Mathlib prime-product theorem used;
- exact DkMath GN identity used;
- whether an equivalent DkMath theorem already existed;
- final module ownership decision.

## Changed files

List all files.

## Final theorem surface

Give exact Lean declaration names and types.

## Validation

Record exact build commands and results.

## Deferred items

Especially state whether these were deferred:

```text
Body wrapper
GN > 1 strengthening
GN prime → exponent prime
nested GN composition identity
```

---

# Stop condition

Stop GNPC-001 when the symmetric factor-one theorem and the GN-prime specialization are both implemented and validated.

Do **not** continue automatically into composite-exponent factorization.

Return the report for review before starting GNPC-002.
