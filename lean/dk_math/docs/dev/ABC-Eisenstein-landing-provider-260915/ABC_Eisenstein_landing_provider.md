# ABC Eisenstein Landing Provider Audit

Current base:

```text
Deskuma/dkmath
develop @ 7ee9d183b8ffc00b881084a4ffcea56d0bae1616
```

This is a research / branch-pruning task. Do not attempt a general proof of ABC.

## Central question

For a realized cubic ABC shell witness `a`, let

```text
alpha := eisensteinCoord ((a : ℤ) + 2) 1
```

so that

```text
Norm(alpha) = a^2 + 3*a + 3
```

and the existing ABC production API decomposes this norm through the canonical repeated-modulus / complement structure.

Determine whether the existing production hypotheses are sufficient to construct, unconditionally and canonically enough for Lean,

```text
beta gamma : TraceOneInt (-1)
```

such that

```text
alpha = beta * gamma^2.
```

Equivalently, determine whether the currently missing ABC factorization-existence provider can be built from the already formalized shell arithmetic.

## Existing receivers — do not re-prove them

The repository already contains generic production infrastructure for:

1. Eisenstein / TraceOne coordinates;
2. exact lattice landing:
   divisibility in `TraceOneInt (-1)` iff the two conjugate-product coordinates satisfy the corresponding norm divisibility conditions;
3. exact square/Core-image landing:
   existence of `gamma` with

```text
alpha = beta * gamma^2
```

iff the conjugate-product coordinates satisfy the square-coordinate equations;
4. norm multiplicativity and power norms;
5. ABC conditional consequences once an explicit equality

```text
beta * gamma^2 = eisensteinCoord ((a : ℤ) + 2) 1
```

is supplied.

The task is therefore not to rebuild the receiver layer. The missing object is the provider.

## Required audit

Start from the current production facts around:

```text
GNExcessCubicFullRepeatedModulus
GNExcessCubicComplement
GNExcessCubicRealizedLargeModulusShellWitnessSpace
GNExcessCubicSquarefulPell / related squareful decomposition
GNExcessCubicEisensteinCoordinates
GNExcessCubicEisensteinFactorConsequences
```

and all generic Lib infrastructure now available under:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
DkMath.Lib.NumberTheory.EisensteinLatticeLanding
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector
```

Do not assume that the repeated modulus itself must equal `Norm(gamma)^2`, or that the complement itself must equal `Norm(beta)`. Explore the possible canonical allocation of the repeated/squareful part and squarefree/complement part.

## Phase 1 — element-level feasibility

For

```text
alpha = (a+2) + ω
```

derive the exact coordinate equations required for

```text
alpha = beta * gamma^2
```

with

```text
beta = c + d*ω
gamma = m + n*ω.
```

Compare these equations with the actual production facts known for the ABC shell witness.

Determine whether the shell data already force the two lattice-landing divisibilities for some explicitly constructible `beta`.

If yes, give an explicit candidate construction for `(c,d)` and the exact theorem chain needed in Lean.

## Phase 2 — ideal-level fallback

If element-level construction is too strong, test whether the production facts at least force an ideal factorization of the form

```text
(alpha) = b * g^2
```

for suitable ideals `b,g`.

Then determine precisely what is still required to descend this ideal factorization to

```text
alpha = unit * beta * gamma^2
```

or directly to

```text
alpha = beta * gamma^2.
```

Do not silently assume UFD, PID, principalization, class-group triviality, or a unit normalization theorem.

If the obstruction is class-group / principalization / unit-sector data, identify it exactly.

## Phase 3 — local prime allocation

For every rational prime occurring in the norm decomposition, classify which channel it may occupy in the Eisenstein factorization:

```text
ramified prime 3
split primes q ≡ 1 mod 3
inert primes q ≡ 2 mod 3
```

Use existing DkMath cubic GN / Eisenstein / p-adic facts where available.

Determine whether the shell hypotheses force even valuation in the would-be `gamma^2` channel and leave a controlled squarefree residual for `beta`.

This phase should explicitly test whether the repeated-modulus/complement decomposition is already the shadow of an Eisenstein square-factor decomposition, or merely a norm-level decomposition with insufficient phase/orientation information.

## Phase 4 — information-gap test

The most important question is:

```text
Does the current ABC shell data determine enough orientation/coordinate
information to lift norm factorization back to an Eisenstein factorization?
```

Norm divisibility alone is known to be insufficient in general.

If the answer is no, identify the smallest missing datum. Examples include:

- a residue/orientation choice at each split prime;
- compatibility of those local choices by CRT;
- an ideal-square condition;
- principalization;
- a unit-sector condition;
- a new MultiGauge transition supplying the missing orientation;
- another explicit arithmetic invariant.

Do not answer merely “more information is needed”. State the exact missing mathematical proposition.

## Required adversarial tests

Actively search for counterexamples to naive lifts such as:

```text
Norm(beta) | Norm(alpha)
    =>
beta | alpha
```

or

```text
squareful norm part
    =>
element square factor.
```

Use small numerical Eisenstein examples if useful.

Also test whether two shell witnesses can have identical norm/repeated/complement data but different Eisenstein landing behavior. If such a pair exists, it proves that norm-shell data alone cannot be the provider.

## Required outcome classification

Return exactly one principal verdict.

### Outcome A — FACTORIZATION PROVIDER FOUND

The current shell hypotheses suffice.

Provide:

- explicit `beta` / `gamma` construction or an exact constructive theorem chain;
- minimal new Lean lemmas;
- proposed production module;
- dependencies;
- scratch Lean verification where practical.

### Outcome P — PRECISE BRIDGE MISSING

The route is viable, but one explicit new theorem is missing.

State that theorem as sharply as possible, preferably in Lean-shaped form.

Examples:

```text
shell witness
  -> local split-prime orientation compatibility
```

or

```text
canonical repeated ideal is an ideal square
```

or

```text
ideal square factor is principal
```

This outcome is valuable only if the missing bridge is materially narrower than the original factorization-existence problem.

### Outcome B — NORM/LATTICE DATA INSUFFICIENT

The current shell arithmetic cannot supply the desired factorization.

Give a concrete obstruction, countermodel, or information-loss explanation proving that the present route is only normalization/transport.

Do not add decorative production APIs.

## Deliverables

Produce:

```text
report-000.md
```

with:

- theorem inventory;
- exact dependency graph;
- algebraic derivation;
- numerical diagnostics/counterexamples if useful;
- candidate Lean theorem shapes;
- Outcome A / P / B verdict.

Scratch Lean and Python diagnostics are encouraged.

Do not modify production Lean unless a genuinely new theorem has been established and independently kernel-checked.

## Scope firewall

Do not claim:

```text
ABC conjecture proved;
Helfgott–Venkatesh formalized;
Mordell integral-point bound established;
near-linear shell count established.
```

The sole research question is:

```text
Can the existing ABC shell norm structure be lifted to an actual
Eisenstein square-factor / lattice-landing provider?
```
