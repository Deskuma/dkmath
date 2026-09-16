# instruction-008 — MG-004C TraceOne power/Core-image landing

## Role

Act as Lean formalization engineer and research auditor.

MG-004A/B already establish the lattice-landing receiver.  This checkpoint
must add the **next strictly stronger filter**: after an integral quotient
exists, determine whether that quotient lies in a power/Core image.

Do not add a root-existence provider.  This is a receiver/criterion layer.

## Read first

Read the exact current sources and theorem signatures before coding:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-007.md
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-007.md
DkMath/NumberTheory/TraceOneQuadratic.lean
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
```

Also audit existing FLT5/FLT7/ABC power packets only to avoid duplication.
Application-owned power/descent theorems must not be moved into Lib.

## Frozen conventions

For `TraceOneInt s`, multiplication is the existing production multiplication.
For

```text
gamma = <m,n>
```

the square coordinate identity should be

```text
gamma^2 = <m^2 + s*n^2, 2*m*n + n^2>.
```

For

```text
alpha = <a,b>
beta  = <c,d>
```

MG-004B already gives

```text
(alpha * conj beta).fst = a*c + a*d - s*b*d
(alpha * conj beta).snd = b*c - a*d.
```

Do not change these conventions.

## Main production target

Preferred new neutral module:

```text
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
```

Import the existing generic landing module.  Keep this module independent of
MultiGauge, ABC, FLT, Petal, Legendre, and PrimorialUniverse.

### 1. Square-coordinate formula

Prove a stable theorem such as:

```lean
theorem traceOne_sq_coordinates (s m n : ℤ) :
  (⟨m,n⟩ : TraceOneInt s) ^ 2 =
    ⟨m^2 + s*n^2, 2*m*n + n^2⟩
```

Use existing ring operations.  Do not define a second multiplication API.

### 2. Generic power receiver, if clean

Audit/prove the neutral equivalence for arbitrary `r : ℕ`:

```text
norm beta != 0 ->
(
  exists gamma, alpha = beta * gamma^r
  <->
  exists gamma,
    alpha * conj beta = ofInt s (norm beta) * gamma^r
)
```

This is useful only if the reverse direction genuinely uses MG-004B-style
nonzero-norm cancellation and the theorem stays compact.

It must not be presented as a power-existence theorem.  It is only an exact
receiver/rewrite of an already quantified power witness.

If the arbitrary-power theorem causes unnecessary complexity, record that and
keep the square theorem as the primary production result.

### 3. Main square/Core landing iff

Under

```text
hNorm : norm beta != 0
```

prove an exact theorem equivalent to:

```text
exists gamma : TraceOneInt s,
  alpha = beta * gamma^2

<->

exists m n : ℤ,
  (alpha * conj beta).fst =
    norm beta * (m^2 + s*n^2)
  and
  (alpha * conj beta).snd =
    norm beta * (2*m*n + n^2).
```

This is the primary MG-004C theorem.

The reverse direction must reconstruct

```text
gamma = <m,n>
```

and use the already-proved nonzero-norm cancellation or the generic power
receiver.  Do not appeal to a field quotient.

### 4. Structured quotient formulation

If useful and non-duplicative, expose a theorem separating the layers:

```text
exists gamma, alpha = beta * gamma^2
<->
exists q,
  alpha = beta * q
  and
  exists gamma, q = gamma^2.
```

This is logically simple, so add it only if it improves downstream API use.
Do not count a purely definitional repackaging as the main Outcome A result.

The substantive theorem is the conjugate-coordinate criterion above.

### 5. Norm consequences

From

```text
alpha = beta * gamma^r
```

prove the expected norm identity if not already available in an adequate form:

```text
norm alpha = norm beta * (norm gamma)^r.
```

Prefer deriving a generic `norm_pow` helper from existing `traceOne_norm_mul`.
Do not add parallel norm definitions.

For `r=2`, this gives a necessary square-norm condition, but do not claim that
square norm alone implies square/Core landing.

### 6. Strictness regression: lattice landing is not Core landing

Add a kernel-checked example showing the square filter is strictly stronger
than divisibility/lattice landing.

Preferred simple regression:

```text
s = 0
beta  = 1
alpha = <2,0>.
```

Prove both:

```text
beta | alpha
```

and

```text
not exists gamma : TraceOneInt 0, alpha = beta * gamma^2.
```

The second claim should reduce to the first square coordinate equation
`m^2 = 2` and be discharged arithmetically.

This regression is important: it certifies the strict chain

```text
integer-lattice landing
not=>
square/Core-image landing.
```

### 7. Optional Eisenstein specialization

Only if short and useful, add a regression/corollary at `s = -1` that agrees
with `eisensteinCoord_sq` / `eisensteinCoord_mul_sq`.

Do not refactor the existing Eisenstein modules merely to force reuse.

## Outcome policy

### Outcome A — CORE LANDING ESTABLISHED

Accept if production proves the exact square/Core coordinate iff under
`norm beta != 0`, together with the strictness regression.

An arbitrary-power receiver is a useful bonus but not required for Outcome A.

### Outcome B — POWER RECEIVER ONLY

Use if the generic quantified power receiver is clean, but the explicit
square/Core coordinate iff cannot be completed without unjustified extra
infrastructure.

### Outcome C — NO MATERIAL GAIN

Use if the only possible additions are decorative predicates or tautological
rewrappings of `exists gamma, ...` with no new coordinate criterion.

Do not add such wrappers merely to produce code.

## Scope exclusions

Do not add:

```text
UFD / PID / Euclidean-domain instances;
universal square-root or r-th-root providers;
prime-existence theorems;
ABC / FLT / Petal / Legendre application bridges;
MultiGauge transition providers;
MG-002 automata;
analytic estimates.
```

Do not assume that norm-square conditions are sufficient for element-square
conditions.

## Validation

At minimum run:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.Lib.NumberTheory.TraceOneLatticeLanding
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib
git diff --check
```

Scan changed Lean sources for:

```text
sorry
admit
new axiom declarations
```

No new warning diagnostics should be introduced.

## Documentation

Create:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-008.md
```

Report:

- exact theorem names and signatures;
- whether arbitrary-power receiver was added;
- square/Core coordinate iff;
- strict lattice-vs-Core regression;
- norm consequences;
- build/audit results;
- any deviation from the requested neutral module layout.

Update `ROADMAP.md` only to reflect the actual achieved outcome.
