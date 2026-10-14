# Instruction 002 — Successor Degree / Factor-World Reset Ultra exploration

## Mission

Study the transition

```text
d -> d + 1
```

as a possible structural reset of both:

1. the GN factor world, and
2. the unit-power gauge.

The previous Gap Focusing campaign established Outcome B:

- fixed-anchor Gap decomposition is canonical in the polynomial setting;
- GN retains all nontrivial cyclotomic phases;
- for `d >= 2`,
  `GN_d(X,1)` is irreducible over `Z[X]` / `Q[X]` exactly when `d` is prime;
- the FLT residual unit class requires additional power extraction and
  ramifier-normalization data.

This instruction asks what happens **between adjacent degrees**.

Do not assume in advance that factor-world reset and unit-gauge reset are one
phenomenon.  Determine whether they are genuinely linked or merely parallel
consequences of `gcd(d,d+1)=1`.

## Phase 1 — successor identities

Starting from the current production GN / GTail API, derive or prove neutral
theorems for

```text
GN_{d+1}(x,u)
  = (x+u) * GN_d(x,u) + u^d
```

and

```text
GN_{d+1}(x,u)
  = u * GN_d(x,u) + (x+u)^d.
```

Record the weakest useful algebraic assumptions.

For the unit-gap specialization `u=1`, isolate the Bézout-type identity

```text
GN_{d+1}(x,1) - (x+1) * GN_d(x,1) = 1.
```

Audit whether the polynomial version is stronger or cleaner than only
pointwise integer statements.

## Phase 2 — adjacent-degree factor support

Determine exactly what the successor identities imply about common factors.

Primary target:

```text
gcd(x,u)=1
  -> gcd(GN_d(x,u), GN_{d+1}(x,u)) = 1
```

in an appropriate natural/integer setting.

Do not overstate the result.  If the strongest honest theorem is instead that
every common prime divisor of the two GN values divides both `u^d` and
`(x+u)^d`, record that theorem and derive the primitive-pair corollary.

For `u=1`, investigate whether the Bézout identity gives a stronger universal
coprimality theorem directly.

The research interpretation to test is:

```text
successor degree changes the visible prime-factor support.
```

Do not call this a "new prime appears at every step" theorem unless that is
actually proved.

## Phase 3 — polynomial successor separation

Use the new Gap Focusing / prime-degree kernel API where useful.

Let

```text
K_d(X) = GN_d(X,1).
```

Study the relation between `K_d` and `K_{d+1}` as polynomials.

Questions:

- Are they coprime in `Z[X]` or `Q[X]` for all positive d?
- Is there a direct Bézout witness from the successor identity?
- How does the cyclotomic divisor-layer description change from d to d+1?
- Which cyclotomic layers disappear, persist, or are replaced?

Separate the exact theorem from the heuristic phrase "factor-world reset".

## Phase 4 — unit-power gauge at adjacent exponents

Let `U = R^×` be the unit group and consider the power subgroups

```text
U^d
U^(d+1).
```

Because `gcd(d,d+1)=1`, investigate the honest group-theoretic statements

```text
U^d * U^(d+1) = U
```

and

```text
U^d ∩ U^(d+1) = U^(d(d+1)).
```

Do not assume these exact formulations compile unchanged; choose the correct
subgroup / image-of-power formulation for Lean.

If supported, investigate a CRT-style quotient decomposition morally of the
form

```text
U / U^(d(d+1))
  ~= (U / U^d) × (U / U^(d+1)).
```

Be explicit about the category and hypotheses required.

If a cleaner statement is available for arbitrary abelian groups written
additively via multiplication-by-n maps, prefer the mathematically natural
form and then specialize to units.

## Phase 5 — compare the two successor phenomena

Once both sides are formalized, answer:

> Does `d -> d+1` define one checked reset principle acting simultaneously on
> GN factor support and unit-power gauge?

Possible outcomes:

### Outcome A — common successor reset

There is a meaningful common structural statement: adjacent degrees are
separated both in GN factor support and in unit-power gauge by the same
coprime-exponent mechanism, with a nontrivial formal bridge between the two.

### Outcome B — parallel but distinct layers

Adjacent-degree GN coprimality / factor separation is a strong theorem, and
adjacent unit-power quotients admit a separate CRT-like decomposition, but no
honest theorem identifies them as one structure without additional arithmetic
data.

### Outcome C — superficial analogy

The apparent commonality is only the elementary fact
`gcd(d,d+1)=1`; packaging the two subjects as one reset principle obscures
rather than explains the mathematics.

Any of A/B/C is a successful result.

## Phase 6 — Zsigmondy / primitive-prime audit

Only after the successor structure is stable, audit existing DkMath and Mathlib
material related to:

- Zsigmondy-style primitive prime divisors;
- primitive prime support of `a^n-b^n`;
- cyclotomic-value prime divisors;
- existing DkMath PrimitiveSet / primitive-scale APIs.

Research question:

> Is the phrase "each new degree exposes a new prime direction" justified by an
> existing or provable primitive-prime theorem, and if so under exactly which
> exceptions?

Do not silently import the classical Zsigmondy theorem as an explanation if it
is not available in the current formal stack.

Keep separate:

```text
adjacent GN values are coprime
```

from

```text
every degree has a primitive prime divisor.
```

They are different claims.

## Phase 7 — relation to previous DkMath themes

Compare the checked results with:

- Gap Focusing / Prime Degree Rigidity;
- the FLT3/5/7 normalization-fixed unit-power class;
- DRC product-degree composition;
- primitive-prime / PrimitiveSet work;
- the earlier "natural number +1 changes the factor world" interpretation.

The goal is to determine what can now be stated as mathematics rather than
metaphor.

Do not start a new FLT proof campaign.

Do not connect this result to the magic-square `2p` observation unless the
successor analysis itself produces a precise map.  The `2p` work from
Instruction 001 remains a separate multiplicative-degree phenomenon.

## Implementation guidance

Prefer:

- neutral theorems under `DkMath.NumberTheory.GapFocusing.*` if they naturally
  extend the existing package;
- reusable abelian-group lemmas under an appropriate neutral library namespace
  if unit-gauge statements are not specific to number theory;
- small test/regression files and explicit axiom audits.

Avoid:

- theorem names that claim "reset", "moire", or "world change" unless the formal
  statement itself justifies that terminology;
- structures whose fields simply assume the desired coprimality or CRT result;
- production changes that are only cosmetic refactors;
- norm-only identification of elements or carriers.

## Durable checkpoint protocol

Update the campaign findings continuously.

Checkpoint after:

- successor identities;
- common-factor / coprimality theorem;
- polynomial Bézout/cyclotomic-layer analysis;
- unit-group intersection/product analysis;
- CRT quotient result or failure;
- A/B/C decision;
- Zsigmondy/primitive-prime audit.

If the run is interrupted, the findings must make the next mathematical action
obvious.

## Minimum deliverable

The final report should answer:

1. What exact successor identities hold for GN?
2. What do they imply about common prime-factor support?
3. Are `GN_d(X,1)` and `GN_{d+1}(X,1)` polynomially coprime?
4. How do `U/U^d` and `U/U^(d+1)` relate?
5. Does a genuine CRT-style successor gauge theorem hold?
6. Is there any theorem-level bridge between factor reset and unit-gauge reset?
7. What, if anything, can safely be said about primitive new prime directions?

End with Outcome A, B, or C and list all remaining interpretive claims
separately from Lean-checked mathematics.
