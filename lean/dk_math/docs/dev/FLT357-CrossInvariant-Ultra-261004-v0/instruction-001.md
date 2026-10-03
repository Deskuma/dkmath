# Instruction 001 — FLT3/5/7 cross-invariant pre-audit

## Mission

Perform a bounded, source-grounded comparison of the current FLT3, FLT5, and
FLT7 proof architectures.

Do **not** begin by trying to prove FLT7 or general FLT.

Instead answer:

> Can the already-unconditional p=3 and p=5 proofs, and the current p=7
> partial proof, be expressed through the same structural layers?  If yes,
> what is the smallest honest common invariant/schema?  If not, where does
> the first genuinely mathematical split occur?

The new FLT7 endpoint available on this branch is:

```text
(A) = P7 * J^7
A   = lambda * u * beta^7
```

with ramified exponent 1, every nonramified exponent divisible by 7, and the
unit/additive-descent frontier still open.

Use this as an observation lens, not as a pattern to impose.

## Core comparison axes

For each of p=3,5,7, identify the actual production theorem/module supporting
each axis below, or explicitly record that no such layer exists.

1. **Original integer/GN factorization**
   - Where is `(x+u)^p-u^p = x*GN_p(x,u)` or its FLT specialization used?
   - What is the exact distinguished factor/carrier?

2. **Cyclotomic / algebraic carrier**
   - What ring/order is actually used?
   - Is it the full cyclotomic carrier, a real subfield/order, a quadratic
     TraceOne carrier, GoldenInt, EisensteinInt, or something else?
   - Never identify carriers from matching norms alone.

3. **Ramified direction**
   - Is there an explicit analogue of `lambda_p = 1-zeta_p`?
   - Is a fixed ramified multiplicity extracted?
   - Does that layer collapse into another theorem at low p?

4. **Normalized ideal power**
   - After ramified stripping, is the principal ideal actually a p-th power?
   - Is this obtained via coprime factors, PID/UFD, class-group torsion, or a
     special low-degree theorem?

5. **Unit / phase class**
   - What is the exact unit quotient left after ideal extraction?
   - Is it trivial, finite-sector, singleton, or handled by projective/phase
     coordinates?
   - Distinguish p-specific unit classification from a generic theorem.

6. **Integral/additive landing**
   - How does an algebraic p-th power return to integer/natural coordinates?
   - Which theorem prevents a norm-only argument from being mistaken for an
     element/coordinate identity?

7. **Strict descent / contradiction**
   - What decreases?
   - Is the decrease an integer, natural measure, norm, valuation depth, or a
     finite-state exclusion?
   - Is positivity/primitivity reconstructed?

## Required FLT3/FLT5 reverse projection

Try to restate the existing completed p=3 and p=5 routes in the FLT7-style
sequence

```text
ramified correction
-> normalized ideal p-th power
-> unit class
-> additive landing
-> descent
```

without changing their mathematical content.

A successful projection need not introduce new production code.

If a layer is invisible because p=3 or p=5 collapses it automatically, identify
the exact theorem making it collapse.

If the route fundamentally differs, state the first non-cosmetic obstruction.

## One-thread versus stripe-pattern test

Do not assume that "one theorem" means "no cases".

Distinguish these possibilities:

### Outcome A — literal common spine

One honest theorem schema/invariant applies to p=3,5,7; the p=3 and p=5
unconditional endpoints can be read as completed instances, while p=7 stops at
a later unresolved component of the same schema.

### Outcome B — one invariant with discrete sectors

A common invariant exists, but its values split by data such as

- p mod 4,
- signed prime parameter,
- residue/splitting type,
- unit-sector class,
- residue degree,
- class-group p-torsion,
- ramified exponent / phase data.

The visible proof branches are then values of one discrete state machine rather
than unrelated patches.  Identify the minimum state coordinates needed.

### Outcome C — genuinely different mechanisms

No honest common invariant can be found from the current source.  Identify the
first theorem-level point where p=3, p=5, and p=7 require mathematically
different mechanisms.  Do not hide the split behind a fabricated abstraction.

Any of A/B/C is a valid result.

## Moire / sampling question

Test the following interpretation carefully:

> Smooth algebraic power geometry may become a striped or moire-like pattern
> when sampled on the integer/cyclotomic lattice because several discrete
> structures interfere.

If source evidence supports it, identify the concrete periodic/state variables.
Examples may include p mod 4, unit rank/sectors, quadratic character, splitting
degree, ramification, or class-group p-torsion.

Do not promote this metaphor into a theorem without an actual invariant.

## p=11 and p=13 forecast

Only after the 3/5/7 comparison is stable, give a source-grounded forecast for
p=11 and p=13:

- which common layers already have generic APIs;
- which carrier arithmetic is missing;
- which unit/sector datum is missing;
- whether the p=7 ramified correction predicts an analogous mandatory factor;
- which exact obligation would be the first blocker.

No FLT11/13 implementation is requested.

## Existing generic architecture

Audit, do not silently inherit, the current prime-generalization branch summary
and production facade.  In particular check the already-recorded distinctions:

- p mod 4 unit-sector behavior;
- p=3 carrier/API boundary;
- GoldenInt versus TraceOneInt at p=5;
- explicit class-group p-torsion/principalization hypotheses.

Determine whether those are essential state coordinates or artifacts of the
current implementation.

## Implementation restraint

This is a **pre-audit**.

Allowed:

- source searches and exact theorem mapping;
- small scratch Lean files or tiny test-only probes;
- `#check`, `#print axioms`, focused module builds if needed to verify a
  disputed bridge;
- a small neutral lemma only if it is necessary to decide A/B/C and clearly
  belongs in `DkMath.Lib`.

Do not:

- start a new unconditional FLT7/11/13 proof campaign;
- refactor completed FLT3/FLT5 merely for cosmetic uniformity;
- add a generic theorem whose hypotheses simply encode the desired conclusion;
- identify elements/carriers from equal norms;
- use historical/sorry-bearing routes as evidence for a production theorem
  without an explicit dependency audit;
- run full `lake build` unless the pre-audit unexpectedly makes production
  changes requiring it.

## Durable checkpoint protocol

The five-hour usage limit may stop the run before completion.

Therefore update

`docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/findings-001.md`

continuously.

Write a checkpoint:

- after the initial source inventory;
- after mapping each of p=3, p=5, and p=7;
- whenever a candidate common invariant appears;
- whenever that invariant fails;
- before any nontrivial scratch proof or build;
- before changing strategy;
- before any action whose loss would require substantial repeated research.

Do not wait for a final report.

If interrupted, the findings file should make the next action obvious.

## Deliverable for this bounded run

The minimum useful deliverable is a matrix for p=3,5,7 with rows:

```text
carrier
ramified correction
normalized ideal power
unit/phase class
additive landing
descent measure
remaining obstruction
```

plus:

- current A/B/C assessment;
- candidate invariant/state coordinates;
- exact source theorem names supporting each nontrivial claim;
- first predicted blockers for p=11 and p=13 if enough evidence is available.

A final `report-001.md` is optional for this bounded pre-audit.  Durable
`findings-001.md` takes priority.
