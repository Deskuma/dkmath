# FLT7 Ultra Research Challenge — Complete-Support Seventh Divisibility

Branch: **research/FLT7-CompleteSupport-Ultra-261004-v0**

## Target

The current FLT7 route has reached a precise frontier.

For a fixed current phase-corrected degree-six carrier `A`, let

```lean
I := carrierIdeal c
```

The repository proves an exact local cutoff at the selected current oriented
prime:

```text
A ∈ P^k  ↔  k ≤ 14e.
```

It also proves complete finite height-one support factorization and a checked
receiver saying that if every support exponent is divisible by seven, then

```text
A = u * beta^7
```

for a unit `u`, while preserving the original Fermat equation.

The unresolved theorem is essentially:

```lean
∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
  7 ∣ exponent (carrierIdeal c) v
```

Do **not** assume this theorem.

Your job is to perform a deep repository-wide mathematical audit and determine
why complementary support remains, whether it can actually occur, and what
existing structure controls it.

## Research question

Investigate possible bridges among:

- current FLT7 phase-corrected carriers and residue addresses;
- exact current oriented/conjugate ownership and cutoff theorems;
- carrier product and norm identities;
- prime-below / height-one support structure in the current degree-six ring;
- DRC-004 prime cyclic gluing;
- DRC-005 prime-shell roots, roots of unity, and finite Hensel structure;
- DRC-006 split/inert/ramified residue classification;
- DRC-007 QR/QNR provenance, explicit quadratic subfield, relative norm, and
  ideal transport;
- existing cyclotomic factorization, Galois action, conjugation, Dedekind
  support, and prime-over-rational-prime APIs;
- any theorem forcing a prime ideal dividing the current carrier to arise from
  a current residue address or its conjugate.

A promising conceptual route is:

```text
prime ideal in complete carrier support
  -> rational prime below it
  -> order-seven / cyclotomic residue condition
  -> current residue address
  -> oriented or conjugate ownership
  -> exponent divisible by 7.
```

But do not force this route if another formulation is stronger or more natural.

## Mandatory durable-checkpoint protocol

This is critical.

The model/session may run out of usage allowance before the research is
finished. Therefore **important reasoning must be written to disk continuously**.

Use:

```text
docs/dev/FLT7-CompleteSupport-Ultra-261004-v0/findings-001.md
```

as an append-oriented durable log.

### You MUST update findings-001.md:

1. immediately after the initial repository audit;
2. whenever you identify a new relevant theorem/module/packet;
3. whenever a proposed proof route succeeds or fails;
4. whenever you discover a non-obvious obstruction or missing datum;
5. before starting any long/full build;
6. before making a large refactor or implementation attempt;
7. before switching to a substantially different proof strategy;
8. whenever you have enough information that losing the current session would
   otherwise cause meaningful duplicated work.

Do not wait until the end.

Each update should be concise bullet points and should include, when relevant:

- exact file/module/theorem names;
- what was learned;
- why it matters for complete support;
- hypotheses still missing;
- whether the item is proved, inferred, or only a candidate;
- next route to test.

When a research phase becomes stable, make a small git commit if practical.
Prefer multiple meaningful checkpoint commits over one giant final commit.

### Durable log format

Maintain these sections:

```markdown
## Current status
## Confirmed facts
## Candidate bridges
## Failed / blocked routes
## Open obligations
## Next action
## Checkpoint history
```

Update `Current status` and `Next action` on every durable checkpoint.

## Initial diagnosis required

Before major implementation, record in `findings-001.md` a concise diagnosis:

1. what the complementary support can consist of;
2. which existing theorem families constrain it;
3. the most promising proof route;
4. whether DRC-004 through DRC-007 materially change the frontier;
5. the exact theorem you intend to prove first.

Only after that diagnosis should you begin substantial proof implementation.

## Desired outcomes

### Outcome A

Prove complete-support seventh divisibility and continue the existing checked
route as far as it honestly goes.

### Outcome B

Find a stronger or more natural structural theorem implying the required
divisibility, implement it, and connect it to the current receiver.

### Outcome C

Show precisely why the present data are insufficient. Identify the smallest
missing mathematical datum/theorem, preferably with a formal obstruction or
model explaining why current facts cannot determine the complementary
exponents.

Outcome C is a valid research success.

## Boundaries

Do not:

- use historical/oriented carriers merely because their scalar norms match;
- identify elements from equality of norms;
- silently discard complementary support;
- infer global exponent divisibility from one selected local row;
- lose orientation/conjugation data;
- hide unresolved assumptions in structures or typeclass instances;
- turn ideal seventh powers into element seventh powers without the checked
  principalization/unit receiver;
- claim strict descent without a smaller positive counterexample;
- use `sorry`, `admit`, new axioms, `unsafe`, or equivalent shortcuts.

If DRC-004 through DRC-007 do not bridge into the current FLT7 carrier, say so
explicitly and record the exact carrier mismatch.

## Implementation policy

Search first. Reuse current production APIs.

You may introduce a new neutral reusable theorem in `DkMath.Lib` if the audit
shows that it is the genuine missing abstraction. Do not refactor stable FLT7
code merely for stylistic uniformity.

Use focused builds during development. Before any full build, checkpoint the
current findings to disk.

## Final deliverable

If the run reaches a stable stopping point, create:

```text
docs/dev/FLT7-CompleteSupport-Ultra-261004-v0/report-001.md
```

containing:

- Outcome A/B/C;
- canonical current stack used;
- exact new theorem(s);
- whether complete-support seventh divisibility was proved;
- how DRC-004 through DRC-007 did or did not contribute;
- remaining hypotheses or the exact first unresolved theorem;
- validation and axiom audit;
- explicit statement whether unconditional FLT7 / strict descent was reached.

Even if no final report is reached because of usage exhaustion,
`findings-001.md` is the authoritative recovery artifact.
