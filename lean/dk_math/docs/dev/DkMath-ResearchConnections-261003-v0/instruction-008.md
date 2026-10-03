# DRC-008 — FLT7 current aggregation

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Use only the current FLT7 packet stack and current ownership/cutoff
infrastructure to determine how far the exponent-seven descent can now be
kernel-checked.

The intended progression is:

~~~text
current local ownership
  -> aggregate all current prime-ideal exponents
  -> principalization / class-group receiver
  -> unit sector
  -> seventh-power coordinate landing
  -> additive relation preserved
  -> strict descent.
~~~

This checkpoint is about assembling the current theorem stack honestly. It is
not an instruction to force an FLT7 theorem if a genuine mathematical frontier
remains.

## What to do

Treat this as a current-state audit, aggregation, and closure task.

- Identify the canonical current FLT7 counterexample/routing packets and the
  current degree-six / cyclotomic ownership and cutoff endpoints actually used
  by the public architecture.
- Distinguish those from historical, oriented, experimental, or superseded
  carriers. Use an older carrier only through an explicit checked bridge into
  the current one.
- Aggregate the local prime-ideal ownership statements over the complete
  current finite support, preserving exact exponents and conjugate orientation.
- Determine the strongest current global ideal-power statement that follows.
- Feed that statement into the existing principalization / class-group
  receiver when its hypotheses are available; keep any class-group hypothesis
  explicit.
- Continue through the existing unit-sector and seventh-power coordinate
  landing machinery when the required hypotheses can actually be discharged.
- Preserve the Fermat additive relation through every transport.
- If the current stack reaches a genuine smaller positive counterexample,
  kernel-check the strict descent and close FLT7.
- If it does not, stop at the exact first missing theorem and formalize the
  strongest correct aggregation/receiver theorem that isolates that frontier.

Reuse the generic infrastructure added in DRC-001 through DRC-007 whenever it
simplifies or strengthens the current route, but do not refactor working FLT7
code merely for stylistic uniformity.

The exact files, theorem names, packet boundaries, aggregation representation,
and proof strategy are for you to determine from the repository.

## Expected outcome

Outcome A does **not** require pretending that FLT7 is closed.

Outcome A means that the current FLT7 route has been advanced to the strongest
honest kernel-checked endpoint available from the present repository, with the
local-to-global aggregation completed wherever the existing data suffice and
the next mathematical frontier stated exactly.

If all remaining hypotheses can be discharged and strict descent closes, expose
the resulting unconditional FLT7 theorem and audit it. If not, expose a precise
frontier theorem rather than a speculative closure.

## Boundaries

Do not:

- switch back to historical/oriented carriers merely because their scalar
  norms match the current carrier;
- promote local ownership to global factorization without a checked finite
  aggregation theorem;
- turn ideal p-th powers into element p-th powers without the required
  class-group/principalization and unit data;
- drop unit-sector information during seventh-power extraction;
- infer element identity from norm equality;
- lose the original Fermat additive relation during coordinate transport;
- claim strict descent without an explicitly smaller positive counterexample;
- weaken unresolved assumptions by hiding them in structures or typeclass
  instances;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts.

If the current public/current packet stack is ambiguous, resolve that by
repository audit and document which stack is canonical before implementing
aggregation.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks for every new aggregation/bridge;
- current-stack regression tests;
- compatibility checks against public FLT prime / FLT7 facades;
- axiom audit of every new public endpoint;
- full build and `DkMathTest` build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-008.md
~~~

with Outcome A / B / C and, in particular:

- the canonical current FLT7 stack selected;
- what local ownership data were aggregated;
- the exact global ideal/element/descent endpoint obtained;
- every remaining hypothesis, if any;
- whether unconditional FLT7 was actually reached;
- the first unresolved theorem if it was not;
- validation and axiom results.

Do not finish the checkpoint without a report.
