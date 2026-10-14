# DRC-007 — Cyclotomic QR provenance lift

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Lift the existing quadratic-residue / nonresidue provenance data from scalar
norm compatibility to the strongest kernel-checked element-level statement
actually supported by the current DkMath packets.

The guiding chain is:

~~~text
QR / QNR products
  -> Gauss difference
  -> TraceOne coordinates
  -> element identity in an explicit quadratic subfield
  -> relative norm
  -> ideal transport
~~~

The key point is to preserve provenance: equal scalar norms alone are not enough.

## What to do

Treat this as an audit-and-lift task.

- Inspect the current QR/QNR provenance packets, Gauss-product/difference APIs,
  TraceOne bridges, cyclotomic norm code, prime-ideal ownership code, and any
  explicit quadratic-subfield embeddings already present.
- Determine exactly which data are strong enough to reconstruct an element,
  rather than only its norm.
- If an element-level lift is available, formalize the cleanest reusable theorem
  that carries the existing provenance into an explicit quadratic/TraceOne
  target and then through the appropriate relative norm / ideal map.
- Reuse the existing signed-prime/discriminant conventions and current
  cyclotomic carriers.
- Prefer a smaller precise provenance theorem over a broad statement that
  silently forgets signs, units, conjugation choices, or ideal ownership.
- Keep current FLT7 carriers and current ownership infrastructure distinct from
  historical/oriented variants unless an explicit checked bridge exists.

The exact source packet, target algebra, theorem statements, maps, namespaces,
and proof strategy are for you to determine from the repository.

## Expected mathematical result

A successful Outcome A should leave DkMath with a production-level bridge in
which QR/QNR or Gauss provenance determines an actual element-level quadratic
object, and where the relevant relative norm / ideal statement is derived from
that element data.

A partial but structurally correct endpoint is preferable to an unjustified
norm-to-element reconstruction.

## Boundaries

Do not:

- infer element equality from scalar norm equality;
- erase sign, unit, conjugation, or QR/QNR provenance needed to identify the
  element;
- turn ideal data into principal element data without the required
  principalization/class-group hypothesis;
- identify historical/oriented and current FLT7 carriers merely because their
  norms agree;
- duplicate an existing TraceOne/cyclotomic bridge without a clear reason;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty from this repository connection alone.

If the current provenance packet is insufficient for the full chain, identify
the exact missing datum and formalize the strongest correct intermediate
theorem instead of guessing it.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- meaningful provenance/sign/conjugation regressions;
- compatibility with existing cyclotomic and ownership endpoints;
- public API integration where appropriate;
- axiom audit;
- full build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-007.md
~~~

with Outcome A / B / C, the source provenance packet used, the exact
element-level statement obtained, how norm and ideal transport follow, what was
not inferred, validation results, and any remaining obstruction.

Do not finish the checkpoint without a report.
