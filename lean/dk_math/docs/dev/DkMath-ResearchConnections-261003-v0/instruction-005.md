# DRC-005 — General prime-shell Hensel

Branch: **research/DkMath-ResearchConnections-261003-v0**

## Goal

Generalize the existing cubic Hensel-depth machinery from the degree-three shell
to the prime shell of arbitrary prime degree.

The intended arithmetic picture is:

~~~text
GN p g u ≡ 0 mod q
~~~

for distinct primes `p` and `q`, with `q` not dividing the relevant base,
corresponds to a nontrivial p-th root of unity modulo `q`. Away from the
ramified prime `q = p`, these roots should be simple and should lift uniquely
through powers of `q`.

The implementation should expose the clean reusable theorem/API behind that
picture.

## What to do

Treat this as an audit-and-generalize task.

- Inspect the existing cubic infrastructure, especially
  `DkMath.NumberTheory.GNThreeHenselDepth` and
  `DkMath.NumberTheory.GNThreePairedDepth`, together with the current GN /
  cyclotomic / valuation APIs.
- Audit pinned Mathlib for the most natural Hensel, derivative, root-of-unity,
  `ZMod`, valuation, and lifting machinery.
- Decide which parts of the cubic theory are genuinely degree-three and which
  are instances of a prime-shell theorem.
- Formulate and kernel-check the strongest clean reusable prime-degree result
  supported by the current repository.
- Include the non-ramified lifting behavior and exact-depth information where
  the existing abstractions make this natural.
- Keep the ramified case `q = p` explicitly separate rather than hiding it in
  stronger assumptions.
- Preserve existing cubic APIs and downstream users; specialize the generic
  result back to degree three when that is useful and stable.

The exact theorem statements, namespaces, proof strategy, and weakest practical
hypotheses are for you to determine.

## Expected mathematical result

A successful Outcome A should leave DkMath with a production-level generic
prime-shell Hensel API that explains the existing cubic phenomenon as a special
case.

In some mathematically equivalent form, it should make precise the chain

~~~text
prime-shell root mod q
  <-> nontrivial p-th root of unity mod q
  -> simple root when q != p
  -> unique lift to q^k
  -> controllable / exact q-adic depth.
~~~

A smaller set of reusable endpoints is preferable to a large monolithic theorem
if that matches the existing library better.

## Boundaries

Do not:

- infer a generic prime theorem from fixed-prime computations;
- merge the ramified `q = p` case with the non-ramified simple-root case;
- assume invertibility or nonvanishing of a base silently;
- duplicate the cubic Hensel implementation without extracting the common
  structure;
- use `sorry`, `admit`, new axioms, or unsafe shortcuts;
- claim mathematical novelty from this repository generalization alone.

If the full expected chain requires assumptions not visible in the schematic
goal, determine and state the correct hypotheses rather than forcing the target.

## Validation and deliverable

Use the normal DkMath workflow:

- focused kernel checks;
- representative prime/boundary regressions;
- compatibility with the existing cubic endpoints where appropriate;
- public API integration;
- axiom audit;
- full build when practical.

Always leave:

~~~text
docs/dev/DkMath-ResearchConnections-261003-v0/report-005.md
~~~

with Outcome A / B / C, the generic theorem(s) obtained, the relation to the
existing cubic machinery, the ramified/non-ramified boundary, validation
results, and any remaining obstruction.

Do not finish the checkpoint without a report.
