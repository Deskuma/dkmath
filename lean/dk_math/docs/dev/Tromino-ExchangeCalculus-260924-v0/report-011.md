# TRM-012 report: same-label pairing / Tromino residual normal form

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-012 turns every finite `BoundarySignature` into an explicit
same-label involutive pairing. Fixed points are the residual ports. The
checkpoint stops at this finite normal form; no `TransitionGraph`, physical
boundary extraction, planar non-crossing pairing, XOR path transport,
`BoundaryIR`, residual optimization, or Four Color claim is introduced.

## Mathlib pairing API audit and decision

The local Mathlib checkout provides:

- `Function.Involutive` for the certificate law;
- `Finset.orderIsoOfFin`, the increasing equivalence between `Fin k` and an
  ordered finite set;
- `Finset.orderEmbOfFin` and
  `Finset.coe_orderIsoOfFin_apply` for returning to indexed ports;
- `Fintype.equivFin` and finite permutation infrastructure, but no smaller
  dedicated matching API was needed here.

The implementation uses `Finset.orderIsoOfFin` rather than a generic
existence/matching theorem. It pairs consecutive ranks in each label fiber.
The last rank is fixed exactly when the fiber cardinality is odd. This is
Outcome A: a deterministic ordered construction, with no new declaration
marked `noncomputable` and no classical choice used to select a pairing
certificate.

## Certificate and residual representation

Production is `DkMath/Tromino/BoundaryPairing.lean`:

```lean
structure BoundaryPairing (S : BoundarySignature) where
  mate : Fin S.arity → Fin S.arity
  involutive : Function.Involutive mate
  sameLabel : ∀ i, boundaryDelta S (mate i) = boundaryDelta S i
```

`residualPorts P` is the filtered `Finset` of fixed points, and
`pairedPorts P` is its finite complement. The API includes the simp-friendly
membership equivalence, closure of non-residual ports under `mate`, and the
transition-readiness theorem: a non-residual port has a distinct mate, the
same boundary delta, and returns under the involution.

`portsWithLabel S delta` is the thin filtered-port fiber and its cardinality
is definitionally `boundaryLabelCount S delta`.

## Canonical construction

`adjacentMate n` pairs ranks `0 ↔ 1`, `2 ↔ 3`, and so on, fixing the final
rank for odd `n`. The proof establishes involutivity and:

```text
card {i | adjacentMate n i = i} = n % 2
```

`fiberPairing` transports this map through the increasing order equivalence
of each label fiber. `canonicalMate` combines the three fiber-local maps,
and `canonicalBoundaryPairing` packages its involution and label law.

For every label, the residual fiber is carried bijectively to the fixed-rank
fiber of `adjacentMate`; therefore:

```text
card (residualPorts canonicalBoundaryPairing).filter (boundaryDelta = delta)
  = boundaryLabelCount S delta % 2
```

The total residual cardinality is the sum of the A/B/C residual cardinalities.
Consequently, a conserved even signature has no residual, while a conserved
odd signature has exactly three residual ports, one in each of the A/B/C
fibers. The conserved decomposition theorem packages the empty or cardinality
three alternatives using TRM-011's parity dichotomy.

## Regression audit

`DkMathTest/Tromino/BoundaryPairingAxiomAudit.lean` checks:

1. the empty signature has no residual;
2. `A A B B C C` is conserved and pairs perfectly;
3. `A A A B B B C C C` has three residual ports and one residual in each
   label fiber;
4. `A A B C` has two residual ports, one B and one C;
5. duplicate indexed contacts `A A` have no residual, and each indexed port
   is non-fixed, guarding against Finset-of-contacts collapse;
6. the transition-readiness theorem for arbitrary non-residual ports.

## Computability and axiom audit

No `sorry`, `admit`, `unsafe`, new `axiom`, or `noncomputable` declaration is
present in the production or audit source. The canonical certificate is an
ordinary executable `def` assembled from ordered finite data. The focused
`#print axioms` audit reports only the standard foundational dependencies
(`propext`, `Quot.sound`, and, through the existing finite ordered-set
infrastructure, `Classical.choice`); no project-local axiom is introduced.

## Validation

Focused builds completed successfully:

```text
lake build DkMath.Tromino.BoundarySignature
lake build DkMath.Tromino.BoundaryPairing
lake build DkMathTest.Tromino.BoundaryPairingAxiomAudit
```

The audit build completed successfully at 1497 jobs. The only build messages
are existing Mathlib/linter notices and deprecation notices for the local
`dif_pos` proof syntax; no proof failure remains.

## Stop boundary

TRM-012 stops at the finite same-label normal form: disjoint 2-cycles plus at
most one residual port of each nonzero label, with the conserved cases reduced
to either a perfect pairing or a perfect pairing plus one A/B/C residual.
Transition graphs, geometric non-crossing structure, physical extraction,
path transport, optimization, and Four Color claims remain deferred.
