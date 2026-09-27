# TRM-015 report: label-only boundary flow certificate / contact erasure

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-015 introduces an independent label-only boundary carrier. It retains
port identity, multiplicity, arity, and one nonzero `TrominoState` delta per
port, while omitting all `BoundaryContact` inside/outside data.

The existing TRM-012, TRM-013, and TRM-014 APIs remain unchanged and are not
migrated to this carrier. Color recovery, open residual paths, ghost
completion, planarity, `BoundaryIR`, optimization, and Four Color claims are
not introduced.

## FlowSignature representation and erasure

Production is `DkMath/Tromino/FlowSignature.lean`:

```lean
structure FlowSignature where
  arity : Nat
  label : Fin arity → TrominoState
  nonzero : ∀ i, label i ≠ 0
```

`BoundarySignature.toFlowSignature` is a computable projection with label
`boundaryDelta S` and nonzero proof `boundaryDelta_ne_zero S`. The public
simp bridges expose the erased arity and label exactly.

## Independent flow observers

`flowSum`, `FlowConserved`, and `flowLabelCount` are defined directly from
`FlowSignature`; none is an alias of the corresponding contact-based
observer. The module proves:

- zero has count zero;
- every label is A, B, or C;
- A/B/C counts sum to the arity;
- the two coordinate formulas for `flowSum` in terms of A/C and B/C counts.

The existing ZMod-2 coordinate lemma is reused only as the generic parity
bridge, not as a definition of the flow observers.

## Label-only conservation kernel

`flowConserved_iff_parity` proves:

```text
FlowConserved F ↔
  countA % 2 = countC % 2 ∧ countB % 2 = countC % 2
```

`flowConserved_even_or_odd` then gives the all-even or all-odd dichotomy.
This theorem depends only on nonzero delta labels and the additive
Klein-four carrier.

## Exact erasure calibration

The module proves the exact identities:

```text
flowSum S.toFlowSignature = boundarySum S
FlowConserved S.toFlowSignature ↔ BoundaryConserved S
flowLabelCount S.toFlowSignature delta = boundaryLabelCount S delta
```

The boundary conservation parity theorem is reproduced through
`boundaryConserved_iff_flowConserved_parity`, without removing or renaming
the original contact-based API.

## Information loss and gauge calibration

The contact-level observation is explicit: absolute inside/outside states are
not retained, only their difference. `contactDelta_same_of_translation`
shows that contacts of the form `(x, x + delta)` erase to `delta` for any
origin `x`.

`exchangeBoundaryContact` translates both sides by the same `gamma`, and
`contactDelta_exchangeBoundaryContact` proves that the erased delta is
unchanged. This is a small translation-invariance calibration, not a general
gauge-theory API.

## Independent audit fixtures

`DkMathTest/Tromino/FlowSignatureAxiomAudit.lean` contains computable
label-only fixtures for:

- empty;
- `A A B B C C`;
- `A A A B B B C C C`;
- `A A B C`; and
- duplicate `A A` ports.

The audit checks conservation, nonconservation, label counts, the even/odd
dichotomy, and the count-sum theorem without constructing any
`BoundaryContact` for those flow fixtures. A separate contact-based
`A A B B C C` signature verifies label, sum, conservation, and count
compatibility after erasure.

## Computability and axiom audit

The production and audit sources contain no `sorry`, `admit`, `unsafe`,
`noncomputable`, or new project-local `axiom` declaration. All data
definitions and test fixtures are computable. The focused `#print axioms`
audit reports only the existing foundational dependencies (`propext`,
`Quot.sound`, and `Classical.choice` through finite-set infrastructure).

## Validation

Focused builds completed successfully:

```text
lake build DkMath.Tromino.BoundarySignature
lake build DkMath.Tromino.FlowSignature
lake build DkMathTest.Tromino.FlowSignatureAxiomAudit
```

The FlowSignature audit completed successfully at 1495 jobs. The regression
stack remains contact-based and was not migrated; the existing
`PieceExchange` unnecessary-`simpa` linter notice is unchanged.

## Recommended migration boundary

The next reviewed migration can generalize pairing and transition APIs over a
label-only signature, retaining compatibility adapters from
`BoundarySignature`. That migration should be separate from this checkpoint:

```text
FlowSignature
  -> generic same-label pairing
  -> generic transition network
  -> primitive-cycle zero-holonomy
  -> later state reconstruction
```

TRM-015 itself stops before that migration and before any reconstruction
theorem.
