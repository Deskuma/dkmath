# TRM-014 report: closed-orbit XOR obstruction / primitive cycle compatibility

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-014 adds the closed-orbit XOR layer above TRM-013. It remains entirely
within the finite abstract network model. It does not add open residual paths,
ghost completion, arbitrary path independence, planar or noncrossing
constraints, physical boundary extraction, `BoundaryIR`, optimization, or
Four Color claims.

## Transition-XOR convention

Production is `DkMath/Tromino/TransitionXor.lean`.
`transitionXor N p n` is the finite sum over `j < n` of the label at
`(transitionStep N)^[j] p`. Consequently, `j = 0` contributes the starting
label, `n` steps contribute `n` labels, and the local mate contributes no
additional state difference.

The main reduction is:

```text
transitionXor N p n = n • boundaryDelta (N.signature p.1) p.2
```

It uses the existing iterate label-preservation theorem and does not split
the argument into separate A/B/C cases.

## Characteristic-two parity

The reusable theorem `nsmul_state_eq_mod_two` computes repeated addition in
the Tromino four-state carrier. `nsmul_state_eq_zero_iff` then proves:

```text
n • delta = 0 ↔ delta = 0 ∨ n % 2 = 0
```

Since every proper boundary signature has a nonzero boundary delta,
`transitionXor_nonzero_iff_even` gives zero accumulated XOR exactly for even
lengths.

## Primitive return representation

`TransitionReturn` records a positive return, while
`PrimitiveTransitionReturn` adds the strict absence of every smaller positive
return. `firstTransitionReturn` uses `Nat.find` over the existing positive
period certificate from `transitionStep_periodic`; its specification and
minimality prove `exists_primitiveTransitionReturn`.

This keeps the solver-facing transition and XOR definitions computable. Only
the existence proof uses minimality through `Nat.find`; no noncomputable
production data definition is introduced.

`PrimitiveCycleCompatible` packages a primitive return together with zero
cycle XOR. The central theorem is:

```text
PrimitiveTransitionReturn N p n
  -> (transitionXor N p n = 0 ↔ n % 2 = 0)
```

and the corresponding compatibility predicate is equivalent to even
primitive length.

## Prefix transport

`transportState base N p n := base + transitionXor N p n` is executable. The
module proves zero-step initialization, concatenation of prefix lengths, and
the return observer:

```text
transportState base N p n = base ↔ transitionXor N p n = 0
```

for a positive return. On a primitive return this is equivalent to even
period length. No global coloring or arbitrary-path transport is defined.

## Kernel-checked calibrations and counterexample

`DkMathTest/Tromino/TransitionXorAxiomAudit.lean` contains two explicit
finite fixtures. Each region has signature `A A` and an explicit canonical
A-A swap pairing.

- The two-region fixture has a primitive period `2` and zero cycle XOR. Its
  transport returns to the base state.
- The three-region fixture uses the symmetric cross-pairs
  `a1--b0`, `b1--c0`, and `c1--a0`. The alternating graph is a six-cycle,
  and `transitionStep` has the primitive orbit
  `a0 -> c0 -> b0 -> a0`. The audit proves the first and second iterates do
  not return, the third iterate does return, and
  `transitionXor p 3 = deltaA ≠ 0`. Its transport therefore does not return
  to the base state.

The audit separately checks port cardinalities, involutive crossings, region
change, label preservation, local perfectness, and both primitive-cycle
compatibility outcomes.

## Research conclusion and interpretation boundary

Within the current abstract closed-network model, local conservation and
same-label perfect pairing determine a finite degree-two transition system,
but they do not eliminate global holonomy. For a primitive closed orbit with
nonzero preserved label:

```text
even primitive length ↔ zero accumulated XOR ↔ compatible return transport
odd primitive length  ↔ nonzero accumulated XOR ↔ obstructed return transport
```

This is not a claim that planar geometry permits every abstract odd orbit.
Planarity and noncrossing constraints have not yet been formalized and may
exclude some abstract counterexamples.

## Computability and axiom audit

The production and audit sources contain no `sorry`, `admit`, `unsafe`,
`noncomputable`, or new project-local `axiom` declaration. The focused
`#print axioms` output reports only the existing foundational dependencies
(`propext`, `Quot.sound`, and `Classical.choice` through finite ordered-set
infrastructure).

## Validation

Focused builds completed successfully:

```text
lake build DkMath.Tromino.TransitionGraph
lake build DkMath.Tromino.TransitionXor
lake build DkMathTest.Tromino.TransitionXorAxiomAudit
```

The final audit build completed successfully at 1499 jobs. The only emitted
messages are existing or audit-side linter notices; no proof failure remains.
`git diff --check` and new-file whitespace checks are part of the final
closeout.

## Stop boundary

TRM-014 stops once the primitive closed-orbit obstruction is kernel-checked
and the explicit period-3 counterexample is present. Open paths, ghost
completion, planar/noncrossing structure, physical extraction, global path
independence, optimization, and Four Color claims remain deferred.
