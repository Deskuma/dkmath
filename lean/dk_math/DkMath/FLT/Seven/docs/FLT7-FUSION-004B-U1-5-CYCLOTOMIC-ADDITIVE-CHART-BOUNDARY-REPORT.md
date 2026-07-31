# FLT7-FUSION-004B U1.5 cyclotomic additive-chart boundary report

Date: 2026-07-30

Execution mode: ULTRA

Active phase: U1

Event: U1.5

Starting commit: `de1848ee`

Ending commit: this U1.5 Event commit

## Completed Lean facts

The concrete degree-six carrier now has an explicit integral norm

```text
SevenCyclotomicDegreeSixInt.cyclotomicNormHom :
  SevenCyclotomicDegreeSixInt.Ring →* ℤ.
```

It is obtained by composing the relative quadratic norm with the integral
norm of the real cubic order.  Lean proves:

```text
cyclotomicNormHom ramifiedUniformizer = 7
cyclotomicNormHom (star x) = cyclotomicNormHom x
cyclotomicNormHom (rotateEquiv x) = cyclotomicNormHom x.
```

The product of the three quadratic-conjugate pairs, hence of all six Galois
phases, is not a new additive expression.  It is exactly the embedded
integral norm:

```text
sixPhaseProduct x = ofReal (cyclotomicNormHom x).
```

For the actual oriented carrier, this specializes to:

```text
cyclotomicNormHom cyclotomicDegreeSixCarrier
  = 7 * quotientRoot

sixPhaseProduct cyclotomicDegreeSixCarrier
  = ofReal (7 * quotientRoot).
```

The six integral coordinates of the carrier are also exact:

```text
coordinates cyclotomicDegreeSixCarrier
  = [signedRightRoot, 0, 0, -signedLeftRoot, 0, 0].
```

Consequently the U1.4 equation

```text
cyclotomicDegreeSixCarrier
  = orientedLoadElement * orientedResidualRoot^7
```

gives precisely:

```text
coordinates (orientedLoadElement * orientedResidualRoot^7)
  = [signedRightRoot, 0, 0, -signedLeftRoot, 0, 0]

7 * quotientRoot
  = cyclotomicNormHom orientedLoadElement
      * cyclotomicNormHom orientedResidualRoot^7.
```

These facts are combined with the existing direct-chart obstruction in:

```text
orientedElementLevelPower_additiveBoundary.
```

That theorem simultaneously records the coordinate ledger, norm ledger, and:

```text
¬ ∃ c : ℤ,
  SignedFermatSevenChart
    signedRightRoot (-signedLeftRoot) c.
```

The obvious projection shortcuts are excluded concretely.  The zeroth
integral coordinate is not multiplicative:

```text
zerothCoordinate_not_multiplicative.
```

There is also no unital ring homomorphism:

```text
no_ringHom_to_int :
  ¬ Nonempty
    (SevenCyclotomicDegreeSixInt.Ring →+* ℤ).
```

Finally, Lean proves a stronger non-canonicity boundary for the actual chosen
residual root.  The root is nonzero, and multiplication by the primitive
seventh root changes it:

```text
zeta * orientedResidualRoot ≠ orientedResidualRoot.
```

Nevertheless:

```text
span {zeta * orientedResidualRoot}
  = globalOrientedResidualIdeal

cyclotomicDegreeSixCarrier
  = orientedLoadElement * (zeta * orientedResidualRoot)^7

coordinates (zeta * orientedResidualRoot)
  ≠ coordinates orientedResidualRoot.
```

This exact `mu_7` gauge boundary is bundled as:

```text
orientedResidualRoot_muSevenGaugeBoundary.
```

## New module

```text
SevenRamifiedFusionCyclotomicAdditiveChartBoundary.lean
```

The module is imported by the public `DkMath.FLT.Seven` facade.

## Mathematical interpretation

U1.5 does not produce a primitive additive Fermat chart.  It proves why the
three immediate operations on the U1.4 element equation are insufficient:

1. multiplying all six Galois phases retains only the integral norm;
2. extracting additive coordinates does not commute with multiplication or
   seventh powers;
3. the residual generator itself is determined only up to a nontrivial
   `mu_7` action, and this action changes all-coordinate data while preserving
   the ideal, seventh power, load element, and carrier equation.

The visible endpoint candidate is not merely noncanonical; it is impossible,
because its seventh-power difference has exact seven-adic depth five.

Thus U1.4 provides genuine element-level multiplicative data, but that data
does not determine three integers satisfying an additive seventh-power
equation.

## Exact remaining obligation

A future additive reconstruction must supply one of:

- a `mu_7`-invariant extraction from the residual-root orbit to three
  integers; or
- a theorem choosing and proving a canonical phase normalization.

That construction must additionally prove, independently of the norm
identity:

```text
SignedFermatSevenChart a b c
```

for new integer coordinates, including the exact additive equation,
nonvanishing, primitivity, a signed normalization yielding the required
positive natural data, and provenance from the original terminal packet.

No such extractor, phase normalization, or additive compatibility theorem is
currently present.  Since U1.5 produces no primitive chart, U1.6 cannot infer
a strict descent measure from the current element witnesses.  Its sound task
is to formalize that exact strict-decrease failure boundary.

This Event does not claim:

- that the loaded element is a seventh power;
- that a coordinate of a product is the product of its coordinates;
- that the integral norm is an additive chart;
- a primitive reconstructed counterexample;
- a strict drop, descent closure, terminal contradiction, or FLT7.

## Build verification

The focused module build and the public facade build succeeded.  The new
module contains no `sorry`, `admit`, explicit `axiom`, or `native_decide`.
Printed axiom dependencies are limited to the standard `propext`,
`Classical.choice`, and `Quot.sound`.

## Outcome

Outcome C: the exact additive compatibility missing from U1.4 is isolated,
with formal obstruction theorems excluding the norm, coordinate-projection,
visible-endpoint, and unnormalized residual-coordinate shortcuts.

Next selected Event:

```text
ULTRA / U1.6 — strict decrease candidate or exact failure boundary
```
