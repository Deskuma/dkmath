# PCK-002G implementation report

## Outcome

PCK-002G is implemented in the preferred generic Cosmic Formula owner.
The module freezes the square-Gnomon vocabulary and proves the requested
degree-two GN/GTail, square-growth, fixed-Gap Body/Big, kernel-growth, area
growth, and scaling identities.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
423e996be (docs(PCK): insert PCK-002G square Gnomon checkpoint).
The worktree was clean at the start.

## Changed files

- DkMath/CosmicFormula/SquareGnomon.lean
  - Added the new canonical owner and theorem surface.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-004.md
  - Added this implementation report.

PCK-002 SquareBody, PCK-001 HalfUnitZeroConjugate, public aggregators, and
all later prime, primorial, RH, PHZ, zeta, Xi, and CFBRC routes are unchanged.

## Owner and imports

The exact owner is DkMath.CosmicFormula.SquareGnomon in
DkMath/CosmicFormula/SquareGnomon.lean.

The imports are:

    import Mathlib
    import DkMath.CosmicFormula.CosmicFormulaBinom

The module uses CommSemiring as its algebraic assumption. It does not import
DkMath.Collatz.GnomonEvaluation, DkMath.CosmicFormula.CoreBeamGap, or any
analytic or number-theoretic route.

## Definition and theorem surface

The thin abbrev surface is:

    abbrev squareGnomonKernel (x u : R) : R :=
      DkMath.CosmicFormula.GN R u x 2

    abbrev squareGnomon (x u : R) : R :=
      u * squareGnomonKernel x u

The exact GN/GTail bridge is:

    theorem squareGnomonKernel_eq_GTail (x u : R) :
        squareGnomonKernel x u =
          DkMath.CosmicFormula.GTail 2 1 u x

It is proved by rfl, so the new kernel is an orientation-specific view of
the canonical GN definition rather than a second GN alias.

The kernel normal form reuses the existing
DkMath.CosmicFormula.GTail_one_eq_sum expansion. The fixed-Gap Body proof
uses DkMath.CosmicFormulaBinom.GN_eq_sum for the two legacy Body kernels and
the new kernel normal form for the Gnomon term. The Big proof reuses
DkMath.CosmicFormulaBinom.cosmic_id_csr and then rewrites the Body by the
fixed-Gap step theorem below.

The explicit normal forms are:

    squareGnomonKernel x u = 2 * x + u
    squareGnomon x u = u * (2 * x + u)

The core-to-next-square identity is:

    x ^ 2 + squareGnomon x u = (x + u) ^ 2

The fixed-Gap Body step is correctly indexed at the new anchor:

    BodyN 2 (x + u) u =
      BodyN 2 x u + squareGnomon (x + u) u

The Big step reuses the existing Cosmic decomposition and keeps the same
GapN 2 u:

    BigN 2 (x + u) u =
      (BodyN 2 x u + squareGnomon (x + u) u) + GapN 2 u

Thus the Gnomon is Body growth with Gap preserved, not Gap growth. In the
unit case, Body advances by 3, 5, 7, ... while fixed Gap 1 gives Big values
1, 4, 9, 16, ...

The kernel and area growth laws are:

    squareGnomonKernel (x + u) u =
      squareGnomonKernel x u + 2 * u

    squareGnomon (x + u) u =
      squareGnomon x u + 2 * u ^ 2

The raw-coordinate scaling theorem is also implemented:

    squareGnomon (k * x) (k * u) = k ^ 2 * squareGnomon x u

This scaling law is recorded as raw coordinate scaling only. It does not
assert raw GapN invariance.

## Collatz and promotion audit

The existing Collatz owner was inspected. It already owns OddGnomonLayer
and square_add_eq_square_add_gnomon_sum. They were not duplicated or moved.
The dependency direction remains from a later Collatz bridge toward this
generic algebraic owner, not from this Cosmic Formula module into Collatz.

The file is documented as a future candidate for promotion or refactoring
into a DkMath.Lib.Gnomon-style owner after the API stabilizes. No promotion
was performed.

## Resolution-refinement frontier

The module docstring records the future coarse-to-fine telescoping surface:
fine anchors x + (j / k) * u preserve the endpoint transition after
telescoping, while integer visualization scales coordinates by k and
normalization divides square values by k^2.

The examples 1 to 4 at endpoint scale k = 3 and 4 to 9 at endpoint scale
k = 3 are recorded, including their resolved chains. The raw-coordinate
firewall is explicit: (k*u)^2 = k^2*u^2, so raw fine Gap cells must not be
claimed to add directly to the coarse u^2 Gap.

No resolution-refinement theorem family was implemented in this checkpoint.

## Verification

The required focused build passed:

    lake build DkMath.CosmicFormula.SquareGnomon

Result: DkMath.CosmicFormula.SquareGnomon built successfully after 8666
jobs, with no Lean linter warnings in the final build.

git diff --check passed.

The axiom checks were run for the GN/GTail bridge, the Core-to-next-square
identity, the fixed-Gap Body theorem, the kernel-growth theorem, and the
area-growth theorem. Each reported only ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

No project-specific axiom was introduced. The source audit found no newly
introduced sorry, admit, native_decide, or axiom. The only firewall-topic
matches are explanatory documentation stating that those dependencies are
not imported or implemented.

No helper theorem or auxiliary structure was added beyond the two requested
abbrev definitions. No PCK-002G downstream adapter was added.

## Boundary and next authorization

PCK-002G is green at the square-Gnomon algebra boundary. It does not
implement PCK-003 coarse-to-fine square certification, a generic Gnomon
library promotion, a continuous primality notion, or any prime/analytic
consequence.

The next authorized checkpoint is PCK-003: the first thin coarse-to-fine
square certification adapter. PCK-003 is not implemented in this report.
