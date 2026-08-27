# IPSM-062 — CS38 Core–Beam–Gap completion lens amendment

## 0. Purpose

This note does not create a new proof branch. It amends the current CS38 audit in IPSM-061 with a structural lens that already exists in the general DkMath Cosmic Formula library.

The immediate question is no longer only whether the mirror-weighted source ledger cancels against the finite rectangle background. Before asking for cancellation, CS38 must determine whether the surviving finite difference is an error/reach deficit or an intrinsic finite-unit completion Gap.

Canonical branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`.

---

## 1. Existing general theorem: Big = Core + Beam + Gap

`DkMath.CosmicFormula.CoreBeamGap` already defines, over a commutative semiring,

- `Core d x := x ^ d`,
- `Gap d δ := δ ^ d`,
- `Beam d x δ` as the sum of all non-endpoint binomial terms,
- `Big d x δ := BigN d x δ`.

It proves, for positive degree,

`BodyN d x δ = Core d x + Beam d x δ`,

`Big d x δ = BodyN d x δ + Gap d δ`,

and therefore

`Big d x δ = Core d x + Beam d x δ + Gap d δ`.

`DkMath.CosmicFormula.CosmicFormulaBinom` also proves the subtraction form

`Big d x δ - Body d x δ = Gap d δ`.

For `d = 2`, this is exactly

`(x + δ)^2 = x^2 + 2*x*δ + δ^2`.

The notation `δ` is used in this document intentionally. The RH top-edge coordinate is already named `u`; they must not be conflated.

---

## 2. Interpretation firewall

The following is an audit hypothesis, not yet an RH theorem:

- Big: the completed quantity that exists before the finite mathematical cut;
- Gap: the finite unit marker / completion term;
- Body: the quantity obtained after removing the Gap and on which the finite arithmetic/analytic calculation is performed;
- Core + Beam: the internal decomposition of Body.

The conceptual form is

`Big = Body + Gap`,

`Body = Core + Beam`.

For the quadratic kernel,

`Gap = δ^2 >= 0`.

Do not identify any existing RH object with Big, Body, Core, Beam, or Gap merely because the algebraic shape is suggestive. Every identification must be an exact Lean bridge from existing source definitions.

In particular, do not silently identify:

- the top coordinate `u` with the finite unit `δ`;
- the Mellin smoothing width `ε` with `δ`;
- the prime cutoff `X` with a scale reciprocal to `δ`;
- the radial-contact deficit with `δ^2`;
- the zero-side fixed defect with the required prime-side Gap provider.

These are candidates for audit only.

---

## 3. New structural warning about the current finite reach target

The current CS30 reach classification has the exact shape

`FiniteRadialContactDeficit = π * (RectangleBackground - TopZetaMismatchScalar)`.

Hence finite contact is classified by

`FiniteRadialContactDeficit <= 0`

iff

`RectangleBackground <= TopZetaMismatchScalar`.

Up to CS37 this has been treated as the finite reach frontier.

The Core–Beam–Gap lens exposes a second possibility that must now be tested.

If an exact source bridge eventually shows that the relevant finite difference is a completion Gap of the form

`Big - Body = Gap_δ`

with

`0 <= Gap_δ`,

then the natural finite orientation is

`Body <= Big`,

not `Big <= Body`.

In that case, a finite theorem demanding the analogue of `deficit <= 0` would be structurally over-strong. The correct closure mechanism could instead be:

1. prove the exact finite completion identity;
2. prove the finite Gap is nonnegative or otherwise structurally controlled;
3. preserve the Gap throughout the finite mathematics;
4. only afterward study the source-derived limit in which the unit shrinks and the Gap vanishes.

This is only a possibility. CS38 must decide it from the existing RH ledger; it must not assume it.

---

## 4. Red-ribbon interpretation

The useful conceptual distinction is:

- Big supplies existence of the uncut whole;
- Gap supplies the cut / finite unit marker;
- Body is the finite observable obtained after making that cut.

The Gap is therefore not automatically an error term. It can be the marker that makes a discrete mathematical observable possible in the first place.

Analytically shrinking a unit must be distinguished from deleting the unit structure before forming the finite object.

Schematic order:

`Big -> mark by δ -> Body/Gap decomposition -> finite mathematics -> limit of δ`.

Do not replace this by

`Big -> δ := 0 -> finite mathematics`

unless an exact theorem proves the two constructions agree for the observable in question.

---

## 5. CS38 amendment: audit order

Keep the weighted source-recovery tasks of IPSM-061, but insert the following structural audit before attempting a rectangle-background cancellation theorem.

### A. Close the weighted source consistency square

Continue exactly as IPSM-061 specifies:

1. recover completed rate as fixed-Xi plus elementary correction;
2. decompose the paired weighted scalar density;
3. compress the full top residual integral to the oriented half interval;
4. recover fixed-Xi, Gamma, elementary, and finite-PHZ source channels;
5. prove equality with the existing top mismatch ledger.

This remains source-derived finite mathematics.

### B. Name the exact surviving difference

After substitution into the CS30 rectangle identity, do not immediately ask whether the surviving remainder is `<= 0` or whether it cancels.

First obtain the narrowest exact equality possible, schematically

`CompletedWhole = RecoveredBody + SurvivingRemainder`.

The theorem names must use the actual RH quantities, not `Big`/`Body`/`Gap`, until a formal bridge is established.

### C. Test for Core–Beam–Gap shape

Audit whether the surviving remainder has one of these source-derived forms:

1. an explicit square / norm-square;
2. a quadratic endpoint completion;
3. a finite second-difference pure-endpoint term;
4. a known `Gap d δ = δ^d` image under an exact algebra/ring homomorphism;
5. a sum of such terms.

If none occurs, record that the Core–Beam–Gap lens did not identify the remainder and retain the existing reach frontier.

### D. Separate finite completion from limiting closure

If a genuine nonnegative completion Gap is found, do not try to prove it negative.

Instead split the future frontier into two different questions:

- finite completion theorem: `Whole = Body + Gap`;
- limit theorem: the source-derived Gap tends to zero under the relevant analytic limit.

No limit exchange is allowed merely because the Gap has been identified.

---

## 6. Candidate RH locations to inspect, without assuming an identification

The following existing quantities are natural places to test because they already occur as exact finite differences:

- `pascalCenteredXiPrimeSideFiniteRadialContactDeficit`;
- `pascalCenteredXiPrimeSideFiniteRectangleBackground`;
- `pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar`;
- fixed radial second-moment terms;
- finite complement-boundary scalar;
- fixed-Xi top versus finite arithmetic top companion;
- endpoint terms produced by the CS33/CS34 weighted-displacement integration by parts;
- center-normalized mirror amplitude / phase displacements from CS35.

This list is diagnostic only. No candidate is privileged in advance.

The zero-side fixed second-moment defect may be compared for classification, but it remains forbidden as the missing prime-side reach provider.

---

## 7. Special quadratic audit

Because the current conceptual hypothesis is specifically the magic-core structure `x^2`, CS38 should explicitly test whether any exact surviving finite source has a quadratic three-element decomposition

`Core = x^2`,

`Beam = 2*x*δ`,

`Gap = δ^2`.

At a balanced normalization `x + δ = 1`, the equality `x = δ` forces

`x = δ = 1/2`,

and the three primitive quadratic kernels satisfy

`x^2 = x*δ = δ^2 = 1/4`.

This observation is only a structural target. It does not identify the Riemann critical line or prove any zero-location statement.

If an exact RH bridge to this quadratic pattern appears, formalize the bridge in a separate theorem before using any consequence of the `1/2` balance point.

---

## 8. Verdict impact

CS38 remains **Green-B** if it closes weighted source recovery and either:

- finds no Core–Beam–Gap identification, leaving the reach frontier unchanged; or
- identifies an exact finite completion remainder but does not yet close its limiting behavior.

Upgrade beyond Green-B only if an actual existing frontier is removed by source-derived theorems.

A result that merely renames `RectangleBackground - Mismatch` as `Gap` is not progress.

A genuine advance requires at least one of:

- an exact bridge from an existing DkMath `Gap d δ` object;
- a proved square/norm-square completion identity;
- a strictly smaller source remainder after exact algebraic cancellation;
- a source-derived finite completion theorem that changes the correct orientation of the remaining frontier.

---

## 9. Revised central CS38 question

The central question is now two-stage:

1. After exact mirror-weighted source recovery, what is the precise surviving finite difference?
2. Is that difference a missing error/reach term, or is it the intrinsic finite-unit completion Gap required by `Big = Body + Gap`?

Only Lean should decide between those two interpretations.
