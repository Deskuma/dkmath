# IPSM-049 — CS25 closeout and CS26 interaction phase-boundary closed-form audit

## Status

CS25 verdict: **Green-B**.

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`.

The implementation in `PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit.lean` is accepted as the source of truth.

## CS25 facts now fixed

The normalized finite ray state is the finite prime-power ray amplitude itself. For each prime ray, the CS17 plus/minus densities are exactly the two shifted norm-square surfaces

`PlusDensity = normSq (Z + 1)` and `MinusDensity = normSq (Z - 1)`.

Define the pointwise common carrier and interaction by

`CommonDensity Z := normSq Z + 1`

and

`InteractionDensity Z := 2 * Z.re`.

Then the ordinary complex identities are exact:

`PlusDensity = CommonDensity + InteractionDensity`

and

`MinusDensity = CommonDensity - InteractionDensity`.

The common carrier is nonnegative, but no sign is asserted for the interaction.

After interval integration and prime weighting, the same decomposition survives exactly at ray and aggregate level. In particular,

`AggregateInteraction = 2 * FiniteModeSum`.

Together with the CS24 normalization,

`NormalizedPrimeContribution = AggregateInteraction / π`.

Writing `CorrectionSource` for the cutoff-independent sum of the archimedean, elementary, and top-horizontal normalized real contributions, the complete finite source is therefore

`CompleteSource = CorrectionSource + AggregateInteraction / π`.

The finite radial-contact deficit consequently collapses to the interaction-only identity

`G(ε,W,X) = G(ε,W,0) - AggregateInteraction(ε,W,X)`.

Hence finite radial contact is exactly interaction reach:

`G(ε,W,X) ≤ η ↔ G(ε,W,0) - η ≤ AggregateInteraction(ε,W,X)`.

CS24's canonical positive-mass decomposition is compatible with this identity, but its common carrier cancels completely between the mass and the remainder. The pure-real countermodel in CS25 correctly shows that canonical remainder smallness is stronger than direct radial contact and is not a necessary condition.

The remaining frontier is therefore not an energy-ordering theorem and not a common-carrier estimate. It is an independent lower-reach theorem for the signed aggregate interaction.

Named gap retained:

`PascalCenteredXiPrimeSideAggregateInteractionReachGap.noIndependentCofinalInteractionReachProvider`.

No interaction sign, infinite exchange, endpoint sign, or RH conclusion is supplied.

---

# CS26 objective

Do **not** introduce another predicate equivalent to interaction reach and count that as progress.

The next useful step is to expose the signed aggregate interaction as a finite explicit phase-boundary ledger. This returns to the unfinished CS13 nonzero-frequency primitive, which is now directly relevant because CS25 proves that the interaction is the only cutoff-dependent term in the radial-contact deficit.

Target module name:

`DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit`

A nearby descriptive name is acceptable, but keep the module RH-side and finite.

## CS26-A — close the CS13 nonzero-frequency primitive

For real `a r T` with `r ≠ 0`, prove the exact closed form for the existing primitive

`pascalCenteredXiPrimeSidePhasePrimitive a r T`.

The intended mathematical identity is

`J(a,r,T) = exp(a*r) * (T*cos(r*T)/r + (a*r - 1)*sin(r*T)/r^2)`.

This must be proved from the existing integral definition, not introduced as a replacement definition.

Keep the already-proved zero-frequency theorem

`J(a,0,T) = a*T`.

Prefer also a total piecewise closed form that uses the zero-frequency branch at `r = 0` and prove exact equality with the integral-defined primitive.

This is a calculation theorem only. It is not a sign provider.

## CS26-B — identify the two mode frequencies

Let the centered right-edge real coordinate be

`a := W.rectangle.σ - 1/2`.

For a positive natural mode `n`, expose the two real frequencies already implicit in CS13:

`rPlus := ε - log n`

and

`rMinus := -ε - log n`.

Using `pascalCenteredXiPrimeSideModePhaseTransport` and `real_part_affine_exp_phase`, prove an exact formula expressing the finite mode kernel through the two phase primitives.

The expected shape is a positive real normalization depending on `n` and `ε`, multiplied by

`J(a,rPlus,T) - J(a,rMinus,T)`.

Do not hard-code a guessed cast/rpow normalization if the existing `Complex.cpow` transport yields a cleaner exact statement. The theorem should follow the repository's current normalization rather than forcing a prettier but harder representation.

## CS26-C — safe small-ε regime

The eventual RH limit uses `ε → 0+`. Record a convenient local regime such as

`0 < ε < log 2`.

For every mode with `2 ≤ n`, this gives

`rPlus < 0`, `rMinus < 0`, and in particular both frequencies are nonzero.

Modes `n = 0` and `n = 1` must be handled from the actual von-Mangoldt source; do not silently discard them. If their coefficients vanish by existing theorems/simp facts, prove that explicitly in the finite ledger.

The purpose of this gate is to remove the piecewise `r = 0` branch from all genuinely arithmetic modes near the `ε → 0+` limit.

## CS26-D — finite aggregate interaction boundary ledger

Use the already-proved CS25 identity

`AggregateInteraction = 2 * Σ Λ(n) * FiniteModeKernel(n)`

and the new mode closed form to obtain an exact **finite** boundary-phase expansion of `AggregateInteraction`.

All sums remain over `Finset.range (X + 1)` or an already-existing finite prime/prime-power support.

No infinite sum/integral exchange is allowed.

The resulting expression should make visible, mode by mode, the two frequencies

`ε - log n` and `-ε - log n`

and their `T`-boundary trigonometric terms.

## CS26-E — isolate the top-boundary ledger

The closed form contains terms proportional to the upper endpoint `T`, together with sine boundary terms. Separate these into named finite ledgers rather than immediately attempting a sign argument.

Audit whether any of these `T`-boundary terms matches, cancels, or combines exactly with the already-existing top-horizontal correction contained in

`pascalCenteredXiPrimeSideIndependentCorrectionSourceReal`.

Three acceptable outcomes:

1. **Exact cancellation / exact recombination found.** Prove it and expose the smaller source object.
2. **Only a partial algebraic match exists.** Record the exact common part and a named residual.
3. **No source-level identification is currently derivable.** State that boundary matching remains a named gap; do not manufacture a provider.

A failed cancellation audit is still a valid Green-B result if the exact phase-boundary ledger is new and source-derived.

## CS26-F — interaction reach must remain independent

Even after obtaining the explicit boundary ledger, do not infer

`0 ≤ AggregateInteraction`,

`G(ε,W,0) ≤ AggregateInteraction`,

cofinal radial contact,

endpoint nonpositivity,

or RH

unless a genuinely independent source estimate is proved.

The oscillatory sine/cosine boundary expression is expected to remain signed.

If the closed form merely rewrites the interaction without improving its order properties, preserve the existing interaction-reach gap.

## Why this is the correct next step

CS10–CS25 progressively removed stronger and artificial provider surfaces:

`tail sign → mode sign → ray ordering → aggregate ordering → cutoff monotonicity → terminal ceiling → good cutoff → radial contact → abstract signed mass → canonical positive mass → common-carrier cancellation`.

After CS25, the cutoff-dependent radial mechanism is reduced to one scalar signed object:

`AggregateInteraction`.

The repository already contains the exact finite phase transport needed to expose this object, but CS13 intentionally stopped before the nonzero-frequency primitive was evaluated. Closing that gap is therefore not another logical adapter: it changes the arithmetic interaction from an interval-integral object into a finite boundary-phase object that can be compared directly with the finite contour correction ledger.

This is the first preferred route before introducing any new abstract interaction provider.

## Firewall

- finite cutoffs only;
- finite rectangle height only;
- no infinite prime series inside the interval integral;
- no exchange of `X → ∞`, `ε → 0+`, or `T → ∞`;
- no zero-side fixed-defect nonnegativity as a sign provider;
- no assumption equivalent to the desired interaction reach hidden in a structure field;
- no CF2D collision theorem as a substitute for the missing source estimate;
- no RH conclusion.

## Expected CS26 verdict

**Green-B** if the nonzero-frequency primitive and finite aggregate boundary-phase ledger are proved exactly while the interaction-reach estimate remains named and open.

A stronger verdict requires a genuinely source-derived cancellation or inequality that reduces the interaction-reach frontier rather than merely renaming it.
