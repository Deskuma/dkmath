# ZDI-008 — positive-density bounded-span projection feasibility audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0012-ZDI-006-P2F-coercivity-cancellation-feasibility-audit-report.md`
- `0014-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-report.md`

## Goal

Audit the one remaining live moving-frame possibility after ZDI-007:

> Although positive-density blocks cannot have frame span tending to zero, can one choose a strictly positive density small enough that the limiting phase span stays inside a fixed safe angle, so that all pair contributions in a late block retain one common scalar projection sign and produce a block lower bound strong enough to beat the residual-tail upper bound?

This is a **feasibility / obstruction audit**, not an instruction to prove the Riemann Hypothesis and not an instruction to package the missing step as a provider.

Do not begin a long theorem chain. First determine whether the exact existing formulas admit any jointly realizable density/angle/constant region.

## Global RH boundary

The final target remains Mathlib `RiemannHypothesis`.

The already audited CFBRC algebra proves that the CFBRC zero locus lies on the critical line. The unresolved mathematical content remains the source-recovery / zero-forcing direction from a standard nontrivial Riemann-zeta zero to that zero locus.

Any theorem that excludes every off-critical `NontrivialRiemannZetaZero` is therefore RH-closing. Such a theorem is allowed only if its proof contains the genuine independent mathematics. Do not introduce an assumed structure field or newly named predicate whose content is already the desired global no-cancellation conclusion.

In particular, do not add abstract assumptions named like:

```text
GlobalLowerBound
NoCancellation
Coercive
Dominated
PositiveEnergy
BoundedSpanDominated
```

unless they are merely characterized names for facts already independently proved in the same dependency chain. Never count a newly packaged RH-closing hypothesis as a provider.

## Fixed ZDI-007 obstruction

Preserve the exact scope of ZDI-007.

The repository now proves that a positive-density schedule cannot also satisfy the existing `EtaPairGrowingBlockSchedule` relative-length-to-zero contract. In particular, for a positive-density schedule `S`, the same block length cannot satisfy both

```text
(S.blockLength K : ℝ) / etaPairFrameLeftEndpoint K -> S.density
```

with `0 < S.density`, and

```text
(S.blockLength K : ℝ) / etaPairFrameLeftEndpoint K -> 0.
```

The canonical `N(K)=K` schedule has density `1/2`, so it is incompatible with the old sublinear growing-block geometry.

ZDI-007 also proves the exact positive-density block-span limit

```lean
|s.im| * Real.log (1 + 2 * S.density).
```

Therefore a positive-density block generally does **not** have span tending to zero.

This closes the old shrinking-span / frozen-frame argument at positive density. It does **not** prove that the exact Eta tail can never be dominated by the exact finite block, and it does not rule out a bounded but nonzero phase span.

## Exact positive-density rotation facts to reuse

Start from the existing theorems rather than reconstructing their limits.

Audit and reuse at least:

```lean
EtaPairPositiveDensityBlockSchedule.leftEndpointRatio_tendsto_one_add_two_mul_density
EtaPairPositiveDensityBlockSchedule.scheduledBlockPhase_tendsto
EtaPairPositiveDensityBlockSchedule.scheduledBlockRotation_tendsto
EtaPairPositiveDensityBlockSchedule.blockSpan_tendsto
EtaPairPositiveDensityBlockSchedule.not_relativeLength_tendsto_zero
EtaPairPositiveDensityBlockSchedule.not_common_blockLength_with_etaPairGrowingBlockSchedule
```

The signed phase limit is

```lean
s.im * Real.log (1 + 2 * S.density),
```

and the absolute span limit is

```lean
|s.im| * Real.log (1 + 2 * S.density).
```

The canonical half-density schedule gives phase limit `s.im * log 2`; do not use it as evidence that every positive density is too large. The live question is whether **small positive density** can keep the limiting span below a safe angular threshold.

## Positive-density schedule realizability

Prefer existing `EtaPairPositiveDensityBlockSchedule` infrastructure.

If the repository already contains realizable schedules with adjustable density, use them and cite their characterization theorems. If it contains only fixed examples such as the half-density schedule, determine the smallest Lean-friendly parameterized construction needed to test densities near zero.

Any new schedule construction must immediately certify:

1. the exact block-length formula;
2. `blockLength K -> ∞` if required by the finite-block/tail interface;
3. the exact relative-length density limit;
4. strict positivity of the density;
5. compatibility with the finite block indexing and endpoint formulas actually used later.

Do not insert a schedule field whose value is chosen only to force the desired inequality.

If a parameterized positive-density schedule is awkward to construct in Lean, documentation-only asymptotic feasibility analysis is acceptable at this stage, provided all conclusions are clearly marked as analytic calculations rather than proved source facts.

## Bounded-span angle audit

For a fixed nonreal `s` and a fixed safe angle `δ`, audit whether one can choose `ρ > 0` such that

```text
|s.im| * log (1 + 2ρ) < δ.
```

A natural first threshold is any `δ` strictly below `π / 2`; a stricter value such as `π / 4` is acceptable if that matches existing sign lemmas more cleanly.

Do not hard-code an arbitrary threshold before inspecting the existing projection/sign theorems. Search the current geometry for the actual angular hypothesis under which a fixed real-linear projection remains positive or negative.

Inspect at least:

- `EtaCriticalMirrorPairedFrameBlockAlignment.lean`;
- `EtaCriticalMirrorPairedFrameGaugeAudit.lean`;
- `EtaCriticalMirrorPairedFrameVariation.lean`;
- `EtaCriticalMirrorDefectPairQuantitativeMargin.lean`;
- `EtaCriticalMirrorDefectPairNormMarginComparison.lean`;
- `EtaCriticalMirrorPairedFrameBlockMarginDomination.lean`;
- `EtaCriticalMirrorPairedFrameFiniteBlockCertificate.lean`;
- `EtaCriticalMirrorPairedFramePositiveDensityRotationLimit.lean`;
- `EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit.lean`.

If the repository already has a `SmallAngleAdmissible`-type notion, inspect its primitive meaning and realizability before using it. A mere named Prop is not evidence.

## Fixed scalar projection requirement

The desired non-cancellation mechanism must be scalar and linear at the finite-sum level.

A legitimate route would have the following shape.

For one fixed block start `K`, choose a single real-linear functional / projection `L_K` determined at the block start. Prove that every pair contribution in the block remains in a common angular cone, so that

```text
L_K (pairContribution (K + j))
```

has one common sign and a quantitative lower bound for every `j < blockLength K`.

Then use exact linearity:

```text
L_K (sum pairContribution) = sum (L_K pairContribution).
```

This is fundamentally different from an invalid inference such as

```text
‖sum z_j‖ small -> sum ‖z_j‖ small.
```

If angular transport yields a loss factor such as `cos δ`, derive it from an exact rotation/projection identity or an existing theorem. Do not insert the factor heuristically.

The functional may depend on the block start `K`; what must remain fixed is the functional **across all terms of that one block**. A pair-by-pair rotating projection does not remove cancellation in the whole finite sum.

## Bounded-span transport versus old shrinking-span geometry

The old growing-block route used relative block length tending to zero so that the entire block frame asymptotically froze.

ZDI-008 asks whether a weaker contract is enough:

```text
late block phase span < δ
```

for one fixed safe `δ`, without requiring the span itself to tend to zero.

Audit exactly which existing lemmas truly require `span -> 0` and which only require an eventual upper bound by a small angle.

Classify any needed replacement theorem as one of:

- already implied by existing exact rotation formulas;
- a small independent trigonometric transport lemma;
- equivalent to the old growing-block assumption in disguise;
- unavailable because the projection frame itself changes in an uncontrolled way.

Do not rebuild the whole moving-frame hierarchy before this distinction is known.

## Positive-density normalized margin constants

The repository already contains exact normalized positive-density block-margin limits. Reuse:

```lean
EtaPairPositiveDensityBlockSchedule.rightNormalizedBlockMarginPowerLowerBound_tendsto
EtaPairPositiveDensityBlockSchedule.leftNormalizedBlockMarginPowerLowerBound_tendsto
```

whose limiting constants have the forms

```text
(s.im^2 / 4) * density * (1 + 2*density)^(s.re - 2)
```

on the right and

```text
(s.im^2 / 4) * density * (1 + 2*density)^(-s.re - 1)
```

on the left.

Trace the exact normalization used for the residual-tail power bound from ZDI-006 and derive the corresponding limiting residual constant on the same scale.

Do not compare unnormalized quantities with different powers of the frame endpoint.

## Joint density/constant feasibility audit

The central question is not merely whether a small density satisfies the angle condition, and not merely whether positive density balances the asymptotic exponents.

Determine whether there exists a single `ρ > 0` satisfying **both**:

1. a common-sign bounded-span condition for the chosen fixed projection;
2. strict constant domination of the residual majorant by the projected block-margin lower bound.

The two requirements may pull in opposite directions:

- decreasing `ρ` reduces the limiting phase span;
- decreasing `ρ` also weakens the block-margin constant approximately linearly in `ρ`.

Compute the exact dependence from current formulas before judging feasibility.

Do the audit separately for

```text
1 / 2 < s.re
```

and

```text
s.re < 1 / 2.
```

Keep `s.im` explicit. Standard nontrivial zeros are not assumed to have bounded imaginary part, so a density choice that silently requires a uniform global bound on `|s.im|` is not a universal RH route.

A density is allowed to depend on the fixed zero `s` only if the downstream argument remains a legitimate proof for each arbitrary nontrivial zero and the schedule construction/provenance remains independent of the desired conclusion `s.re = 1/2`.

## Constant comparison firewall

Do not infer strict domination from matching rates alone.

For the actual residual upper bound `R_K(s)` and projected block lower bound `M_K(s,ρ,δ)`, the desired eventual inequality must follow from explicit constants after common normalization, schematically:

```text
lim normalizedResidual < lim normalizedProjectedMargin.
```

If the current residual estimate is too coarse to obtain strict constant domination, classify that as an obstruction of the **current bound route**, not as impossibility for the exact Eta residual.

If the projected margin loses a factor due to angular transport, include that exact factor in the constant audit.

## Candidate classification

Classify every live route into exactly one of:

- **C0 — closed**: existing trusted theorems already provide bounded-span fixed-projection domination;
- **C1 — conditional old frontier**: works only after an unproved residual-domination/no-cancellation hypothesis;
- **C2 — genuine new candidate**: all angle, schedule, projection, and constant hypotheses are independently realizable and the resulting scalar rigidity is not a renamed RH step;
- **O-ANGLE**: positive density cannot satisfy the required fixed-projection angle condition;
- **O-CONSTANT**: bounded-angle projection is possible, but the current explicit constants cannot dominate the residual majorant;
- **O-JOINT**: angle admissibility and constant domination are separately plausible but no common density region exists;
- **O-ROUTE**: the current majorant/lower-bound machinery is too weak, without claiming impossibility for the exact Eta tail;
- **E — RH-equivalent frontier**: the proposed statement directly supplies the missing off-critical exclusion with no independent proof;
- **F — untrusted**: depends on `sorryAx`, an unsupported semantic identification, or another excluded provider.

Do not promote C1 to C2.

## Small Lean additions allowed

Small audit theorems are encouraged if they settle feasibility cleanly, for example:

- an explicit adjustable positive-density schedule and its density-limit theorem;
- an eventual bounded-span theorem from the exact span limit;
- a fixed-projection cone lemma derived from exact rotation identities;
- an explicit incompatibility theorem between angle admissibility and residual/margin constant domination;
- an exact theorem characterizing the feasible density interval.

Do not implement a long RH proof chain in ZDI-008.

Every new load-bearing `def` must satisfy the definition-certification rules: primitive characterization, realizability, provenance, RH-equivalence audit, and a negative/impossibility test where useful.

## Required report

Create:

`0016-ZDI-008-positive-density-bounded-span-projection-feasibility-audit-report.md`

The report must contain:

1. exact source inventory for positive-density phase/span limits;
2. positive-density schedule realizability status;
3. fixed block-start projection / scalar-linearity audit;
4. exact angular condition needed for common sign;
5. existence or nonexistence of small positive densities satisfying that condition;
6. right-side normalized residual and margin constants;
7. left-side normalized residual and margin constants;
8. joint angle-versus-constant feasible region, if any;
9. classification table using C0/C1/C2/O-ANGLE/O-CONSTANT/O-JOINT/O-ROUTE/E/F;
10. the smallest exact mathematical inequality or transport lemma still missing;
11. a recommendation for ZDI-009.

If no fixed scalar projection survives bounded positive span, say so explicitly and recommend closing the moving-frame branch rather than inventing another provider.

If a genuine jointly feasible C2 region survives, ZDI-009 may implement only that narrow route.

## Stop conditions

Stop and report rather than extending the theorem chain if:

- the only common-sign statement uses a pair-by-pair rotating functional;
- the bounded-span condition requires an unproved provider;
- a positive density can satisfy the angle bound but no current explicit constant can beat the residual majorant;
- constant domination requires a density that violates the angular condition;
- a uniform density would require an unavailable global bound on `|s.im|`;
- a new predicate merely renames exact residual domination or off-critical exclusion;
- the only remaining assertion is already RH-equivalent by construction.

A negative result is valuable. The purpose of ZDI-008 is to decide whether positive-density bounded-span transport is a genuine escape from the ZDI-007 schedule obstruction or merely another form of the same global cancellation frontier.

## Verification

For every changed Lean module, run the narrowest relevant `./lean-build.sh` target.

Run `#print axioms` on every theorem promoted to C0/C2 or obstruction status and reject any `sorryAx` dependency.

Run:

```text
git diff --check
```

Do not add `sorry`.

## Completion condition

ZDI-008 is complete when the repository has a mechanically grounded answer to this single question:

> Can a strictly positive-density Eta pair block retain one common fixed scalar projection sign over a bounded nonzero phase span **and simultaneously** have an explicit projected margin constant that dominates the current residual-tail bound?

Only a jointly realizable C2 answer should lead to an implementation route. Otherwise record the precise obstruction and close or redirect the moving-frame branch.