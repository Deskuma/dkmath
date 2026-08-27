# ZDSS-004 — dual-tail rate extraction / normalized-mode bridge exploratory instructions

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Parent roadmap: `0000-RH-CFBRC-zero-derived-second-source-roadmap.md`

Depends on:

- `0002-ZDSS-001-zero-derived-source-rank-independence-audit-report.md`
- `0004-ZDSS-003-source-matched-positive-scalar-centered-coercivity-exploration-report.md`
- `ZeroDerivedPrimeCoordinateSourceRankAudit.lean`
- `ZeroDerivedDualEndpointPositiveScalarCoercivityAudit.lean`
- `PrimeMirrorEtaAsymptoticDichotomy.lean`
- normalized Eta-tail / increment APIs already present in `DkMath.RH.CFBRC`

## 0. Route transition

ZDSS-001 established:

```text
INDEPENDENT-SOURCE-FOUND
```

through the two separately zero-controlled finite endpoint sources

```text
A_K(s) := etaPairedPartial K s
B_K(s) := etaPairedPartial K (criticalMirror s).
```

ZDSS-003 then established:

```text
POSITIVE-SCALAR-UPPER-CLOSED
RATE-ASYMMETRY-IDENTIFIED
RH-EQUIVALENT-FRONTIER-IDENTIFIED
NEW-INFORMATION-OBSTRUCTION
```

for the source-matched positive scalar

```text
E_K(s) = ||A_K(s)||^2 + ||B_K(s)||^2.
```

The U-side is therefore no longer the immediate gap:

```text
NontrivialRiemannZetaZero s
  -> separate endpoint tail identities
  -> separate power upper bounds
  -> E_K(s) -> 0.
```

The missing information lies between whole-endpoint/tail control and the mode-level horizontal detector.

This checkpoint must not spend its main effort constructing yet another unnormalized positive scalar from `A_K` and `B_K`. It should investigate whether the **rate information** carried by the zero-derived endpoint tails reaches the already formalized normalized mode Gap.

## 1. Exact mode detector already available

The repository already proves an exact closed form for the normalized endpoint increment Gap.

Schematically, with

```text
delta = centeredSigma s.re,
q = K + 1,
```

the normalized Gap has the form

```text
G_K(s) = q^(2 * delta) + q^(-2 * delta) - 2.
```

The existing dichotomy is:

```text
s.re = 1/2
  -> G_K(s) = 0 for every K,

s.re != 1/2
  -> G_K(s) -> +infinity.
```

The raw amplitude Gap satisfies

```text
rawGap_K(s) -> 0
```

throughout the open strip, while

```text
G_K(s) = (K + 1) * rawGap_K(s).
```

Hence an off-critical point can satisfy simultaneously

```text
rawGap_K(s) -> 0,
G_K(s) -> +infinity.
```

This checkpoint should treat that rate dichotomy as an already solved C-detector, not re-prove it unless a smaller reusable interface is needed.

## 2. Central research question

Investigate the following question without assuming its answer:

> Does the standard nontrivial zeta-zero hypothesis impose enough additional rate information on the two endpoint tails, their finite partials, or their cutoff differences to prevent the normalized mode Gap `G_K(s)` from tending to `+infinity`?

A complete positive answer need not initially prove

```text
G_K(s) -> 0.
```

Any exact zero-derived conclusion incompatible with

```text
G_K(s) -> +infinity
```

may be sufficient to force the critical line.

Examples of potentially sufficient outcomes include, but are not limited to:

```text
1. G_K(s) is eventually bounded;
2. G_K(s) has a cofinal bounded subsequence;
3. liminf G_K(s) < +infinity in a usable formal form;
4. G_K(s) fails to tend to +infinity;
5. a source-derived comparison forces rawGap_K(s) = O(1 / K);
6. a sharper rate forces rawGap_K(s) = o(1 / K);
7. a two-sided endpoint-tail asymptotic excludes the off-critical exponent imbalance.
```

Do not select one of these as a definition of success before inspecting the actual APIs.

## 3. Research discipline: Codex must investigate, compare, and choose

This is deliberately an exploratory research checkpoint.

Codex should not treat this file as a fixed theorem script.

Before implementing the main audit module:

1. inspect the current endpoint-tail, normalized-tail, increment, mirror-Gap, prime-factor, and asymptotic modules;
2. identify exact theorem statements already available, especially their hypotheses and direction of inequalities;
3. write down several candidate rate observables or bridges;
4. determine which candidates are genuinely zero-derived and which are unconditional open-strip identities;
5. compare their information content;
6. select the smallest route that could distinguish `s.re = 1/2` from `s.re != 1/2`;
7. implement exact Lean facts supporting that route;
8. if a chosen route weakens or fails, continue to nearby rate formulations rather than ending the checkpoint immediately.

The report must summarize this reasoning in mathematical terms. It need not reproduce internal scratch reasoning or token-by-token deliberation.

## 4. Mandatory first audit: normalized ordinary Eta tails

ZDSS-001 gives exact zero-derived identities

```text
A_K(s) = -etaPairTail K s,
B_K(s) = -etaPairTail K (criticalMirror s).
```

The repository also contains normalized Eta-tail asymptotic material, including declarations near

```text
etaPairIndexNormalizedRotatedTail_tendsto_constant
```

and related modules.

Audit these APIs first.

Determine exactly:

- what normalization is used;
- whether the theorem is unconditional in the open half-plane or uses a zero hypothesis;
- whether it gives only an upper bound, an actual limit, or an asymptotic equivalence;
- whether the limiting constant can vanish;
- whether the theorem applies separately to `s` and `criticalMirror s`;
- whether the two endpoint limits can be compared without assuming the critical line;
- whether phase rotation loses or preserves the amplitude/rate information needed for `G_K`;
- whether the result survives passage from tails to finite partials using the zero-derived identities.

If the normalized-tail theorem already gives a useful exact two-sided asymptotic, expose the smallest reusable bridge theorem rather than rebuilding it.

If it is unconditional and therefore does not itself encode a zero-specific restriction, determine whether combining it with the simultaneous zero identities at both endpoints creates a new constraint.

## 5. Candidate family A — endpoint tail normalization

Investigate normalizations suggested by the known decay exponents.

Schematic examples include

```text
K^(s.re) * A_K(s)
K^(1 - s.re) * B_K(s)
```

or equivalent rotated/complex-normalized versions already present in the repository.

Questions to test:

- Do these quantities converge?
- Are their limits nonzero?
- Are the two limits related by critical-mirror symmetry?
- Does a nonzero limit provide a lower as well as an upper rate for `||A_K||` or `||B_K||`?
- Can the relative decay exponents be extracted from source identities rather than inserted into a definition?
- Can a ratio or product of the endpoint rates eliminate irrelevant phase while retaining `centeredSigma`?

A normalization depending on `s.re` is not automatically circular: it may be used if it is characterized from the existing source variable and the resulting theorem is unconditional or zero-derived for legitimate reasons. However, merely defining a normalization that algebraically cancels the desired exponent is not proof of centered coercivity.

## 6. Candidate family B — consecutive cutoff differences

The exact identities

```text
A_(K+1) - A_K = one original endpoint mode,
B_(K+1) - B_K = one mirror endpoint mode
```

are essentially unconditional finite-sum identities.

ZDSS-001 already established that cutoff subtraction by itself is not new zero information.

Nevertheless, ZDSS-004 may combine these differences with the **zero-derived tail identities or rate theorems**.

Audit whether the zero hypothesis implies a useful relation between:

```text
A_K,
A_(K+1),
B_K,
B_(K+1),
```

and the individual endpoint modes beyond the tautological finite-difference identity.

Potential observables include:

```text
||A_(K+1) - A_K|| / ||A_K||
||B_(K+1) - B_K|| / ||B_K||

K * (A_(K+1) - A_K)
K * (B_(K+1) - B_K)

K * (||A_(K+1)|| - ||A_K||)
K * (||B_(K+1)|| - ||B_K||)
```

when denominators/nonvanishing are legitimately available.

Do not assume monotonicity or noncancellation of complex tails without proof.

## 7. Candidate family C — multiplicative or sparse cutoff comparison

A rate can sometimes be recovered more robustly from scale changes than from adjacent differences.

Audit comparisons such as

```text
A_(2K) versus A_K
B_(2K) versus B_K
```

or more generally

```text
A_(floor(lambda * K)) versus A_K
B_(floor(lambda * K)) versus B_K
```

for fixed `lambda > 1`, if existing APIs make such comparisons natural.

Possible questions:

- Does a normalized tail have a scale-ratio limit?
- Does the endpoint pair have different scale exponents off critical?
- Can a scale quotient be made phase-insensitive?
- Can a bounded/cofinal statement be proved without establishing a full asymptotic expansion?

Sparse/cofinal cutoffs are allowed if they preserve enough information to contradict the existing `atTop` divergence theorem for `G_K`.

A full statement for every sufficiently large K is not required if a rigorous cofinal subsequence argument suffices.

## 8. Candidate family D — log-slope / exponent extraction

The two endpoint power scales are schematically

```text
K^(-s.re)
K^(-(1 - s.re)).
```

This suggests, but does not prove, slope observables involving logarithms of norms.

Audit whether exact nonzero asymptotics support quantities such as

```text
log ||A_K|| / log K
log ||B_K|| / log K
```

or finite differences of log norms.

This route is admissible only when the required eventual nonvanishing and two-sided asymptotic control are proved.

Upper power bounds alone are insufficient to identify a decay exponent.

Do not use

```text
||A_K|| <= C K^(-sigma)
```

to conclude a matching lower rate or a log-slope limit.

If zeros of the complex tail prevent direct logarithms, investigate whether squared norms, limsup/liminf, or scale ratios avoid the problem.

## 9. Candidate family E — direct normalized-mode bridge

The preferred target is not necessarily an asymptotic formula for the entire tail.

Search for an exact inequality or identity connecting the zero-derived endpoint source data to

```text
etaMirrorAmplitudeGap s K
```

or directly to

```text
etaEndpointIncrementMirrorGap s K.
```

Possible bridge shapes include:

```text
(K + 1) * etaMirrorAmplitudeGap s K <= rateUpper K s
```

with `rateUpper` bounded on zeros, or

```text
etaEndpointIncrementMirrorGap s K <= F(A_K, A_(K+1), B_K, B_(K+1))
```

for a source-controlled right-hand side.

The direction of inequalities matters. Do not reverse triangle, Cauchy-Schwarz, or a previously one-sided tail bound.

If the exact mode Gap can be expressed in terms of norms of endpoint increments, determine whether a valid identity involving finite-tail differences gives a path around whole-sum cancellation.

## 10. Candidate family F — summation-by-parts / Abel / Gram structure

If direct tail-rate extraction is insufficient, inspect whether the actual paired-Eta source has additional structure capable of turning a sequence of whole-tail identities into mode information.

Possible mechanisms to audit include:

```text
summation by parts
Abel transform
finite telescoping identities
exact discrete derivatives
Gram-type identities on the actual Eta mode family
orthogonality already proved in the repository
positive weighted averages
```

This is not authorization to assume generic no-cancellation.

Any positive modewise statement must be derived from the actual Eta source or an existing exact theorem.

Do not import a general inequality in the wrong direction merely because it would produce the desired result.

## 11. A weaker contradiction may be enough

The existing off-critical theorem is strong:

```text
G_K(s) -> +infinity.
```

Therefore ZDSS-004 should explicitly search for **weaker zero-derived anti-divergence statements**, not only for `G_K -> 0`.

Examples:

```text
eventually G_K <= C
```

or

```text
exists a cofinal sequence K_j with G_(K_j) <= C
```

or a theorem implying

```text
not (Tendsto G atTop atTop).
```

Such statements may be significantly easier to derive from tail information than full centered coercivity.

If one is proved, connect it immediately to the existing off-critical divergence theorem and test whether it yields

```text
s.re = 1 / 2.
```

Do not postpone a short exact contradiction merely because the roadmap originally anticipated a stronger quadratic lower bound.

## 12. Distinguish four information levels

For every rate theorem or candidate, classify it as one of:

```text
U0 — unconditional open-strip rate fact
U1 — zero-derived whole-endpoint rate fact
U2 — zero-derived mode/normalized-Gap control
C  — horizontal detector / critical-line consequence
```

The desired new bridge is primarily

```text
U1 -> U2.
```

The repository already has a strong

```text
U2 -> C
```

mechanism through normalized-Gap divergence.

Do not count a new `U0` theorem as RH progress merely because it contains `s.re` in its formula.

Conversely, a theorem may be useful even if it is unconditional when combining **two** unconditional asymptotics with the zero-derived identities produces a genuinely new `U1` or `U2` statement.

## 13. Frontier awareness without prematurely closing exploration

Some statements at this stage will be strong enough that, combined with existing results, they imply `s.re = 1/2`.

That alone is not a reason to reject them.

The correct distinction is:

- if the statement is proved unconditionally or from the legitimate standard-zero hypotheses, it is a valid result even if it closes RH;
- if it is merely postulated, encoded in a definition, or imported through an RH-equivalent provider, it is not an independent source theorem.

In particular, do not assume any of the following merely to advance the proof:

```text
normalized Gap bounded on zeros
normalized Gap tends to zero on zeros
endpoint Gap controls UnitGap
uniform positive centered coercivity
modewise no-cancellation
```

But if one of these can actually be derived from accepted source facts, prove it and follow the consequence as far as Lean allows.

## 14. Exploratory continuation boundaries

The checkpoint should remain open to nearby mathematical reformulations when a candidate weakens or fails.

Do not terminate the entire checkpoint merely because:

- one normalization has zero limiting constant;
- adjacent differences are too weak;
- a direct norm ratio is undefined infinitely often;
- a first attempt only produces `limsup`/`liminf` information;
- the strongest desired `G_K -> 0` theorem is unavailable;
- one historical Gap bridge is circular.

Instead ask whether the same source facts support a weaker but still discriminating rate statement.

Strong warning boundaries remain:

- a proposed provider is equivalent to RH and is being used as an assumption rather than proved;
- a new definition simply inserts `centeredSigma = 0` or bounded normalized Gap;
- an inequality is required in a mathematically invalid direction;
- a load-bearing theorem depends on `sorryAx`, a new axiom, or an unrealizable antecedent;
- the route silently returns to the already closed positive-density/current-residual-majorant geometry;
- repeated modules rename the same missing bridge without extracting new source information.

These warnings should trigger a strategy review, not an automatic instruction to stop all investigation.

## 15. Preferred implementation style

Prefer one focused audit module, tentatively named along the lines of

```text
ZeroDerivedDualTailRateNormalizedModeBridgeAudit.lean
```

but rename it if the repository inspection identifies a more accurate mathematical object.

The module may include:

- small exact source-characterization lemmas;
- normalized-tail transport lemmas;
- cutoff-scale comparison lemmas;
- boundedness/non-divergence interfaces for the normalized Gap;
- explicit obstruction or countermodel lemmas where they sharpen the information boundary;
- conditional frontier lemmas only when they precisely identify the remaining load-bearing hypothesis.

Avoid creating many numbered Lean modules merely to record exploratory algebra. Keep failed algebraic experiments in the report unless they produce reusable exact theorems.

## 16. Success ladder

Do not force a binary `PROVED / FAILED` classification.

At the end, choose the strongest accurate classification supported by the implementation, for example:

```text
NORMALIZED-MODE-BRIDGE-CLOSED
COFINAL-BOUNDED-BRIDGE-CLOSED
ZERO-DERIVED-NONDIVERGENCE-CLOSED
TWO-SIDED-TAIL-RATE-FOUND
RATE-OBSERVABLE-FOUND
PARTIAL-RATE-BRIDGE
RATE-INFORMATION-OBSTRUCTION
SOURCE-ASYMPTOTIC-GAP
NEW-INFORMATION-FOUND
```

Multiple labels may be appropriate.

If a theorem unexpectedly proves the critical-line conclusion for every nontrivial zero, do not suppress it merely because the checkpoint was exploratory. Audit its dependencies and continue to the exact Mathlib RH wrapper if the theorem is genuinely source-derived and axiom-clean.

## 17. Axiom and provenance audit

For every load-bearing new theorem:

- identify whether it is `U0`, `U1`, `U2`, or `C`;
- state its exact hypotheses;
- prove a characterization from pre-existing source objects where a new definition is introduced;
- verify any denominator or eventual nonvanishing hypothesis;
- distinguish exact identities, upper bounds, lower bounds, and asymptotic equivalences;
- inspect `#print axioms`;
- reject `sorryAx`;
- do not add `native_decide` as a proof escape;
- do not add new axioms;
- run focused build;
- run `./lean-build.sh` for the focused module;
- run `lake build DkMath.RH` if the public import surface changes;
- run `git diff --check`.

## 18. Required report

Create

```text
0006-ZDSS-004-dual-tail-rate-extraction-normalized-mode-bridge-exploration-report.md
```

or a close descriptive filename if the implemented result justifies renaming.

The report must contain:

1. current ZDSS-001 / ZDSS-003 trusted spine;
2. exact normalized-Gap dichotomy being targeted;
3. normalized-tail APIs inspected;
4. candidate rate observables considered;
5. a table classifying candidates by `U0/U1/U2/C`;
6. exact new Lean theorems and what information they add;
7. whether full boundedness, cofinal boundedness, non-divergence, or only weaker rate information was obtained;
8. any exact obstruction showing why a plausible bridge loses information;
9. dependency and axiom audit;
10. the smallest remaining mathematical obligation after this checkpoint;
11. a recommendation for the next checkpoint based on the mathematics actually found, not on the original roadmap numbering alone.

## 19. Global objective reminder

The full research objective remains Mathlib's exact `RiemannHypothesis`.

The currently verified structure is:

```text
standard nontrivial zeta zero
  -> two separately controlled endpoint sources
  -> source-matched positive scalar E_K -> 0

and independently

off-critical centered coordinate
  -> normalized mode Gap G_K -> +infinity.
```

ZDSS-004 should investigate the missing bridge:

```text
zero-derived endpoint/tail rate information
  -> enough control of G_K to contradict off-critical divergence.
```

Do not rebuild DkReal or the RH wrapper before the bridge exists.

Do not assume that the final bridge must look like the previously imagined uniform quadratic coercivity inequality. A weaker rate contradiction is fully acceptable if it is exact, source-preserving, and sufficient.
