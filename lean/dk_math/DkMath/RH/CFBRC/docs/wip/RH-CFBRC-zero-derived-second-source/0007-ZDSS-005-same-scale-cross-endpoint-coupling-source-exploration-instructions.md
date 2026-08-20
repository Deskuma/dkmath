# ZDSS-005 — same-scale cross-endpoint coupling source exploratory instructions

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Parent roadmap: `0000-RH-CFBRC-zero-derived-second-source-roadmap.md`

Depends on:

- `0002-ZDSS-001-zero-derived-source-rank-independence-audit-report.md`
- `0004-ZDSS-003-source-matched-positive-scalar-centered-coercivity-exploration-report.md`
- `0006-ZDSS-004-dual-tail-rate-extraction-normalized-mode-bridge-exploration-report.md`
- `ZeroDerivedPrimeCoordinateSourceRankAudit.lean`
- `ZeroDerivedDualEndpointPositiveScalarCoercivityAudit.lean`
- `ZeroDerivedDualTailRateNormalizedModeBridgeAudit.lean`
- `PrimeMirrorEtaAsymptoticDichotomy.lean`
- completed-zeta / functional-equation / endpoint transport APIs already present in `DkMath.RH.CFBRC`

## 0. Route transition

ZDSS-001 established a genuine two-coordinate zero-derived source:

```text
A_K(s) := etaPairedPartial K s
B_K(s) := etaPairedPartial K (criticalMirror s).
```

ZDSS-003 established a positive scalar with a complete U-side:

```text
E_K(s) = ||A_K(s)||^2 + ||B_K(s)||^2,
E_K(s) -> 0
```

at every nonreal standard nontrivial zeta zero, but no centered-coordinate C-side lower bound.

ZDSS-004 then extracted the actual two-sided endpoint rates.  For a nonreal standard nontrivial zeta zero with

```text
sigma = s.re,
delta = centeredSigma sigma = sigma - 1/2,
q = K + 1,
```

the two endpoints separately have nonzero normalized limits of the schematic form

```text
q^sigma       * A_q(s)      -> nonzero finite constant,
q^(1-sigma)   * B_q(s)      -> nonzero finite constant,
```

up to the already certified unit pair-frame rotations.

ZDSS-004 also proves the exact common-scale factorization

```text
rawEndpointNormRatio_K(s)
  = endpointIncrementMirrorRatio_K(s)
      * selfNormalizedEndpointNormRatio_K(s),
```

where

```text
endpointIncrementMirrorRatio_K(s)
  = q^(2 * delta)
```

and

```text
selfNormalizedEndpointNormRatio_K(s)
  -> positive finite constant.
```

Therefore the horizontal coordinate is no longer hidden.  It is exactly the polynomial growth exponent that survives when the two endpoint sources are placed on one common raw scale.

The new problem is not to discover another individual endpoint asymptotic.  The missing information is an independently zero-derived **cross-endpoint coupling on a common scale**.

This checkpoint is called `ZDSS-005` even though the original roadmap reserved that label for DkReal completion.  The route has discovered a new load-bearing gap before DkReal can be used.  DkReal remains downstream and must not be entered until this common-scale gap is closed or sharply classified.

## 1. Purpose

This is an exploratory research-and-implementation checkpoint.

Codex must inspect the current repository, trace exact source provenance, reason about candidate same-scale relations, compare their logical strength, and implement the strongest exact Lean results that the existing mathematics supports.

Do not treat the following as a predetermined theorem script.

The central question is:

> Does the standard nontrivial zeta-zero hypothesis provide any independent finite or asymptotic relation that constrains the original and critical-mirror endpoint sources on the **same cutoff scale**, rather than normalizing each endpoint by its own natural exponent?

The desired information may appear as a norm comparison, a complex linear relation, a finite functional-equation identity, a common remainder equation, a cross-correlation, a cofinal comparison, or another exact source-derived observable.

The checkpoint should not stop merely because the first natural candidate fails.  Use failed candidates to identify what information is missing, then inspect nearby source-preserving formulations.

## 2. Fixed exact factorization and why it matters

Use the ZDSS-004 theorem

```lean
etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio
```

and its eventual zero-derived version as the main algebraic diagnostic.

Schematically:

```text
Q_K(s) := ||B_(K+1)(s)|| / ||A_(K+1)(s)||,
R_K(s) := separately-normalized endpoint norm ratio,
G_K^ratio(s) := q^(2 * centeredSigma s.re),
```

with exact eventual factorization

```text
Q_K(s) = G_K^ratio(s) * R_K(s)
```

and

```text
R_K(s) -> R_infinity(s),
0 < R_infinity(s) < infinity.
```

Thus:

```text
Q_K(s) ~ positive_constant * q^(2 * centeredSigma s.re).
```

This factorization should be used to evaluate the mathematical strength of every proposed coupling theorem.

A candidate common-scale relation is useful only if it prevents the surviving factor

```text
q^(2 * centeredSigma s.re)
```

from escaping in at least one direction, and its provenance is genuinely independent of the already extracted separate endpoint asymptotics.

## 3. Important asymmetry: one-sided boundedness is only one-sided information

Do not overclaim from a single upper bound on `Q_K(s)`.

If

```text
Q_K(s) <= C
```

eventually and `R_K(s)` tends to a positive finite constant, then the factorization excludes

```text
centeredSigma s.re > 0.
```

It does **not** by itself exclude

```text
centeredSigma s.re < 0,
```

because then `Q_K(s) -> 0` is compatible with eventual boundedness.

Therefore explicitly audit at least the following closure mechanisms.

### 3.1 Mirror reapplication

The critical mirror of a standard nontrivial zero is again a standard nontrivial zero, and

```text
centeredSigma (criticalMirror s).re = -centeredSigma s.re.
```

If the same zero-derived upper-bounded-ratio theorem is uniform in the sense that it applies to every nonreal standard nontrivial zero, then apply it once to `s` and once to `criticalMirror s`.

The two applications may together force

```text
centeredSigma s.re <= 0
and
-centeredSigma s.re <= 0,
```

hence equality.

Formalize this implication if the needed hypotheses can be expressed cleanly without smuggling in RH.

### 3.2 Two-sided comparability at one zero

A stronger same-zero relation of the form

```text
0 < c <= Q_K(s) <= C
```

eventually would directly exclude both signs of the horizontal exponent.

Equivalent formulations may include:

```text
Q_K(s) is eventually bounded above and away from zero,
Q_K(s) and 1 / Q_K(s) are both eventually bounded,
abs (log Q_K(s)) is eventually bounded,
Q_K(s) tends to a finite positive limit,
Q_K(s) remains in one compact subset of (0,+infinity) cofinally.
```

Do not privilege one formulation before inspecting what the source APIs naturally provide.

### 3.3 Cofinal or subsequential control

Because `q^(2*delta)` has monotone polynomial escape for fixed nonzero `delta`, full eventual boundedness may be stronger than necessary.

Investigate whether any exact source relation gives only:

```text
Q_K <= C along a cofinal subsequence,
Q_K >= c > 0 along a cofinal subsequence,
liminf Q_K < +infinity,
limsup Q_K > 0,
a recurring same-scale comparison at infinitely many cutoffs.
```

Determine carefully which such statements are sufficient, together with the exact factorization and mirror symmetry, to force the critical line.

## 4. Primary source families to inspect

The order below is a research priority, not a rigid script.  If repository evidence points elsewhere, follow the stronger source.

### 4.1 Finite-truncation functional-equation coupling

The ordinary functional equation or completed-zeta symmetry transports complete zero information between `s`, `1-s`, conjugates, and critical mirrors.  ZDSS-001 already showed that merely reevaluating the P2-F whole source on that orbit gives only duplicate information.

The new question is more specific:

> Is there an exact **finite truncation plus remainder** identity in the current repository, or derivable from accepted APIs, in which the original and mirror endpoint pieces occur simultaneously at one common cutoff or one coupled pair of cutoffs?

Inspect whether a finite functional-equation decomposition has schematic shape such as

```text
finite_original(K,s)
  + coefficient(s,K) * finite_mirror(K,s)
  + controlled_remainder(K,s)
  = zero-derived quantity,
```

or an equivalent common-scale relation.

The coefficient may be complex and need not have modulus one.  Track it exactly; do not discard a horizontal power by renormalization unless the discarded factor is independently controlled.

If a coupled cutoff pair `(K,L)` is natural rather than `(K,K)`, determine whether the relation can still yield one common asymptotic scale after an exact source-preserving comparison of `K` and `L`.

Do not invent an approximate functional equation theorem by definition.  Either derive it from existing analytic APIs or record the exact missing theorem.

### 4.2 Completed-zeta first-order or local zero data

ZDSS-001 found that completed-zeta zero transports and simple derivative reflection are orbit transports, not by themselves new finite source coordinates.

Re-audit them only for a different purpose:

```text
Can local zero data couple the two endpoint finite/tail expansions before separate natural normalization?
```

Possible structures include:

```text
shared derivative coefficient,
shared residue/principal-part coefficient,
a common first-order expansion,
a Wronskian-like relation,
a symmetric finite remainder identity.
```

Do not assume that derivative data vanishes at a zero.  `zeta(s)=0` does not imply `zeta'(s)=0`.

A derivative or local-expansion route counts only if the same `hs` supplies the necessary data and the final common-scale relation is exact or has a rigorously controlled remainder.

### 4.3 Direct endpoint-tail comparison

Inspect whether the two ordinary Eta tails themselves satisfy a relation stronger than their separate asymptotics when both endpoints arise from one zero orbit.

The desired relation might be weaker than equality.  Examples to audit include:

```text
same-scale norm comparability,
ratio boundedness,
ratio bounded away from zero,
phase-aligned difference smaller than either endpoint,
common leading coefficient after one shared normalization,
paired remainder cancellation,
exact conjugate/functional coefficient relation.
```

Be careful: the unconditional ordinary tail asymptotics already allow different exponents `sigma` and `1-sigma`.  A relation obtained solely from applying the same unconditional tail theorem twice is not new cross-endpoint information.

### 4.4 Finite prime-factor coordinate coupling

ZDSS-001 exposed each endpoint finite sum through the same Eta term architecture and inherited finite prime-factor provenance.

Inspect whether retaining the endpoint coordinates before summation reveals a same-mode or same-prime relation that is lost by the whole sums.

Candidate questions:

```text
Are original/mirror coordinates paired by an exact multiplicative factor?
Does one zero identity give a joint linear constraint across each mode?
Is there a finite Gram matrix whose off-diagonal term is source-controlled?
Can prime-factor decomposition produce a common positive scalar without reversing triangle/Cauchy inequalities?
Does a natural symmetric coordinate basis isolate the q^(2*delta) factor?
```

Do not repeat the ZDI-011 error of inferring modewise energy from one small whole sum.

But do not assume in advance that all modewise information is inaccessible: ZDSS-001 now has two endpoint equations, so audit the **actual two-source coordinate manifold** rather than arbitrary independent complex vectors.

### 4.5 Scale-coupled cutoffs

The same-scale comparison need not literally use identical integer cutoff labels if an exact arithmetic coupling provides a canonical map between them.

Audit possibilities such as:

```text
K versus 2K,
K versus floor(alpha*K),
paired truncation lengths arising from a functional equation,
reciprocal analytic scales,
cutoffs selected by the same prime-factor support boundary.
```

The key requirement is that the comparison cannot normalize each endpoint by its own unknown horizontal exponent and thereby divide out the desired information.

## 5. Minimal sufficient frontier lemmas worth formalizing

Even before finding a provider, it may be useful to formalize clean frontier theorems expressing how weak a same-scale relation would suffice.

These are classification tools, not assumptions to be imported as evidence.

Possible theorem shapes include the following.

### 5.1 Upper bounded raw ratio for every zero plus mirror reuse

Schematic theorem:

```lean
-- schematic only
 theorem re_eq_half_of_rawRatio_eventually_bounded_for_zero_and_mirror
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (hboundS : ∃ C, ∀ᶠ K in atTop,
      etaDualEndpointRawNormRatio K s ≤ C)
    (hboundMirror : ∃ C, ∀ᶠ K in atTop,
      etaDualEndpointRawNormRatio K (criticalMirror s) ≤ C) :
    s.re = 1 / 2 := by
  ...
```

A more reusable formulation may quantify one provider over every nonreal standard zero and then instantiate it at both orbit points.

### 5.2 Two-sided comparability frontier

```text
0 < c,
0 < C,
eventually c <= Q_K(s),
eventually Q_K(s) <= C
```

should force `s.re = 1/2` through the exact ZDSS-004 rate factorization.

Formalize the weakest convenient version if doing so helps evaluate candidate providers.

### 5.3 Cofinal boundedness frontier

If the existing real-power asymptotic API makes it convenient, prove that an off-critical polynomial ratio cannot be bounded along a cofinal subsequence in its escaping direction.

Then combine with mirror symmetry as needed.

Do not spend excessive time polishing abstract filter lemmas unless they materially reduce the source obligation.

## 6. Distinguish source levels

Continue the information-level discipline.

Use the following labels in the report where useful:

```text
U0  unconditional analytic/algebraic fact in the open strip
U1  zero-derived separate endpoint information
U1X zero-derived cross-endpoint information on a common scale
U2  anti-divergence / boundedness information for the normalized mode detector
C   critical-line consequence
```

ZDSS-004 reached strong `U1` but demonstrated compatibility with off-critical `U2` divergence.

ZDSS-005 seeks a genuine transition

```text
U1 -> U1X
```

or directly

```text
U1X -> U2.
```

A theorem that merely restates `q^sigma A_q -> const` and `q^(1-sigma) B_q -> const` remains `U1`, even if written as a ratio after separate normalization.

## 7. Strong warning boundaries, not automatic checkpoint termination

The following are strong signs that one candidate is circular, duplicate, or source-empty:

- the candidate comparison is obtained only after normalizing each endpoint by `s.re` and `1-s.re` separately;
- the proposed bounded raw ratio is simply assumed;
- a coefficient is defined using `centeredSigma s.re` specifically to cancel the exact horizontal power;
- a functional-equation statement only transports the complete zero and does not couple finite endpoint pieces;
- a derivative route silently assumes derivative vanishing;
- a positive modewise bound reverses triangle, Cauchy-Schwarz, or another one-way inequality;
- an endpoint comparison proposition is already shown equivalent to `s.re = 1/2` and is then reused as a provider;
- a declaration depends on `sorryAx`, a new axiom, or an unrealizable antecedent;
- the work returns to the closed positive-density/current-majorant route;
- several new modules merely rename the same missing common-scale comparison.

These warnings do **not** require immediate termination of the whole checkpoint.  When one candidate hits such a boundary, classify it and inspect nearby source families or weaker sufficient relations.

Stop the overall exploration only when the implemented evidence supports a clear proof completion, a sharp source-availability obstruction, or a well-localized smallest next mathematical obligation.

## 8. Do not confuse an RH-load-bearing theorem with circularity

Any genuine same-scale relation strong enough to bound the raw endpoint ratio in both horizontal directions will be RH-load-bearing in combination with ZDSS-004.

That fact alone is not a reason to reject it.

The correct distinction is:

```text
GOOD:
  theorem is independently derived from accepted zero/functional/arithmetic data,
  then combined with ZDSS-004 to obtain the critical line.

BAD:
  theorem is assumed, defined, or imported from an RH-equivalent frontier
  whose only justification is the desired critical-line conclusion.
```

If Codex unexpectedly derives a strong common-scale relation from unconditional or standard zero data, follow the proof.  Do not weaken a valid theorem merely because it would finish RH.

## 9. Suggested research workflow

### Phase A — exact API inventory

Inspect the current repository for declarations involving combinations of:

```text
functional equation
completed zeta
criticalMirror
one_sub
conj
Eta tail
Eta paired partial
finite truncation
remainder
normalized tail
endpoint increment
prime-factor Eta term
derivative / local expansion
```

For every promising declaration record:

```text
hypotheses
finite/infinite object
cutoff variables
whether s and mirror s occur simultaneously
whether normalization uses one common scale or two endpoint-specific scales
whether the theorem is U0, U1, U1X, U2, or C
```

### Phase B — derive frontier strength

Before attempting a complicated provider, use the exact ZDSS-004 factorization to calculate what the candidate would imply.

Questions:

```text
Does it kill delta > 0 only?
Does mirror reuse kill delta < 0?
Does it directly give a two-sided ratio bound?
Does it only recover the already known individual exponents?
Does a cofinal version suffice?
```

Formalize small frontier lemmas when they remove ambiguity.

### Phase C — implement the strongest source-connected relation

Prefer exact finite identities over asymptotic statements when available.

If only asymptotic information is available, preserve constants and rates rather than immediately taking norms or big-O estimates.

Keep complex phase information until it is proved irrelevant; a phase relation may be exactly the missing cross-endpoint datum.

### Phase D — test against the off-critical compatibility certificate

Use

```lean
EtaDualEndpointRateNormalizedGapCompatibilityCertificate
```

as a firewall.

A purported new theorem must contribute information not already present in that compatibility certificate.  If it can coexist with the certificate under the hypothetical off-critical case without contradiction, it has not yet closed the required U1X gap.

### Phase E — classify and report

Do not force a binary success/failure label too early.

Possible final classifications include, but are not limited to:

```text
SAME-SCALE-COUPLING-FOUND
ONE-SIDED-COMPARISON-FOUND
MIRROR-CLOSURE-FOUND
TWO-SIDED-COMPARABILITY-FOUND
COFINAL-COMPARISON-FOUND
FINITE-FUNCTIONAL-COUPLING-FOUND
PHASE-COUPLING-FOUND
CROSS-ENDPOINT-SOURCE-FOUND
CROSS-ENDPOINT-SOURCE-ABSENT-IN-CURRENT-API
FUNCTIONAL-EQUATION-FINITE-GAP
COMMON-SCALE-INFORMATION-OBSTRUCTION
RH-PROOF-BRIDGE-CLOSED
```

Use a more precise classification if the mathematics suggests one.

## 10. Lean implementation discipline

Create a focused module only when actual theorem implementation is useful.  A plausible name is

```text
DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
```

but choose a more accurate name if the discovered source relation deserves it.

For every load-bearing new `def`:

- add a docstring explaining mathematical meaning;
- prove an exact characterization where applicable;
- identify whether it is merely a diagnostic observable or actual source information;
- do not encode `s.re = 1/2` or boundedness by construction.

For every load-bearing theorem:

- preserve source provenance;
- inspect realizability of hypotheses;
- distinguish zero-derived from unconditional facts;
- run `#print axioms`;
- no `sorryAx`;
- no new `axiom`;
- no `native_decide` as a substitute for the mathematical argument;
- focused `lake build`;
- wrapper build if used by the repository workflow;
- `lake build DkMath.RH` if the public import surface changes;
- `git diff --check`.

Do not add a public import for a purely exploratory module unless its results are accepted reusable Core.

## 11. Deliverables

Produce a report immediately after the instruction file in the same documentation directory, with the next numeric filename.

The report should include:

1. exact ZDSS-004 inherited factorization and rate recap;
2. source/API inventory for same-scale coupling candidates;
3. explicit distinction between endpoint-specific normalization and common-scale comparison;
4. candidate table with `U0/U1/U1X/U2/C` levels;
5. any frontier theorem showing how weak a ratio/comparability property would force the critical line;
6. mirror-reapplication audit;
7. finite functional-equation / completed-zeta coupling audit;
8. prime-coordinate or phase-coupling audit if relevant;
9. exact new Lean theorems and axiom status;
10. final classification;
11. the single smallest remaining mathematical obligation if RH is not completed.

If no new Lean theorem is justified, a precise negative report is preferable to manufacturing an API.

## 12. Research success is broader than direct RH completion

The best possible outcome is of course a source-derived same-scale relation that, together with the ZDSS-004 factorization, forces

```text
s.re = 1/2
```

for every standard nontrivial zero and closes `Mathlib.RiemannHypothesis` through the existing wrapper.

But the checkpoint is also successful if it proves a materially sharper fact such as:

```text
only one horizontal side can be excluded from one natural source relation;
mirror reuse converts that one-sided theorem into a full critical-line theorem;
a finite functional-equation relation reduces the gap to one explicit remainder estimate;
a phase coupling exists but loses amplitude control at one exact step;
the current repository contains no finite common-scale coupling theorem and the missing theorem is identified precisely.
```

Do not prematurely return to DkReal, fixed-Xi vanishing, old residual-majorant geometry, or a new arbitrary scalar search.

The present research frontier is now very specific:

```text
separate zero-derived endpoint asymptotics
  + exact raw-ratio factorization
  + positive finite self-normalized ratio limit
  + critical-mirror symmetry

        ?

independent same-scale cross-endpoint coupling

        -> horizontal power cannot escape
        -> centeredSigma s.re = 0
        -> s.re = 1/2.
```

Final guiding question:

> What exact information from the **same zero** relates the two endpoint sources before their unequal natural powers are divided out?
