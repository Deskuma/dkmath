# RH-CFBRC Zero-Derived Second Source Roadmap

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Base: `develop` at `e5098e181d6ff510822f872c26332ace2ce80b69`

Date: 2026-08-20

## 0. Reset and route identity

This branch starts from the completed ZDI finite-certificate audit.

The former branch

```text
wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0
```

is closed at

```text
CLOSED — O-INFORMATION
```

and its numbering is retired here.

New work starts from `ZDSS-001`.

`ZDSS` means **Zero-Derived Second Source**.

The purpose of this route is not to sharpen the already audited Eta whole-sum estimate. The purpose is to determine whether a genuinely additional zero-derived source exists and, only if it does, whether that additional information can be converted into a positive centered-coordinate scalar.

The trusted ZDI Core remains available, especially ZDI-005 P2-F / Q2-F and the ZDI-011 information firewall.

## 1. Exact research frontier inherited from ZDI

The previous route isolated the desired finite scalar certificate into three properties.

For a standard nontrivial zeta zero `s`, seek a finite real scalar `E K s` satisfying:

```text
A. finite arithmetic provenance
B. zero-derived upper control
C. centered-coordinate lower control
```

Schematic target:

```text
0 <= E K s
E K s <= epsilon K s
lowerWeight K s * (centeredSigma s.re)^2 <= E K s
epsilon K s -> 0
```

with sufficient positive control of `lowerWeight`.

The previous branch has two separate halves:

```text
P2-F / Q2-F:
  A + B for a cancellation-prone finite complex whole sum

primeMirrorEnergy / aggregate mirror Gap:
  A + C for a nonnegative centered-coordinate detector
```

The missing mathematical ingredient is therefore not another estimate of either existing object. It is an independent zero-derived source identity capable of connecting the zero hypothesis to a positive scalar carrying centered-coordinate information.

## 2. Fixed facts that must not be re-proved

Preserve the following accepted source spine.

### 2.1 Genuine zero-derived finite prime-factor source

For a nonreal standard nontrivial zeta zero, ZDI-005 provides the genuine finite source identity

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
  = -etaCriticalMirrorDefectPairTail K s
```

and the finite source has exact prime-factor coordinate provenance.

ZDI-006 gives

```lean
etaPrimeFactorMirrorDefectPairedPartial K s -> 0.
```

This is trusted reusable Core.

### 2.2 Whole-sum information firewall

ZDI-011 proves that for arbitrary post-processing `F`,

```lean
F (etaPrimeFactorMirrorDefectPairedPartial K s)
  = F (etaCriticalMirrorDefectPairedPartial K s).
```

Thus no operation depending only on that one complex whole-sum value can be counted as a second source.

The generic opposite-unit countermodel also records that

```text
small whole sum
```

does not imply small diagonal mode energy.

Do not re-open whole-sum norm, projection, rotation, squaring, or renamed coercivity routes.

### 2.3 Positive centered-coordinate candidates

Historical `primeMirrorEnergy` and aggregate mirror Gap remain valid unconditional candidates for the C side. They are finite, nonnegative, and have exact critical-line rigidity.

They are not zero-derived providers.

No theorem may treat their desired vanishing or smallness as an assumption unless independently derived from a new source.

### 2.4 DkReal completion is ready but inactive

The DkReal shrinking-interval uniqueness layer is not the current research problem.

Do not add rational radii, nested intervals, or DkReal wrappers before a genuine B-to-C bridge has been found.

## 3. Central principle: information rank before quadraticization

The first question of this branch is not

> Can we build a quadratic energy?

It is

> Does the zero hypothesis provide more than one independent finite source coordinate after all exact symmetries and invertible transports are accounted for?

A second formula is not a second source merely because it has a different syntax.

The following transformations are information-preserving unless an additional independent datum is introduced:

```text
exact equality
nonzero scalar multiplication
unit multiplication
complex conjugation with known inverse
critical-mirror rewriting when the source is already determined by the first source
coordinate permutation
any explicitly invertible linear transport of the same source data
post-processing of one whole complex value
```

A candidate counts as genuine information gain only when its value is not recoverable from the existing P2-F source by already certified invertible transformations and source-free algebra.

Do not define an abstract `rank` predicate first and then satisfy it by construction. Align actual existing source maps first; introduce rank language only after the concrete source space and transformations are fixed.

## 4. Phase ZDSS-001 — source inventory and independence audit

Inventory every zero-derived source already available from the same standard nontrivial zero hypothesis `hs` without adding RH-equivalent assumptions.

At minimum inspect:

```text
P2-F finite prime-factor source at s
critical-mirror transported source
conjugate transports
functional-equation / completed-zeta zero transports already present in DkMath
separate endpoint identities if they carry more information than the defect difference
multiple-cutoff exact identities only insofar as they are zero-specific
```

For each candidate, determine by exact Lean theorem whether it is:

```text
SAME
SCALAR-DUPLICATE
CONJUGATE-DUPLICATE
MIRROR-DUPLICATE
INVERTIBLE-TRANSPORT-DUPLICATE
GENUINELY-INDEPENDENT
UNKNOWN-GAP
```

The classification must be derived from the current repository declarations, not from visual similarity or general mathematical expectation.

A useful ZDSS-001 result is either:

1. one explicit pair of finite zero-derived source maps with certified genuine information gain; or
2. a precise obstruction showing that all currently available transforms of P2-F remain rank-one information.

## 5. Phase ZDSS-002 — dual finite source audit

Proceed only if ZDSS-001 shows that the existing source inventory contains no independent second coordinate or identifies a concrete external candidate family that is not already duplicate information.

The preferred candidate family is a **dual finite source** in which the same zero hypothesis controls two finite arithmetic pieces rather than one whole defect sum.

A schematic analytic shape is:

```text
A_X(s) + chi(s) * B_Y(1-s) + R_XY(s) = zeta(s)
```

or an equivalent already available DkMath/Mathlib theorem.

This roadmap does not authorize inventing an approximate functional equation API. First audit whether an exact theorem with suitable finite source provenance already exists or can be derived from fixed standard APIs without importing RH-equivalent content.

If such a dual source exists, certify whether `A_X` and `B_Y` genuinely add information after known functional-equation symmetry is factored out.

If no suitable exact source is available, record that as a named source-availability obstruction rather than building a heuristic substitute.

## 6. Phase ZDSS-003 — quadraticization only after independence

Only after a genuinely independent pair is certified may the route form a positive scalar from the pair.

Permitted schematic forms include:

```text
|L1 K s|^2 + |L2 K s|^2
```

or a source-matched Hermitian / polarization form whose positivity is separately proved.

The key requirement is that the quadratic scalar must inherit zero-derived upper control from the two independent source identities by valid inequalities.

Do not use an invalid implication of the form

```text
|sum z_k| small -> sum |z_k|^2 small.
```

The preferred object is not necessarily the historical `primeMirrorEnergy`. A new source-matched positive scalar is acceptable if it satisfies A/B/C without encoding the desired conclusion.

## 7. Phase ZDSS-004 — centered-coordinate coercivity bridge

If a source-derived positive scalar `E K s` is available, seek an unconditional lower theorem of the form

```text
lowerWeight K s * (centeredSigma s.re)^2 <= E K s
```

or

```text
abs (centeredSigma s.re) <= radius K s.
```

The lower theorem must be independent of the zero hypothesis except for ordinary domain facts already known for a nontrivial zero.

The coefficient must have sufficient positivity so that zero-derived upper control forces the radius to zero.

At this stage it is legitimate to compare the new scalar with `primeMirrorEnergy` or aggregate mirror Gap, but only through exact source-preserving theorems.

## 8. Phase ZDSS-005 — DkReal completion, only if the scalar bridge closes

If ZDSS-004 yields

```text
(centeredSigma s.re)^2 <= epsilon K s
epsilon K s -> 0
```

or an equivalent absolute-coordinate bound, then and only then return to the existing DkReal completion layer.

Expected final path:

```text
independent second source
  -> source-derived positive scalar
  -> centered-coordinate shrinking bound
  -> rational majorants
  -> common nested shrinking intervals around 1/2
  -> DkReal uniqueness
  -> Mathlib RiemannHypothesis
```

Do not rebuild DkReal completeness or the existing RH wrapper.

## 9. Candidate source families and priority

Use the following priority unless repository facts force a different order.

### Priority 1 — existing zero/mirror/functional-equation source rank

Cheapest and mandatory first audit. Determine whether an independent second source is already present but hidden by previous defect packaging.

### Priority 2 — dual finite arithmetic source

Audit an exact two-piece finite representation associated with the standard zero, if a source-preserving theorem is available.

### Priority 3 — fixed Xi / second-moment source

The fixed Xi defect already has strong positivity and an RH-equivalent global vanishing frontier. Therefore it is admissible only if a **new independent arithmetic upper/sign theorem** is found.

Do not use `PascalCenteredXiFixedDefectVanishesOnSafeRadii` or an equivalent statement as a provider.

### Priority 4 — local residue / multiplicity source

Local residue identities are genuinely zero-derived but primarily detect multiplicity. Use them only if an additional theorem converts their data into a positive horizontal/centered scalar without importing RH-equivalent content.

## 10. Stop conditions

Stop the current candidate and record a named obstruction when any of the following occurs:

1. The candidate is an exact equality or invertible transform of the existing P2-F whole source.
2. The apparent second source is only conjugation, mirror rewriting, or nonzero scalar multiplication with no information gain.
3. Positivity requires squaring mode coordinates whose individual upper control is not zero-derived.
4. A quadratic upper bound requires reversing triangle, Cauchy-Schwarz, or another one-way inequality.
5. The candidate provider is equivalent to `RiemannHypothesis` or to fixed-Xi defect vanishing.
6. The source depends on an unproved `sorry` or an unrealizable antecedent.
7. A new definition encodes `centeredSigma = 0`, a shrinking radius, or the desired energy bound by construction.
8. Work starts drifting back into ZDI-007..010 positive-density/current-majorant geometry.
9. Successive modules merely rename the same missing independence statement.

A stopped candidate is a successful audit result.

## 11. Lean-first certification discipline

For every load-bearing declaration:

- prove a characterization theorem from existing source objects;
- audit realizability / non-vacuity of hypotheses;
- record exact source provenance from `NontrivialRiemannZetaZero` or unconditional finite arithmetic;
- classify RH-equivalent propositions as frontiers, never providers;
- inspect with `#print axioms`;
- reject any dependency on `sorryAx`;
- run focused builds;
- run the public/root build when imports change;
- run `git diff --check`.

A compiled `def` is not mathematical progress without a meaning theorem.

## 12. Immediate sequence

### ZDSS-001 — zero-derived source rank / independence audit

Trace the existing P2-F source and every already available zero-preserving mirror, conjugate, functional-equation, completed-zeta, endpoint, and cutoff transport. Align them on concrete finite source objects and classify whether any candidate supplies genuine additional information.

Do not build a quadratic scalar in this phase unless genuine independence is first certified.

### ZDSS-002 — independent dual finite source audit

Only if required after ZDSS-001, audit the nearest exact dual finite arithmetic representation whose two source pieces are both controlled by the same standard zero hypothesis.

### ZDSS-003 — source-matched positive scalar

Only after independence, construct and certify a nonnegative quadratic/Hermitian scalar with zero-derived upper control.

## 13. Completion criterion

This branch closes successfully in either of two ways.

### Proof completion

An axiom-audited Lean term of Mathlib's exact `RiemannHypothesis` is produced through a genuinely independent source route.

### Research closeout

The audited second-source families are shown to carry no additional zero-derived information or to fail at a precise named source/positivity/coercivity obstruction, and the smallest missing mathematical ingredient is recorded without manufacturing a provider.

Final research rule:

```text
Do not ask how to estimate the old source harder.
Ask what new information the zero hypothesis actually gives.
```
