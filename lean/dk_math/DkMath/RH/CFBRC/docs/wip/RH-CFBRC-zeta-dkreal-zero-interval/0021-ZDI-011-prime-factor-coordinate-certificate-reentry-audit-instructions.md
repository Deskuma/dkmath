# ZDI-011 — prime-factor coordinate finite-certificate re-entry audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0010-ZDI-005-eta-prime-factor-finite-source-bridge-report.md`
- `0012-ZDI-006-P2F-coercivity-cancellation-feasibility-audit-report.md`
- `0014-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-report.md`
- `0016-ZDI-008-positive-density-bounded-span-projection-feasibility-audit-report.md`
- `0018-ZDI-009-positive-density-normalized-constant-obstruction-audit-report.md`
- `0020-ZDI-010-positive-density-source-connected-constant-obstruction-report.md`
- `EtaCriticalMirrorPrimeFactorFiniteSourceBridge.lean`
- `EtaCriticalMirrorPrimeFactorCoercivityAudit.lean`
- `EtaCriticalMirrorPositiveDensitySourceConnectedConstantObstruction.lean`

## 0. Strategic reset

ZDI-010 closes the positive-density/current-majorant branch as a source-connected obstruction.

The following route is now **closed** unless a genuinely sharper exact-tail theorem is independently discovered later:

```text
P2-F whole Eta defect partial
  -> moving/block frame
  -> positive-density margin
  -> current absolute residual power majorant
  -> residual domination
```

ZDI-011 must not continue refining the same schedule, frame, margin, or current residual-majorant constants.

Return to the main ZDI purpose from the roadmap:

> For every standard nontrivial zeta zero `s`, derive finite prime-based certificates producing a stagewise bound on the centered real coordinate and ultimately rational shrinking intervals containing both `s.re` and `1/2`.

The preferred final shape remains

```text
|s.re - 1/2| <= q K
q K -> 0
```

or, before rationalization,

```text
(centeredSigma s.re)^2 <= epsilon K

epsilon K -> 0.
```

## 1. Fixed facts after ZDI-005..010

### P2-F / Q2-F — keep

ZDI-005 gives a genuine zero-derived finite prime-factor source:

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
  = - etaCriticalMirrorDefectPairTail K s
```

for a nonreal nontrivial zeta zero.

The finite source is an exact `Finset.range K` sum whose natural bases are written through `Nat.factorization.support` and prime logarithms.

ZDI-006 gives

```lean
etaPrimeFactorMirrorDefectPairedPartial K s -> 0
```

through the inherited Eta tail bound.

These are real progress and remain on the trusted source spine.

### Whole-sum coercivity — rejected under current information

ZDI-006 correctly records that any functional depending only on the value or norm of

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
```

is mathematically a functional of the old Eta defect partial. Prime-factor notation alone does not remove cancellation.

Do not retry a theorem of the schematic form

```text
c(K,s) * |centeredSigma s.re|
  <= ||etaPrimeFactorMirrorDefectPairedPartial K s||
```

unless the left-to-right inequality uses a genuinely new source-derived arithmetic fact beyond the whole-sum value.

### Positive-density/current-majorant route — closed

ZDI-007..010 establish, with source objects in Lean, that:

- positive-density schedules do not instantiate the old shrinking-frame schedule;
- bounded-span angle feasibility alone is insufficient;
- the normalized current residual majorant is larger than the certified positive-density margin by a strict factor already before any projection loss;
- ZDI-010 connects this comparison to the actual residual-majorant and margin-lower-bound objects.

Classify this route as

```text
O-CONSTANT / FACT-FIXED
```

for the current bounds.

Do not build ZDI-011 on a renamed residual-domination predicate.

## 2. Core question of ZDI-011

The question is no longer:

> Can the whole complex P2-F sum be shown coercive?

Instead ask:

> Does the finite prime-factor coordinate expansion expose a **source-connected nonnegative scalar certificate** that is both controlled from the zero-derived identities and coercive in the centered coordinate?

A successful finite certificate `E K s : ℝ` must have all three independent properties below.

### A. Prime-coordinate provenance

`E K s` must be characterized directly from the existing finite prime-factor coordinates or another already certified finite prime source.

It must not be defined as the desired right-hand side, as `centeredSigma^2`, or as an RH-equivalent predicate.

### B. Zero-derived upper control

For

```lean
hs : NontrivialRiemannZetaZero s
```

there must be a proved finite bound

```text
E K s <= upper K s
```

with

```text
upper K s -> 0.
```

The proof must come from an exact zero-derived identity, not from an invalid reverse triangle inequality.

### C. Coordinate lower control

Independently of the zero hypothesis, prove a bound of the form

```text
lowerWeight K s * (centeredSigma s.re)^2 <= E K s
```

or an equivalent absolute-coordinate inequality.

To be useful for DkReal, the quotient

```text
upper K s / lowerWeight K s
```

must tend to zero, with eventual positivity of `lowerWeight` proved.

If all three are obtained, the next task may rationalize the resulting radius.

## 3. Information-gain firewall

A candidate is **not** new information if it is determined only by the single complex whole-sum value.

In particular, do not infer any of the following from smallness of a sum without an additional theorem:

```text
||sum z_k|| small -> sum ||z_k|| small
||sum z_k|| small -> sum ||z_k||^2 small
||sum z_k|| small -> sum |projection z_k| small
```

A diagonal energy such as a sum of modewise squares may have excellent positivity in `centeredSigma`, but it does not become zero-derived merely because the whole P2-F sum is small.

If the only possible upper control requires such a passage, record the obstruction as **O-INFORMATION**.

A small generic countermodel may be formalized if useful, but it is only a firewall. It does not replace an audit of the actual Eta/prime-factor source.

## 4. First audit: preserve the two endpoint identities separately

ZDI-005 packages the critical-mirror defect, but the zero provenance ultimately comes from two endpoint zero identities.

Before searching for a new scalar, inventory the strongest already proved source statements separately for:

```text
eta paired source at s
eta paired source at criticalMirror s
```

and, if already available without new assumptions,

```text
conjugate / functional-equation zero transports
completed-zeta zero transports
```

Determine whether the defect equality discarded information that can be retained as a finite two-component source.

Do not introduce derivatives, shifted zeta values, twisted L-functions, or additional zeros unless an existing theorem supplies them from the same `hs` without an RH-equivalent assumption.

A useful result of this audit is either:

- an explicit finite source vector with genuinely more independent zero-derived coordinates than the single defect sum; or
- a theorem/report showing that the available endpoint/mirror equations reduce to the same information for the desired scalar purpose.

## 5. Second audit: existing positive prime-mirror Gap as a candidate target

Historical CFZP contains unconditional finite prime-mirror Gap facts, including aggregate objects with exact centered-coordinate rigidity such as a theorem of the shape

```text
cfzpAggregateMirrorGapUpTo X delta = 0 <-> delta = 0
```

and exact factorization through `delta^2` and a nonnegative Beam.

These are **not** zero-derived providers.  ZDI-011 may reuse them only as candidate coordinate-lower objects.

Audit whether there is an exact source-preserving bridge from the ZDI-005 finite prime-factor source to such a finite mirror Gap, or to an analogous Gap built on exactly the natural bases occurring in the P2-F source.

The required direction is:

```text
standard zeta zero
  -> finite zero-derived source identity
  -> source-connected nonnegative finite Gap/energy upper bound
  -> centered-coordinate lower bound.
```

Do not use the reverse direction

```text
centeredSigma = 0 -> Gap = 0
```

as a provider.

Do not identify two historical observables merely because their formulas look similar.

## 6. Third audit: finite multi-stage information

The zero-derived finite-plus-tail identity is available for every cutoff `K`, not only one cutoff.

It is therefore legitimate to inspect whether **several exact cutoff identities together** supply more usable information than one whole partial value.

Examples that may be audited include:

```text
P K
P (K+1)
P (K+2)
```

or a finite block of cutoff values, because their differences recover actual source terms.

However, any proposed weighted or quadratic certificate must still satisfy the A/B/C criteria above.  Merely recovering individual terms, whose natural decay already holds for every point in the open strip, is not a coordinate certificate.

Do not restart the old moving-frame block-margin route under new names.

## 7. Preferred theorem shape if a certificate exists

A successful result should be close to:

```lean
theorem centeredSigma_sq_le_finitePrimeCertificateRadius
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0)
    (K : ℕ) :
    centeredSigma s.re ^ 2 <= finitePrimeCertificateRadius K s := by
  ...
```

with a separate theorem

```lean
Tendsto (fun K => finitePrimeCertificateRadius K s) atTop (nhds 0)
```

and explicit nonnegativity.

The radius may initially be real-valued. Rational majorization belongs to the next stage, not this audit.

If the natural result is

```text
abs (centeredSigma s.re) <= r K s
```

that is equally acceptable.

## 8. Stop conditions

Stop and report rather than opening another long chain if any of the following is reached:

1. The candidate scalar is only a function of the whole P2-F sum/norm already audited in ZDI-006.
2. The upper bound on a positive modewise energy requires reversing triangle/Cauchy inequalities.
3. The candidate is the historical prime-mirror Gap but no zero-derived upper bridge exists.
4. Several cutoff identities yield only termwise decay valid for arbitrary open-strip points, with no extra zero-specific coordinate control.
5. A new predicate is equivalent to residual domination, no-cancellation, or RH.
6. The construction returns to positive-density/current-majorant geometry closed by ZDI-010.

If all natural candidates fail for information reasons, classify the result **O-INFORMATION** and state exactly what additional independent zero-derived identity would be required.

## 9. Decision after ZDI-011

### If A/B/C certificate exists

Proceed directly toward the DkReal route:

```text
finite scalar certificate
  -> centeredSigma^2 <= epsilon_K
  -> real radius -> rational majorant q_K
  -> nested shrinking intervals around 1/2
  -> DkReal uniqueness
  -> RiemannHypothesis.
```

Do not detour through moving frames.

### If O-INFORMATION

Treat that as a successful audit result.  The next research question is then not a sharper estimate of the same P2-F equality, but the search for one **additional independent zero-derived identity** capable of controlling a positive prime-coordinate scalar.

Candidate source families must be dependency-audited before implementation.

## 10. Certification requirements

For every new load-bearing declaration:

- characterization from existing source objects;
- realizability / non-vacuity where applicable;
- provenance from the standard zero or unconditional finite prime arithmetic;
- explicit classification if RH-equivalent;
- `#print axioms`;
- no `sorryAx`;
- focused build;
- `git diff --check`.

## 11. Deliverables

1. A narrow audit module only if actual Lean lemmas are needed.
2. `0022-ZDI-011-...-report.md` containing:
   - P2-F/Q2-F source recap;
   - explicit closure of ZDI-007..010 as a side obstruction;
   - inventory of independent zero-derived finite identities;
   - candidate positive scalar certificates and their A/B/C status;
   - exact source bridge to historical prime-mirror Gap if one exists;
   - information-loss/cancellation obstruction if it does not;
   - final classification: `CERTIFICATE-CANDIDATE`, `O-INFORMATION`, or a more precise named obstruction;
   - the single smallest next mathematical obligation.
3. No new positive-density schedule, fixed-block projection transport, residual-domination predicate, or RH provider.
