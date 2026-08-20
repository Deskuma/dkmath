# ZDSS-003 — source-matched positive scalar / centered-coercivity exploratory audit instructions

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Parent roadmap: `0000-RH-CFBRC-zero-derived-second-source-roadmap.md`

Depends on:

- `0002-ZDSS-001-zero-derived-source-rank-independence-audit-report.md`
- `ZeroDerivedPrimeCoordinateSourceRankAudit.lean`
- `EtaCriticalMirrorPrimeFactorFiniteSourceBridge.lean`
- `EtaCriticalMirrorPrimeFactorCoordinateCertificateReentryAudit.lean`
- historical finite mirror-energy / Gap modules only as audited candidate material

## 0. Route transition

ZDSS-001 ended with:

```text
INDEPENDENT-SOURCE-FOUND
```

The same nonreal standard nontrivial zeta-zero hypothesis supplies two separately controlled ordinary paired-Eta endpoint sources:

```text
A_K(s) := etaPairedPartial K s
B_K(s) := etaPairedPartial K (criticalMirror s)
```

with separate exact zero-derived tail identities and separate explicit power bounds.

P2-F is only the antisymmetric projection

```text
P2F_K(s) = B_K(s) - A_K(s).
```

The projection from the endpoint pair to the difference is not injective, so the endpoint pair contains proof information not recoverable from the P2-F whole value alone.

Because the independent pair has already been found, the roadmap's originally anticipated ZDSS-002 search for a new external dual finite source is not the immediate task. This checkpoint proceeds to the source-matched positive-scalar / centered-coordinate question.

Do not reopen the old source-rank inventory unless a concrete obstruction in this checkpoint forces a return to source selection.

## 1. Purpose of this checkpoint

This is an exploratory research-and-implementation task, not a theorem script with a predetermined final lemma.

Codex must inspect the current repository, compare multiple mathematically natural scalar constructions, reason about what information each construction preserves or destroys, and implement the strongest exact Lean results that can be justified from existing source objects.

The central research question is:

> Can the two separately zero-controlled endpoint sources be combined into a nonnegative finite scalar whose smallness is zero-derived and whose size also carries an unconditional quantitative trace of the centered horizontal coordinate `centeredSigma s.re`?

The desired architecture remains schematic:

```text
standard nontrivial zeta zero
  -> separately controlled endpoint pair (A_K, B_K)
  -> source-matched positive scalar E_K
  -> centered-coordinate lower information
  -> shrinking bound for centeredSigma
```

The checkpoint need not complete every arrow. It should determine as much of the architecture as the actual repository mathematics supports.

## 2. Fixed inherited source facts

Treat the following as the primary accepted starting point.

For

```lean
hs : NontrivialRiemannZetaZero s
him : s.im ≠ 0
```

ZDSS-001 proves:

```lean
etaPairedPartial K s = -etaPairTail K s
```

and

```lean
etaPairedPartial K (criticalMirror s)
  = -etaPairTail K (criticalMirror s).
```

It also proves separate norm upper bounds of the form

```text
||A_K(s)||
  <= ||s|| * K^(-s.re) / s.re
```

and

```text
||B_K(s)||
  <= ||criticalMirror s||
       * K^(-(criticalMirror s).re)
       / (criticalMirror s).re.
```

The same module classifies mirror, conjugation, and `1-s` transports of P2-F as duplicate information and classifies consecutive-cutoff subtraction as unconditional term recovery.

Do not count those transforms again as new source coordinates.

## 3. Research discipline

### 3.1 Do not choose the answer before inspecting the source geometry

The examples in this document are candidate families, not mandatory definitions.

Do not begin by defining the scalar that would make the desired theorem easy to state. First inspect:

- the exact finite endpoint formulas;
- the prime-factor mode formulas underlying each endpoint;
- existing mirror-energy / Gap formulas;
- exact conjugation and critical-mirror relations;
- any source-matched cross terms already present;
- any useful finite Hermitian or polarization identities already in DkMath / Mathlib;
- whether the endpoint pair naturally lives in a better coordinate basis than `(A_K,B_K)`.

Codex is expected to make a mathematical judgment about which observable has the best chance of preserving horizontal information.

### 3.2 Separate upper control from coercive lower information

For every candidate scalar, keep these questions separate:

```text
U-side:
  Is E_K nonnegative?
  Is E_K finite and source-derived?
  Does the zero hypothesis give E_K <= upper_K?
  Does upper_K -> 0?

C-side:
  Does E_K detect centeredSigma?
  Is there an unconditional lower bound involving centeredSigma^2?
  Does the coefficient remain quantitatively useful as K grows?
```

A candidate that solves only one side is still worth recording accurately.

### 3.3 Do not infer modewise energy from whole-source smallness

ZDSS-001 gives two whole endpoint values, not automatic control of every internal mode.

Therefore remain alert to invalid passages such as:

```text
||sum a_k|| small -> sum ||a_k||^2 small
||sum b_k|| small -> sum ||b_k - a_k||^2 small
```

unless an additional exact theorem supplies the missing information.

The existence of two endpoint sources removes the old one-difference information loss, but it does not automatically remove cancellation inside each endpoint sum.

### 3.4 Do not assume that the historical primeMirrorEnergy is the right scalar

Historical positive energies and aggregate mirror Gaps are valuable comparison targets because they already detect the horizontal coordinate.

However, they are admissible here only through exact source-preserving bridges.

A new scalar built directly from the endpoint pair may be preferable if it has a cleaner zero-derived upper bound.

## 4. Candidate scalar families to investigate

The following list is deliberately non-exclusive. Codex should inspect these and may introduce a better source-matched candidate if the repository structure suggests one.

### Candidate A — total endpoint energy

```text
E_total(K,s) := ||A_K(s)||^2 + ||B_K(s)||^2
```

This is the simplest positive scalar with immediate separate-source upper control.

Questions to audit:

- prove nonnegativity;
- derive the strongest explicit zero-derived upper bound from the two endpoint power bounds;
- prove convergence to zero for a nontrivial zero;
- determine whether any unconditional lower theorem involving `centeredSigma s.re` exists;
- determine whether such a lower theorem would require information absent from whole endpoint values.

Do not assume that total endpoint energy detects the critical line merely because the two endpoint exponents are mirror exponents.

### Candidate B — endpoint norm imbalance

Examples include:

```text
(||A_K|| - ||B_K||)^2
```

or an algebraically cleaner equivalent.

This candidate is naturally sensitive to asymmetry between `s.re` and `1 - s.re`, but its usefulness is not known.

Audit whether the available zero-derived bounds are sufficiently two-sided to control it. Upper bounds alone may be too weak to infer an asymmetry theorem.

### Candidate C — cross-correlation / polarization scalar

Inspect quantities involving

```text
Re (A_K * conj B_K)
```

or Hermitian combinations such as

```text
||A_K - B_K||^2
||A_K + B_K||^2
```

and their polarization identities.

The purpose is to test whether the missing centered information is carried by a cross term rather than by the diagonal endpoint energies.

P2-F already gives `B_K - A_K`, so any scalar depending only on that one projection is old information. A useful cross-correlation theorem must exploit the separately available endpoint coordinates.

### Candidate D — source-matched mode energy

Inspect whether the exact finite prime-factor representation of each endpoint permits a positive scalar whose modewise upper control is genuinely supplied by the separate endpoint zero identities, rather than inferred from whole-sum smallness.

This may involve a new exact decomposition, orthogonality identity, finite Gram form, or another source-derived structure.

Do not force this candidate if the current endpoint identities still leave mode cancellation uncontrolled.

### Candidate E — K-weighted or normalized dual-source scalar

The two source upper bounds decay with mirror exponents approximately governed by `s.re` and `1 - s.re`.

It is legitimate to investigate carefully chosen K-dependent weights or normalizations if they arise naturally from the exact source bounds or finite arithmetic representation.

However, audit whether the weighting merely inserts the centered coordinate by hand. A normalization is meaningful only if its definition and useful inequalities have source provenance independent of the desired RH conclusion.

### Candidate F — comparison with historical mirror Gap / energy

Search for exact finite identities or inequalities connecting the endpoint pair, its source-matched scalar, and historical objects such as:

```text
primeMirrorEnergy
cfzpAggregateMirrorGapUpTo
```

or related finite Gap / Beam objects.

The direction of interest is from endpoint-source data toward a positive horizontal detector.

Do not use a theorem whose hypothesis already expresses the collapse or vanishing needed for RH.

## 5. Repository research expected from Codex

Before deciding the implementation target, search the repository broadly enough to identify relevant existing APIs.

At minimum inspect declarations related to:

```text
etaPairedPartial
etaPairTail
etaPairTerm
etaPrimeFactorMirrorDefectPairTerm
primeMirrorEnergy
MirrorGap
AggregateMirrorGap
UnitGap
centeredSigma
criticalMirror
Hermitian / inner-product / norm-square identities
finite prime-factor logarithm representations
```

Also inspect the ZDSS-001 report's warning that an existing endpoint-Gap-to-UnitGap proposition is RH-equivalent under the current endpoint limits.

Do not import that proposition as a provider. Instead understand exactly why it is equivalent and whether a weaker unconditional theorem exists nearby.

Codex may inspect historical CFZP / PPW / IPSM modules as a fact ledger. Historical numbering or later placement does not make a declaration trusted automatically; classify dependency and provenance before using it.

## 6. Mathematical reasoning tasks

The implementation report must include explicit reasoning on the following questions even if some answers are negative or unresolved.

### 6.1 What is the smallest natural positive scalar actually controlled by ZDSS-001?

Determine this from the implemented endpoint inequalities, not from the desired final theorem.

### 6.2 What information about `s.re` is visible in that scalar before using the zero hypothesis?

Distinguish exact algebraic dependence from asymptotic guesses.

### 6.3 Does the centered coordinate appear in a diagonal term, a cross term, a ratio, a rate imbalance, or only after descending to mode coordinates?

Trace this explicitly.

### 6.4 Is any candidate coercivity statement already RH-equivalent?

If a statement combined with existing endpoint convergence immediately yields `s.re = 1/2` for every standard nontrivial zero, that alone does not make the statement invalid, but it makes it load-bearing enough that its provenance must be audited with exceptional care.

Do not reject such a theorem merely because it would prove RH if it can be proved unconditionally from fixed arithmetic source facts. Do reject using it as an assumed provider or encoding it as a definition.

### 6.5 Can the two-source structure eliminate the old cancellation firewall in any restricted source-matched subspace?

The generic whole-sum countermodel lives in a large arbitrary coordinate space. The actual endpoint pair arises from a specific Eta / prime-factor manifold.

It is legitimate to investigate whether exact source relations restrict that manifold enough to permit a coercive theorem that is false for arbitrary complex vectors.

If so, the restriction must be a proved theorem about the actual source family, not an informal intuition.

## 7. Preferred implementation style

Prefer one narrow audit module if concrete Lean results emerge, for example a name in the family:

```text
ZeroDerivedDualEndpointPositiveScalarCoercivityAudit.lean
```

The exact name may be adjusted to match the strongest result actually obtained.

Avoid creating a large stack of speculative modules before the main candidate is understood.

Useful theorem classes may include:

```text
nonnegativity
exact scalar characterization
zero-derived explicit upper bound
Tendsto upper bound -> 0
exact polarization / cross-term identity
comparison to existing mirror Gap / energy
unconditional centered-coordinate lower estimate
counterexample / non-injectivity / information obstruction
```

Implement only statements that materially clarify the candidate geometry.

## 8. Exploratory continuation boundaries

This checkpoint is intentionally not governed by a rigid mechanical stop list.

Codex should continue investigating nearby exact formulations when an initial candidate fails, especially when the failure suggests a closely related scalar, basis change, cross term, normalization, or source decomposition that preserves the same accepted endpoint provenance.

The following are strong warning boundaries rather than automatic termination commands:

- a candidate collapses to a function of P2-F alone;
- a proposed positive energy requires an invalid reverse inequality;
- a theorem is merely a restatement of `centeredSigma = 0`;
- an apparent provider is known to be RH-equivalent and is not independently proved;
- a definition inserts the desired shrinking radius or lower bound by construction;
- a dependency introduces `sorryAx` or an unrealizable hypothesis;
- the work drifts into the already closed ZDI-007..010 positive-density/current-majorant route.

When one of these appears, do not blindly continue that exact formulation. First ask whether the obstruction is specific to the candidate or reveals a broader information barrier. It is acceptable to reformulate and test a nearby source-matched candidate within the same checkpoint.

If several materially different natural candidates have been audited and they converge on the same obstruction, then record that obstruction clearly rather than multiplying variants indefinitely.

No fixed number of candidate attempts is prescribed.

## 9. What counts as progress

Any of the following may be a meaningful ZDSS-003 result:

```text
POSITIVE-SCALAR-UPPER-CLOSED
CENTERED-COERCIVITY-FOUND
SOURCE-MATCHED-CROSS-TERM-FOUND
MODE-ENERGY-BRIDGE-FOUND
RATE-ASYMMETRY-CANDIDATE
PARTIAL-COERCIVITY
NEW-INFORMATION-OBSTRUCTION
RH-EQUIVALENT-FRONTIER-IDENTIFIED
```

These labels are examples, not a mandatory enum.

The report should choose a classification that accurately describes the strongest proved mathematical state.

Do not force a binary success/failure classification if the result is genuinely intermediate.

## 10. If a centered-coordinate lower theorem is found

If Codex obtains an unconditional theorem of the schematic form

```text
lowerWeight K s * (centeredSigma s.re)^2 <= E K s
```

or an equivalent absolute-coordinate inequality, immediately audit:

- exact hypotheses;
- positivity / nondegeneracy of `lowerWeight`;
- asymptotic behavior of the quotient against the zero-derived upper bound;
- whether any hidden assumption is RH-equivalent;
- whether the theorem is genuinely unconditional on the horizontal location.

Do not jump directly to a final RH theorem in this checkpoint unless the instruction is explicitly extended later.

Instead, report whether the result is strong enough to make the DkReal completion route mechanically plausible.

## 11. If only upper control is found

If the endpoint pair yields a clean positive scalar with zero-derived convergence but no source-derived centered lower bound, preserve that as accepted Core if useful.

Then identify where the horizontal information is lost:

```text
whole endpoint aggregation
mode summation
missing cross correlation
missing lower estimate
vanishing coefficient
rate-only information
```

or another more precise obstruction.

A precise obstruction is preferable to an artificial provider.

## 12. Axiom and validation requirements

For every new load-bearing theorem:

- inspect `#print axioms`;
- no `sorryAx`;
- use only accepted source declarations or classify any frontier dependency explicitly;
- run focused `lake build`;
- run `./lean-build.sh` for the new module if applicable;
- run `lake build DkMath.RH` if the public import surface changes;
- run `git diff --check`.

If a new public module contains accepted reusable source facts, add it to `DkMath/RH.lean`; otherwise leaving an exploratory module unexported is acceptable when that better reflects its status.

## 13. Deliverables

Produce:

1. a focused Lean audit module if the investigation yields concrete reusable or obstruction theorems;
2. `0004-ZDSS-003-...-report.md` describing:
   - repository APIs inspected;
   - candidate scalars considered;
   - exact U-side status for each serious candidate;
   - exact C-side status for each serious candidate;
   - any cross-term / mode-energy / normalization insight;
   - any RH-equivalent frontier encountered;
   - the strongest accepted theorem chain;
   - unresolved mathematical gap;
   - recommended next checkpoint based on the evidence rather than on the original roadmap numbering;
3. validation results and axiom audits.

The report should distinguish clearly between:

```text
Lean-proved fact
repository-derived inference
mathematical heuristic / conjectural direction
```

## 14. Research attitude for this checkpoint

The purpose is to let the actual two-source structure answer the question.

Do not assume that the correct scalar is already known.
Do not assume that the historical Gap is the correct target.
Do not assume that a short proof cannot exist.
Do not assume that every candidate failure closes the whole route.

At the same time, do not confuse repeated reformulations with new information.

The guiding question is:

> What positive quantity can the zero hypothesis genuinely make small now that both endpoint coordinates are available, and where exactly does the centered horizontal displacement enter that same quantity?
