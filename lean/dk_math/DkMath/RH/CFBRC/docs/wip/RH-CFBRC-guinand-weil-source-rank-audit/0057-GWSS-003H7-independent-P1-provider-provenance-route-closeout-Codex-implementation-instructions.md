# GWSS-003H7 independent P1 provider provenance / mirror-route closeout — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0056-GWSS-003H6-shifted-energy-mirror-parity-paired-dominance-collapse-report.md`

## 0. Mission

GWSS-003H2 through GWSS-003H6 have now closed the finite critical-mirror transport chain for the actual synthesized Mellin witness:

```text
orbit / multiplicity / mass
  -> canonical mirror index
  -> Mellin matrix column conjugation
  -> canonical inverse extractor-row conjugation
  -> canonical off-critical coefficient row: -conj
  -> detector scalar oddness
  -> vertical / top / whole-source transport
  -> finite arithmetic approximant transport
  -> shifted-energy difference parity
  -> paired-dominance consequences.
```

In particular, for the canonical target index `j` and mirror `μ j`, the branch now proves

```text
WholeSource(μ j) = -conj(WholeSource(j))
Δ1(μ j) = -Δ1(j)
ΔI(μ j) =  ΔI(j)
```

and

```text
Dom1(j) ∧ Dom1(μ j)  <->  WholeSource(j).re = 0
DomI(j) ∧ DomI(μ j)  <->  DomI(j).
```

The mirror route therefore supplies transport and, conditionally, an equality collapse.  It still does **not** supply either dominance premise.

GWSS-003H7 is H9 only.

Perform a bounded provenance audit for an **independent finite P1 provider** for the exact canonical synthesized witness.  Determine whether the current branch already contains a theorem that can establish

```text
E1-(c_j) <= E1+(c_j)
```

for every relevant canonical target `j`, from source-side data that is independent of the target's zero-side detector rewrite and independent of mirror transport itself.

If such a theorem exists, identify the exact theorem and prove only the smallest adapter needed to feed it into the H8 paired-collapse theorem.

If no such theorem exists, close the H-series mirror route with a precise provenance report:

```text
mirror transport: CLOSED
paired-collapse mechanism: CLOSED
independent canonical P1 provider: NOT FOUND
```

Do not start GWSS-004 merely because the mirror route is closed.

## 1. Source of truth and required inspection

Use the current GitHub branch as the source of truth.  Read at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessProviderDecisionAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideSignAudit.lean
```

Also read the historical provider decisions:

```text
0034-GWSS-003D-surviving-provider-decision-audit-report.md
0036-GWSS-003E-Gram-polarization-bridge-decision-report.md
0044-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-report.md
0054-GWSS-003H5-whole-source-mirror-conjugation-transport-report.md
0056-GWSS-003H6-shifted-energy-mirror-parity-paired-dominance-collapse-report.md
```

The historical reports contain gaps that were later closed.  Do not repeat stale classifications.  Re-evaluate every old gap against the current branch.

## 2. Exact target proposition

For

```text
n := pascalCenteredXiSquaredOrbitIndexCard R
c_j := pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j
```

with the usual finite hypotheses

```text
hε : 0 < ε
hτ : ∀ i, τ i ≠ 0
hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0
```

and finite `W`, `X`, define the target proposition only conceptually as

```text
CanonicalP1(j) :
  pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy ε τ c_j W X <=
    pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy ε τ c_j W X.
```

Prefer direct expressions or a private/local abbreviation.  Do not create a global provider structure unless an actual theorem needs a typed interface.

By the existing 003G theorem, this proposition is equivalent to

```text
0 <= (pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c_j W X).re.
```

By H8, applying the same proposition to `μ j` gives the opposite inequality at `j`, so a provider valid uniformly for both canonical endpoints would force equality.

The audit question is therefore not whether P1 would be useful.  H8 already answers that.  The question is whether current finite source data actually prove P1 without importing the conclusion through another name.

## 3. Provenance criteria for an admissible P1 provider

A candidate counts as an independent provider only if all of the following are satisfied.

### P1-a. Exact witness

The theorem applies to the **actual synthesized nonzero-`τ` canonical witness** `c_j`, not only the fixed `τ = 0` quadratic source feature and not only an arbitrary abstract scalar.

### P1-b. Full finite source

The theorem retains the actual finite vertical and top-horizontal source contributions used by

```text
pascalCenteredXiMellinGeneralTauWitnessWholeSource
```

or reaches the exact same quantity through a proved adapter.

### P1-c. Correct strength

It proves an order/sign/equality strong enough to derive `CanonicalP1(j)`.  Mere nonnegativity of `E1+` and `E1-` separately is P0, not P1.

### P1-d. Independent provenance

The proof must not obtain the sign by rewriting through the same zero-side detector moment, `q.im`, mirror oddness, H8 paired collapse, or a proposition already equivalent to the desired conclusion.

In particular, the following are transports/readouts, not independent providers:

```text
Δ1 = 4 * WholeSource.re
Δ1 = 2 * FiniteApproximant.im
Dom1 <-> 0 <= WholeSource.re
mirror WholeSource.re oddness
mirror Δ1 oddness
paired Dom1 <-> WholeSource.re = 0.
```

### P1-e. No forbidden equivalent assumption

Reject candidates whose hypothesis is RH, Li, full Weil positivity, an RH-equivalent raw-ratio bound, a zero-exclusion hypothesis equivalent to the desired result, or another already-unproved P1/P2/P3 provider.

### P1-f. Finite validity

No `T -> ∞`, `X -> ∞`, limit exchange, or same-zero-set window extension may be inserted.  The current audit is finite in `ε`, `τ`, `W`, and `X`.

### P1-g. Mirror independence

Critical-mirror symmetry itself cannot count as a second source.  It transports the same finite source data and H8 already proves exactly what it does to the order.

## 4. Required candidate audit

Audit at least the following classes and record exact declaration names and verdicts.

### Candidate A — shifted-energy P0 positivity

The actual-feature module proves all four shifted energies nonnegative.

Check whether any theorem goes beyond separate nonnegativity to an unconditional ordering for the canonical witness.

Expected warning:

```text
0 <= E+
0 <= E-
```

does not imply either `E- <= E+` or `E+ <= E-`.

The GWSS-003E counterexample already records this algebraic fact; reuse it if useful.

### Candidate B — fixed `τ = 0` Gram / quadraticization positivity

Inventory the source-side Gram energy, autocorrelation, whole-surface energy, shifted-energy order equivalences, and any sign theorems.

Distinguish two questions:

1. has H7/F-series now closed the old synthesized-witness **representation bridge**?  Yes, for the general-`τ` source/whole feature;
2. has it proved that the old fixed-`τ = 0` Gram positivity/order theorem supplies P1 for the target-dependent canonical synthesized witness?  This requires an exact theorem, not analogy.

Do not silently transfer a fixed-`τ = 0` sign statement to the synthesized finite linear combination.

### Candidate C — general-`τ` source representation

The F-series closes the actual source feature and finite arithmetic approximant representation.

Audit whether any declaration in that implementation proves a sign or order.  Complex linearity and exact representation alone are not P1.

### Candidate D — homogeneity / prime majorants

GWSS-003C proves first-order scalar transport and homogeneous norm/majorant bounds.

Check whether any later theorem breaks the `q.im` scalar cancellation in an independent way.  If not, retain the existing no-go verdict.

### Candidate E — phase / real-structure restrictions

GWSS-003B proves the universal complex-linear phase no-go.  H5-H7 later proved the actual canonical mirror-conjugation structure.

This closes some old API gaps, but do not confuse conjugation covariance with source sign.  Audit whether the new canonical real/conjugation transport actually proves `WholeSource.re >= 0`; H7 currently gives parity, not sign.

### Candidate F — critical mirror pairing

H4-H8 now provide the complete finite mirror transport.  Classify it explicitly as

```text
TRANSPORT / CONDITIONAL COLLAPSE, NOT INDEPENDENT P1 PROVIDER
```

unless a genuinely source-derived one-sided sign theorem appears elsewhere.

### Candidate G — finite/infinite source sign modules

Inspect `PascalCenteredXiPrimeSideSignAudit.lean`, whole-surface excess/defect modules, and nearby sign/dominance declarations.

Reject any theorem that only assumes eventual sign, asymptotic sign, a later-limit provider, or a different fixed feature.  Record exact reason.

### Candidate H — vanishing-scale / horizontal decay

Re-check whether any new finite theorem since 003D turned the weight-only decay contract into a full source theorem.  Do not authorize a fixed-window `T -> ∞` argument without a new same-zero-set-compatible theorem.

## 5. Repository search requirement

Search the current `DkMath/RH/CFBRC` tree for at least the concepts

```text
WholeSource
nonneg
positive
order
sign
dominance
shifted
energy
Gram
autocorrelation
excess
defect
coercive
```

and inspect any candidate that could apply to the actual canonical synthesized witness.

Search results alone are not proof of absence.  The report must explain why each plausible candidate fails one of P1-a through P1-g, or identify the exact theorem that passes them.

## 6. Allowed implementation outcome A — provider found

If a theorem passes all provenance criteria, do **not** expand scope.

Create a focused module, suggested name:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorP1ProviderAudit.lean
```

Prove only:

1. the smallest adapter from the existing theorem to `CanonicalP1(j)`;
2. the same adapter at `μ j` if the provider theorem is genuinely uniform;
3. by reusing H8, the conditional consequence

```text
WholeSource(j).re = 0
```

or the exact energy equality.

Then stop.

Do **not** identify this zero with `q.im = 0` unless an already-proved independent injectivity theorem directly supplies that implication.  Do not start RH.

Suggested classification if a genuine provider is found:

```text
INDEPENDENT-CANONICAL-P1-PROVIDER-FOUND
```

with a secondary classification describing the exact provider source.

## 7. Allowed implementation outcome B — provider not found

If no theorem passes P1-a through P1-g, do not manufacture a provider contract and do not add redundant Lean theorems already implied by H8.

A report-only closeout is acceptable and preferred.

Write:

```text
0058-GWSS-003H7-independent-P1-provider-provenance-route-closeout-report.md
```

The report must contain:

1. a table of all audited candidate classes;
2. exact current theorem names / modules;
3. whether each candidate addresses the exact canonical synthesized witness;
4. whether it includes the full finite source including top-horizontal contribution;
5. its strength (P0/P1/P2/P3/readout/transport);
6. independence verdict;
7. finite-vs-limit status;
8. explicit reason for rejection or acceptance.

If no provider is found, use primary classification:

```text
MIRROR-ROUTE-TRANSPORT-CLOSED-INDEPENDENT-P1-PROVIDER-NOT-FOUND
```

Secondary classifications should include, where supported:

```text
MIRROR-PAIR-CONDITIONAL-COLLAPSE-CLOSED
ACTUAL-SHIFTED-ENERGY-POLARIZATION-CLOSED
P0-POSITIVITY-NOT-P1
FIXED-TAU0-GRAM-NOT-CANONICAL-P1
GENERAL-TAU-REPRESENTATION-NOT-SIGN
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
GWSS-004-UNAUTHORIZED
```

## 8. Historical-gap reconciliation

The 0034 and 0036 reports predate H4-H8.  The H9 report must explicitly reconcile at least these historical items:

```text
old: actual zero-window conjugation symmetry API GAP
now: closed by H4/H5-era finite critical-mirror work

old: synthesized coefficient real/conjugation structure NOT FOUND
now: canonical extractor/coefficient mirror transport closed by H5/H6

old: target-witness source-feature bridge GAP
now: actual general-τ source / WholeSource representation closed by F-series

old: independent shifted-energy dominance NOT FOUND
now: re-audit required; H8 only gives parity and conditional collapse, not a premise.
```

Do not leave stale gap language in the final route status.

## 9. Forbidden shortcuts / firewalls

Do not use or assume:

```text
RiemannHypothesis
Li criterion
classical Weil positivity / Weil criterion as a provider
Guinand--Weil as an assumed sign theorem
RH-equivalent raw-ratio bounds
zero-side moment sign rewritten as source sign
mirror transport as an independent source
P0 nonnegativity as P1 dominance
fixed-τ = 0 positivity silently generalized to arbitrary synthesized τ
T -> ∞
X -> ∞
limit interchange
new same-zero-set window extension
```

No DkReal detour, eta-tail detour, moving-line collision detour, or unrelated zero-exclusion route is authorized.

## 10. Verification

If a Lean module is added or edited, run at minimum:

```text
lake env lean <focused-module>
lake build <focused-module>
git diff --check
```

Run `#print axioms` on every new load-bearing theorem.  Expected footprint is baseline only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new axiom.

If the outcome is report-only, still run `git diff --check` and verify that every declaration cited in the report exists on the current branch.

## 11. Stop condition

Stop H9 immediately when either:

```text
A. one exact finite independent canonical P1 provider is found and minimally adapted;
```

or

```text
B. the bounded current-tree provenance audit establishes that no current candidate passes P1-a through P1-g.
```

In case B, H2-H8 remain successful finite transport results, but the mirror route is closed as a transport mechanism rather than a proof-producing source of P1.

Do not proceed to GWSS-004 in the same change.