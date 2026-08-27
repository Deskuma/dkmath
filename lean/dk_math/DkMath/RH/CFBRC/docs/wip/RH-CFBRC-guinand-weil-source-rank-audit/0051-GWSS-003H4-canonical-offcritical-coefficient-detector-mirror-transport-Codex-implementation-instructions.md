# GWSS-003H4 canonical off-critical coefficient / detector mirror transport — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0050-GWSS-003H3-mirror-mellin-matrix-extractor-row-transport-report.md`

## 0. Mission

GWSS-003H3 closed H5 at the finite actual-window Mellin matrix level.  In particular, for the canonical mirror index `μ` and the canonical inverse-matrix extractor row `r_j`, the current branch now proves

```text
q_(μ j) = conj(q_j)
r_(μ j) = conj(r_j)
```

with no row permutation and no target `q.im` factor hidden in the extractor theorem.

GWSS-003H4 is H6 only.

Introduce the **canonical off-critical coefficient row** obtained by multiplying the canonical extractor row by the target squared-orbit imaginary coordinate, and prove its exact critical-mirror transport.  Also close the corresponding finite detector scalar / canonical detector extraction identities.

The expected coefficient law is

```text
cOff(μ j) = -conj(cOff(j))
```

but this must be derived from the current APIs, not asserted from heuristic sign counting.

The expected detector scalar law is

```text
Detector(μ j) = -Detector(j)
```

using both the sign change of `q.im` and the already-proved mirror invariance of the multiplicity-weighted mass.

Stop after the coefficient-row and detector-level transport is closed.

Do **not** transport the synthesized whole witness feature, WholeSource, finite arithmetic approximant, shifted energies, P1/P2 inequalities, or any positivity provider in this stage.  Those belong to H7 or later.

Do not start GWSS-004, Guinand--Weil, Weil positivity, Li criterion, infinite-height limits, arithmetic cutoff limits, or RH.

## 1. Required files to inspect first

Read the current branch versions of at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinOffCriticalWitnessAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean
```

Also inspect the exact canonical extractor and mass APIs before introducing duplicate lemmas.

Known load-bearing declarations include:

```text
pascalCenteredXiSquaredOrbitMirrorIndex_spec
pascalCenteredXiSquaredOrbitMirrorIndex_involutive
pascalCenteredXiMellinCanonicalExtractorRow
pascalCenteredXiMellinCanonicalExtractorRow_extracts
pascalCenteredXiMellinCanonicalExtractorRow_mirror
pascalCenteredXiSquaredOrbitMass_conj
pascalCenteredXiSquaredOrbitMassVec
pascalCenteredXiMellinMomentVec_eq_mellinEvaluation_mulVec_massVec
exists_pascalCenteredXiMellin_offCritical_detector_coefficients
pascalCenteredXiMellinWitnessWeight_moment_eq
```

The existing existential off-critical coefficient theorem is useful for comparison, but do not reuse an arbitrary existential witness as though it were the canonical row.

## 2. H6-A — canonical target imaginary scalar

Expose the target squared-orbit imaginary scalar if useful.  A minimal helper may be

```lean
noncomputable def pascalCenteredXiSquaredOrbitImaginaryScalar
    (R : ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) : ℂ :=
  ((pascalCenteredXiSquaredOrbitCoordinate R j).im : ℂ)
```

A helper definition is optional if direct expressions remain readable.

Prove the exact mirror sign law

```text
qIm(μ j) = -qIm(j)
```

from `pascalCenteredXiSquaredOrbitMirrorIndex_spec` and ordinary complex conjugation.  This is elementary geometry and does not constitute new source rank.

Do not assume off-criticality here.  The sign identity should hold for every finite carrier index, including a self-mirror critical-line orbit where both sides are zero.

## 3. H6-B — canonical off-critical coefficient row

Define the canonical coefficient row explicitly from the canonical inverse extractor row:

```lean
noncomputable def pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
    (R ε : ℝ)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun i =>
    ((pascalCenteredXiSquaredOrbitCoordinate R j).im : ℂ) *
      pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i
```

Name may be shortened only if it remains clearly canonical and target-dependent.

This is a definition, not a new existence theorem.

## 4. H6-C — coefficient-row critical-mirror law

Under the same hypotheses needed for the H5 extractor-row mirror theorem (`0 < ε` and `det H ≠ 0`), prove entrywise

```text
cOff(μ j, i) = -conj(cOff(j, i))
```

and preferably also the function equality

```text
cOff(μ j) = fun i => -conj(cOff(j, i)).
```

The proof must visibly use both independent ingredients:

```text
qIm(μ j) = -qIm(j)
r_(μ j) = conj(r_j)
```

Be careful with coercion of the real imaginary part into `ℂ`: its conjugate is itself.  Do not accidentally turn `-conj(c)` into merely `-c`.

This theorem is the load-bearing H6 coefficient statement.

## 5. H6-D — canonical mirror mass-vector equality

GWSS-003H2 proved conjugate-orbit mass invariance and an existential mirror index with equal mass.  H5 subsequently introduced a **canonical** mirror index.

Add the direct canonical-index theorem if not already available:

```text
pascalCenteredXiSquaredOrbitMassVec R
    (pascalCenteredXiSquaredOrbitMirrorIndex R j)
  = pascalCenteredXiSquaredOrbitMassVec R j
```

Derive it from the canonical mirror coordinate specification plus `pascalCenteredXiSquaredOrbitMass_conj`; do not identify the H4 existential chosen index with the H5 canonical index by choice irrelevance.

## 6. H6-E — canonical detector scalar and oddness

Use either a named definition or direct expression for the finite detector scalar

```text
Detector(j) := ((q_j.im : ℂ) * massVec(j)).
```

Prove the exact mirror law

```text
Detector(μ j) = -Detector(j).
```

This theorem should require no `det H ≠ 0` hypothesis: it is a finite orbit/mass identity independent of the Mellin inversion machinery.

Do not weaken it to a norm equality.  The sign is the information needed later.

Also record, if useful, the immediate self-mirror consequence

```text
μ j = j → Detector(j) = 0
```

but do not promote this presentation statement into an RH claim.  For actual off-critical coordinates, H2/H5 geometry already prevents self-mirroring through nonzero imaginary squared coordinate; reuse existing facts rather than opening a new geometry subproject.

## 7. H6-F — canonical detector extraction identity

The project currently has an existential theorem that scales an existential coordinate extractor by `q.im`.  H6 should provide the canonical counterpart.

Under

```text
0 < ε
det (pascalCenteredXiMellinEvaluationMatrix R ε τ) ≠ 0
```

prove

```text
∑ i,
  pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j i *
    pascalCenteredXiMellinMomentVec R ε τ i
  =
  ((pascalCenteredXiSquaredOrbitCoordinate R j).im : ℂ) *
    pascalCenteredXiSquaredOrbitMassVec R j.
```

Preferred proof route:

```text
momentVec = H *ᵥ massVec
canonical extractor row extracts coordinate j
multiply the extraction identity by q_j.im
finite distributivity
```

Do not route through `exists_pascalCenteredXiMellin_offCritical_detector_coefficients`; the point of this stage is to expose the same detector using the canonical row now available from H5.

## 8. H6-G — paired canonical detector extraction

Combine H6-C/H6-E/H6-F to record the finite paired mirror endpoint if it is clean:

```text
canonicalDetectorExtraction(μ j)
  = -canonicalDetectorExtraction(j)
```

The strongest acceptable theorem is an equality of the two finite sums, for example

```text
(∑ i, cOff(μ j,i) * momentVec i)
  = -(∑ i, cOff(j,i) * momentVec i).
```

It is acceptable to prove this by rewriting both sums through the canonical detector extraction theorem and then applying detector oddness.  There is no need yet to prove a conjugation law for `momentVec` or synthesized witness functions.

This distinction is deliberate: coefficient transport and detector extraction are H6; whole-feature conjugation is H7.

## 9. Required firewalls

### Firewall A — `-conj(c)` is not `-c`

The expected canonical coefficient law contains complex conjugation.  Do not simplify it away unless a separate real-valuedness theorem for the row is actually proved.  No such real-valuedness should be assumed.

### Firewall B — canonical row only

Do not compare arbitrary witnesses returned by `exists_matrix_coordinate_extractor` or `exists_pascalCenteredXiMellin_offCritical_detector_coefficients`.  H5 created a canonical inverse row precisely to make transport meaningful.

### Firewall C — mass symmetry is not extractor symmetry

Use H5 for extractor transport and H4/H6-D for mass transport.  Keep their proof roles separate.

### Firewall D — no positivity

Detector oddness is a signed equality, not a P1 inequality and not a positivity provider.

### Firewall E — no whole-feature claim

Do not infer

```text
WitnessWeightMirror = -conj(WitnessWeight)
WholeSourceMirror = ...
D1Mirror = ...
DIMirror = ...
```

in this stage.  The synthesized feature also contains the Mellin basis functions evaluated at the running variable; that transport belongs to H7 and must be checked separately.

### Firewall F — finite stage only

No `X → ∞`, `T → ∞`, `ε → 0`, limit exchange, or asymptotic identification.

### Firewall G — symmetry is not independent rank

The mirror detector is transported information.  Do not count it as a second independent source.

## 10. Preferred implementation location

Preferred new module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean
```

Import H5 and only the minimum additional modules needed.

If it is materially cleaner to add one very small public helper to an upstream module, do so only when it is genuinely presentation-level and reusable.  Report every such upstream edit.

## 11. Primary classification

Choose the strongest accurate primary classification from:

```text
MIRROR-OFFCRITICAL-COEFFICIENT-NEG-CONJ-CLOSED
MIRROR-DETECTOR-SCALAR-ODDNESS-CLOSED
MIRROR-CANONICAL-DETECTOR-EXTRACTION-CLOSED
MIRROR-OFFCRITICAL-COEFFICIENT-TRANSPORT-GAP
MIRROR-CANONICAL-DETECTOR-EXTRACTION-GAP
```

If all H6 items above close, prefer

```text
MIRROR-CANONICAL-DETECTOR-EXTRACTION-CLOSED
```

and list `MIRROR-OFFCRITICAL-COEFFICIENT-NEG-CONJ-CLOSED` and `MIRROR-DETECTOR-SCALAR-ODDNESS-CLOSED` as secondary classifications.

Do not use an RH/off-critical-exclusion classification in H6.

## 12. Expected closeout report

Create

```text
0052-GWSS-003H4-canonical-offcritical-coefficient-detector-mirror-transport-report.md
```

The report must state explicitly:

1. the exact canonical coefficient-row mirror formula;
2. the exact canonical mass-vector mirror formula;
3. the detector scalar mirror formula;
4. the canonical detector extraction identity;
5. whether paired finite detector sums are exact negatives;
6. that no whole-feature / shifted-energy transport was attempted;
7. that no positivity provider or independent source was obtained;
8. that GWSS-004 was not started.

## 13. Verification

If a module is created or modified, run at minimum:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit
git diff --check
```

Run `#print axioms` on the load-bearing public declarations, especially:

```text
canonical off-critical coefficient mirror theorem
canonical mass-vector mirror theorem
detector scalar oddness theorem
canonical detector extraction theorem
paired detector extraction theorem, if added
```

Expected baseline only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new axiom.

## 14. Decision after H6

If H6 closes exactly as expected, the next bounded stage is H7:

```text
canonical synthesized witness / whole-feature critical-mirror transport
```

That stage must determine how the coefficient law `-conj(c)` combines with the Mellin basis conjugation law at the **running variable** and only then infer the transformation of WholeSource and the two shifted-energy polarization channels.

Do not pre-decide that both channels are odd.  The conjugation can make the real and imaginary channels transform differently.
