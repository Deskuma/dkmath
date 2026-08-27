# GWSS-003H4: canonical off-critical coefficient and detector transport report

## Scope

This checkpoint implements only the bounded H6 stage from 0051.  It uses the
canonical inverse Mellin extractor row from GWSS-003H3 and scales it by the
target squared-coordinate imaginary part.  The stage stops before synthesized
whole-feature transport, whole-source identities, shifted energies, P1/P2
inequalities, positivity, infinite limits, GWSS-004, and RH.

## H6-A: target imaginary scalar

`pascalCenteredXiSquaredOrbitImaginaryScalar` packages
`((coordinate R j).im : ℂ)`.  The theorem
`pascalCenteredXiSquaredOrbitImaginaryScalar_mirror` proves the exact finite
geometry identity

```text
qIm (mirrorIndex j) = -qIm j.
```

It is unconditional in the finite carrier index; in particular, a
self-mirror index has zero imaginary scalar.

## H6-B/C: canonical coefficient row

`pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow` is defined by

```text
cOff(j, i) = qIm(j) * row(j, i).
```

The entrywise and function-level theorems
`pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror` and
`pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun` prove

```text
cOff(mirrorIndex j, i) = -conj(cOff(j, i)).
```

The proof visibly combines the imaginary-scalar sign law with the H5
canonical extractor-row conjugation law.  The complex conjugation is not
discarded or replaced by a real-valuedness assumption.

## H6-D/E: mass vector and detector scalar

`pascalCenteredXiSquaredOrbitMassVec_mirror` derives the canonical mass-vector
identity directly from the canonical coordinate specification and
`pascalCenteredXiSquaredOrbitMass_conj`:

```text
massVec (mirrorIndex j) = massVec j.
```

The canonical finite detector scalar is

```text
Detector(j) = qIm(j) * massVec(j).
```

`pascalCenteredXiMellinCanonicalDetectorScalar_mirror` proves the signed law

```text
Detector(mirrorIndex j) = -Detector(j).
```

This is an exact signed equality, not a norm equality or a positivity
statement.

## H6-F: canonical detector extraction

`pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_extracts` proves,
under positive box width and nonzero evaluation-matrix determinant,

```text
Σ i, cOff(j, i) * momentVec(i) = Detector(j).
```

The proof uses the actual finite identity
`momentVec = H *ᵥ massVec` and the canonical inverse-row extraction theorem;
it does not call the earlier existential off-critical coefficient theorem.

## H6-G: paired canonical detector extraction

`pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_paired_extracts_neg`
combines H6-F with detector oddness and proves the exact finite endpoint law

```text
Σ i, cOff(mirrorIndex j, i) * momentVec(i)
  = -(Σ i, cOff(j, i) * momentVec(i)).
```

No conjugation law for the running-variable moment basis is needed here.

## Classification and boundary

Primary classification:

```text
MIRROR-CANONICAL-DETECTOR-EXTRACTION-CLOSED
```

Secondary classifications:

```text
MIRROR-OFFCRITICAL-COEFFICIENT-NEG-CONJ-CLOSED
MIRROR-DETECTOR-SCALAR-ODDNESS-CLOSED
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

No whole-feature or shifted-energy transport was attempted.  No positivity
provider or independent source was obtained.  GWSS-004 was not started.

## Changed files

* `DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean`
* this report

No upstream predecessor module required an edit.  No `sorry`, `admit`,
`native_decide`, or new axiom was added.  No commit, push, PR operation, or CI
result is claimed by this report.

## Verification

The focused module was checked with:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit
git diff --check
```

The load-bearing public declarations were checked separately with `#print
axioms`; each reports only the baseline `[propext, Classical.choice,
Quot.sound]`.
