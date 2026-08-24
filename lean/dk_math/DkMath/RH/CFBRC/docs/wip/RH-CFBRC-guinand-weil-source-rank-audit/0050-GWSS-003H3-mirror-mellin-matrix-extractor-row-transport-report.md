# GWSS-003H3: mirror Mellin-matrix and extractor-row transport report

## Scope

This checkpoint implements only the bounded H5 stage from 0049.  It starts
from the finite critical-mirror and multiplicity-mass transport of GWSS-003H2
and audits the actual general-`τ` Mellin evaluation matrix.  It stops before
the `q.im` coefficient-row sign step, off-critical transport, whole-feature
transport, shifted energy, positivity, source-rank claims, infinite limits,
or RH.

## H5-A: weight conjugation

The new theorem
`centeredMellinSpectralWeight_centeredMellinBoxApprox_conj` proves

```text
W(conj z) = conj (W z)
```

from the exact finite logarithmic-average formula for the centered box.  The
theorem
`pascalCenteredXiMellinSecondDifferenceWeight_conj` then transports the
actual second-difference weight for every real `τ`, treating `τ = 0` through
the patched quadratic branch and `τ ≠ 0` through the finite kernel formula.
No Mellin continuation or limiting argument is used.

## H5-B: canonical mirror `Fin` permutation

`pascalCenteredXiSquaredOrbitCoordinate_injective` exposes injectivity of the
fixed coordinate presentation.  The new noncomputable
`pascalCenteredXiSquaredOrbitMirrorIndex` is selected from the existing
coordinate-existence theorem.  Its specification is conjugation of the
coordinate, and coordinate injectivity proves

```text
mirrorIndex (mirrorIndex j) = j.
```

The mirror index is not identified with `j`; representative choices remain
presentation data.

## H5-C: entrywise matrix column relation

`pascalCenteredXiSquaredOrbitRepresentativeFin_mirror_sq` proves the required
square relation.  Equality of squares, together with evenness of the actual
Mellin weight, removes the sign ambiguity of selected representatives.  The
entrywise theorem is
`pascalCenteredXiMellinEvaluationMatrix_mirror_entry`:

```text
H[i, mirrorIndex j] = conj (H[i, j]).
```

The row family `τ : Fin n → ℝ` is unchanged; there is no hidden row
permutation.

## H5-D: matrix/reindex relation

The public theorem
`pascalCenteredXiMellinEvaluationMatrix_mirror_columns_eq_conj` packages the
entrywise statement as the exact finite reindexing identity

```text
(fun i j => H[i, mirrorIndex j]) = (fun i j => conj (H[i, j])).
```

No separate permutation-matrix API was needed.  The entrywise identity is the
chosen matrix/reindex endpoint and fixes the orientation directly.

## H5-E: canonical inverse extractor row

`pascalCenteredXiMellinCanonicalExtractorRow` exposes the inverse row

```text
row(j, i) = H⁻¹[j, i].
```

Under `det H ≠ 0`,
`pascalCenteredXiMellinCanonicalExtractorRow_extracts` proves that this row
extracts coordinate `j` from `H *ᵥ m`.  The load-bearing transport theorem is
`pascalCenteredXiMellinCanonicalExtractorRow_mirror`:

```text
row(mirrorIndex j, i) = conj (row(j, i)).
```

It is derived by showing that the conjugated original row extracts the mirror
coordinate, then using injectivity of `vecMul` from matrix invertibility.  It
does not compare arbitrary existential extractor witnesses and does not
introduce a target `q.im` factor.

## Classification and boundary

Primary classification:

```text
MIRROR-EXTRACTOR-ROW-TRANSPORT-CLOSED
```

Secondary classification:

```text
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

The first remaining bounded item is H6: the off-critical coefficient-row
transport involving `q.im`.  That sign step is intentionally not present
here.  This stage contains no positivity provider, no independent source, no
finite-approximant identification, no limit exchange, and no RH statement.

## Changed files

* `DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean`
* `DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean`
* this report

No `sorry`, `admit`, `native_decide`, or new axiom was added.  No commit,
push, PR operation, or CI result is claimed by this report.

## Verification

The focused source file was checked with:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean
```

The load-bearing public declarations were checked separately with `#print
axioms`; each reports only the baseline `[propext, Classical.choice,
Quot.sound]`.  The required module-target build command and `git diff --check`
were also run after the implementation.
