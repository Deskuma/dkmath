# GWSS-003H5: whole-source mirror conjugation transport report

## Scope

This checkpoint implements the bounded H7 stage from 0053. It transports the
H6 canonical off-critical coefficient row through the actual finite source
surface. All identities retain the finite window `W` and finite arithmetic
cutoff `X`. No shifted energy, positivity, source-rank claim, limit, GWSS-004
statement, or RH statement is introduced.

## Implemented module

The focused implementation is

`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean`.

The exact hypotheses are separated as follows:

* `hε : 0 < ε` and `hdet : det (evaluationMatrix R ε τ) ≠ 0` are used by the
  canonical coefficient transport and all source-level mirror theorems.
* `hτ : ∀ i, τ i ≠ 0` is used only by the existing normalized logarithmic-box
  representation and therefore appears only in the normalized whole-feature
  integral theorem.
* `W` is a finite residue-transport window and `X : ℕ` remains a fixed finite
  arithmetic cutoff.

## H7-A: witness-weight transport

`pascalCenteredXiMellinCanonicalWitnessWeight_mirror` proves

```text
h_(μ j)(z) = -conj (h_j (conj z)).
```

The equivalent conjugate-argument form is also exported. The proof uses the
H6 coefficient law `c_(μ j) = -conj(c_j)` and the H5 all-real-`τ` basis-weight
conjugation theorem; it does not require nonzero selected dilations.

## H7-B/C: vertical source

The existing exact finite geometry helpers are reused:

```text
RightEdgeNode W (-t)       = conj (RightEdgeNode W t)
VerticalAmplitude W X (-t) = conj (VerticalAmplitude W X t).
```

The latter includes the finite PHZ/von-Mangoldt cutoff, archimedean term, and
elementary correction. The implementation visibly applies the symmetric
interval substitution `t ↦ -t` and proves

```text
V_(μ j) = -conj (V_j).
```

The logarithmic-box refinement is also closed:

```text
VerticalAggregatedFeature_(μ j)(u)
  = -conj (VerticalAggregatedFeature_j(u)).
```

## H7-D/E: top source

The totalized centered-Xi negative logarithmic derivative is transported using
the existing conjugation and oddness APIs, together with

```text
TopNode W (1-x)      = -conj (TopNode W x)
TopAmplitude W (1-x) = -conj (TopAmplitude W x).
```

The finite affine substitution `x ↦ 1-x` then gives

```text
T_(μ j) = conj (T_j).
```

The corresponding feature law retains the running-variable reflection:

```text
TopAggregatedFeature_(μ j)(u)
  = conj (TopAggregatedFeature_j(-u)).
```

Thus the pointwise whole-box law is genuinely mixed, not a simple same-`u`
Schwarz law:

```text
WholeFeature_(μ j)(u)
  = -conj (VerticalFeature_j(u))
    - I * conj (TopFeature_j(-u)).
```

This is recorded by
`pascalCenteredXiMellinCanonicalWholeBoxFeature_mirror`; no unjustified
evenness in `u` is assumed.

## H7-F/G: whole source and approximant

Using the finite orientation convention
`WholeSource = VerticalSource - I * TopSource`, the module proves

```text
S_(μ j) = -conj (S_j)
A_(μ j) =  conj (A_j).
```

The finite approximant law uses the existing exact ledger
`A_j = 2 * I * S_j`; the conjugation of `I` is handled explicitly by the
finite algebraic proof.

The exported channel theorems record the exact parity table:

```text
                 real channel   imaginary channel
WholeSource           odd              even
Approximant           even              odd
```

These are finite equalities only, not positivity or dominance statements.

## H7-H: normalized feature integral

With `hτ`, the existing finite normalized whole-source representation gives

```text
((2*ε)⁻¹ : ℂ) * ∫ WholeFeature_(μ j)(u) du
  = -conj (((2*ε)⁻¹ : ℂ) * ∫ WholeFeature_j(u) du).
```

This conclusion is a finite integral transport identity. It does not use an
infinite-height or cutoff limit.

## Classification and boundary

Primary classification:

```text
MIRROR-WHOLE-SOURCE-NEG-CONJ-TRANSPORT-CLOSED
```

Secondary classifications:

```text
MIRROR-FINITE-APPROXIMANT-CONJ-TRANSPORT-CLOSED
MIRROR-WHOLE-SOURCE-CHANNEL-PARITY-CLOSED
MIRROR-WHOLE-FEATURE-MIXED-U-TRANSPORT-CLOSED
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

No upstream module required an edit. No `sorry`, `admit`, `native_decide`, or
new axiom was added. The mirror identities transport the same finite source
data and therefore do not provide an independent source-rank provider.

Shifted energy, P1/P2 inequalities, positivity, coercivity, GWSS-004,
Guinand--Weil, Li criterion, infinite limits, and RH were not started.

## Verification

The following checks completed successfully:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit
git diff --check
```

`#print axioms` was run on the canonical witness-weight, vertical-source,
top-source, WholeSource, finite-approximant, normalized-integral, and detailed
feature transport theorems. Each reports only the baseline
`[propext, Classical.choice, Quot.sound]`.

No commit, push, PR operation, or CI result is claimed by this report.
