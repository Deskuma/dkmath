# GWSS-003H6: shifted-energy mirror parity and paired dominance collapse

## Scope

This checkpoint implements the bounded H8 stage from 0055.  It uses the
integrated shifted-energy readouts from GWSS-003G and the finite WholeSource
channel parity from GWSS-003H5.  It does not define a second energy API and it
does not introduce a new positivity or dominance provider.

The implementation is

`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean`.

The hypotheses remain explicit: `hε : 0 < ε`, `hτ : ∀ i, τ i ≠ 0`, and
`hdet : det (evaluationMatrix R ε τ) ≠ 0`.  `W` and `X` are finite throughout.

## H8-A/B: integrated shifted-difference parity

`pascalCenteredXiMellinCanonicalShiftedEnergyDifference_one_mirror` proves

```text
Δ1(μ j) = -Δ1(j).
```

`pascalCenteredXiMellinCanonicalShiftedEnergyDifference_I_mirror` proves

```text
ΔI(μ j) = ΔI(j).
```

Both proofs use the existing exact source readouts

```text
Δ1 = 4 * WholeSource.re
ΔI = 4 * WholeSource.im
```

and the H7 real-odd / imaginary-even channel theorem.  No pointwise
WholeBoxFeature simplification is used.

## H8-C/D: `1`-reference dominance reversal and collapse

`pascalCenteredXiMellinCanonicalShiftedEnergy_one_dominance_mirror_iff`
proves the order-level reversal

```text
Dom1(μ j) ↔ E1+(j) ≤ E1-(j).
```

The paired same-orientation consequence is exposed in two forms:

* `pascalCenteredXiMellinCanonicalShiftedEnergy_one_paired_dominance_iff_energy_eq`
  proves

  ```text
  Dom1(j) ∧ Dom1(μ j) ↔ E1+(j) = E1-(j).
  ```

* `pascalCenteredXiMellinCanonicalShiftedEnergy_one_paired_dominance_iff_wholeSource_re_eq_zero`
  proves

  ```text
  Dom1(j) ∧ Dom1(μ j) ↔ WholeSource(j).re = 0.
  ```

These are conditional collapse statements.  They do not establish either
dominance premise, identify the zero with `q.im = 0`, or create a P1 provider.

## H8-E: `I`-reference dominance invariance

`pascalCenteredXiMellinCanonicalShiftedEnergy_I_dominance_mirror_iff` proves

```text
DomI(μ j) ↔ DomI(j).
```

The paired form
`pascalCenteredXiMellinCanonicalShiftedEnergy_I_paired_dominance_iff`
proves

```text
DomI(j) ∧ DomI(μ j) ↔ DomI(j).
```

Thus same-orientation mirror pairing in the `I` channel is redundant and does
not supply an opposite inequality or force `ΔI(j) = 0`.

The compact theorem
`pascalCenteredXiMellinCanonicalShiftedEnergy_mirror_parity` packages the two
exact difference parities in one conjunction.

No individual mirror identity for `E1+`, `E1-`, `EI+`, or `EI-` was proved;
H8 only requires the integrated difference and order readouts.

## Classification and boundary

Primary classification:

```text
MIRROR-SHIFTED-ENERGY-CHANNEL-PARITY-CLOSED
```

Secondary classifications:

```text
MIRROR-ONE-DOMINANCE-PAIR-COLLAPSES-TO-EQUALITY
MIRROR-I-DOMINANCE-PAIR-REDUNDANT
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

No new P1 provider, positivity argument, coercivity argument, limit,
GWSS-004, Guinand--Weil, Weil positivity, Li criterion, or RH step was
introduced.  No `sorry`, `admit`, `native_decide`, or new axiom was added.

## Verification

The following checks completed successfully:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit
git diff --check
```

`#print axioms` was run on the two shifted-difference parity theorems, the
`1`-dominance reversal and paired-collapse theorems, the `I`-dominance
invariance and redundancy theorems, and the compact parity theorem.  Each
reports only the baseline `[propext, Classical.choice, Quot.sound]`.

No commit, push, PR operation, or CI result is claimed by this report.
