# GWSS-003H6 shifted-energy mirror parity / paired-dominance collapse — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0054-GWSS-003H5-whole-source-mirror-conjugation-transport-report.md`

## 0. Mission

GWSS-003H5 closed the actual finite source transport for the canonical critical-mirror pair.  For the canonical mirror index `μ`, canonical off-critical coefficient row `c_j`, whole source `S_j`, and finite arithmetic approximant `A_j`, the current branch proves

```text
S_(μ j) = -conj(S_j)
A_(μ j) =  conj(A_j)
```

with component parity

```text
WholeSource.re : odd
WholeSource.im : even
Approximant.re : even
Approximant.im : odd.
```

GWSS-003G already proves the exact shifted-energy polarization readouts

```text
Δ1(c) := E1+(c) - E1-(c) = 4 * WholeSource(c).re
ΔI(c) := EI+(c) - EI-(c) = 4 * WholeSource(c).im
```

and equivalently

```text
Δ1(c) =  2 * FiniteApproximant(c).im
ΔI(c) = -2 * FiniteApproximant(c).re.
```

It also proves the order readouts

```text
E1-(c) ≤ E1+(c)  ↔  0 ≤ WholeSource(c).re
EI-(c) ≤ EI+(c)  ↔  0 ≤ WholeSource(c).im.
```

GWSS-003H6 is H8 only.

Transport these **integrated shifted-energy differences and dominance orders** across the canonical critical mirror.  Determine exactly which channel is mirror-odd and which is mirror-even, and formalize the resulting paired-dominance consequence.

The expected finite result is:

```text
Δ1(μ j) = -Δ1(j)
ΔI(μ j) =  ΔI(j).
```

Consequently, same-orientation dominance at both mirror endpoints behaves differently in the two channels:

```text
1-reference channel:
  dominance(j) ∧ dominance(μ j)
  forces Δ1(j) = 0
  and hence WholeSource(j).re = 0.

I-reference channel:
  dominance(μ j) ↔ dominance(j)
  so paired dominance is redundant and does not force ΔI(j) = 0.
```

Derive these statements from the already-closed finite APIs.  Do not infer them heuristically from the mixed pointwise whole-feature law.

Stop after the shifted-difference / order / equality-collapse layer is closed.

Do **not** open a new positivity provider, coercivity argument, zero-exclusion theorem, RH implication, GWSS-004, Guinand--Weil, Weil positivity, Li criterion, infinite-height limit, or arithmetic-cutoff limit.

## 1. Required files to inspect first

Read the current branch versions of at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

Known load-bearing declarations include:

```text
pascalCenteredXiSquaredOrbitMirrorIndex
pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
pascalCenteredXiMellinCanonicalWholeSource_mirror
pascalCenteredXiMellinCanonicalWholeSource_channels_mirror
pascalCenteredXiMellinCanonicalFiniteArithmeticApproximant_mirror
pascalCenteredXiMellinCanonicalFiniteArithmeticApproximant_channels_mirror

pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy
pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy
pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy
pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy

pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_two_mul_finiteApproximant_im
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_two_mul_finiteApproximant_re
pascalCenteredXiMellinWitnessWholeShiftedEnergy_order_iff_wholeSource_re_nonneg
pascalCenteredXiMellinWitnessWholeShiftedIEnergy_order_iff_wholeSource_im_nonneg
```

Do not duplicate the shifted-energy definitions.  Prefer a new focused H8 audit module importing H7 and the existing shifted-energy audit.

Suggested module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
```

## 2. Canonical notation

For

```text
R ε : ℝ
τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ
j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)
μ := pascalCenteredXiSquaredOrbitMirrorIndex R
c_j := pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j
c_μ := pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ (μ j)
```

and fixed finite `W X`, write conceptually

```text
Δ1(j) := E1+(c_j) - E1-(c_j)
ΔI(j) := EI+(c_j) - EI-(c_j).
```

Small local abbreviations are acceptable, but avoid creating a second parallel public energy API unless it materially clarifies theorem statements.

The shifted-energy source readouts require

```text
hε : 0 < ε
hτ : ∀ i, τ i ≠ 0
```

and canonical mirror coefficient transport requires

```text
hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0.
```

Keep these hypotheses explicit.

## 3. H8-A — `1`-reference shifted-difference mirror oddness

Using the existing source readout

```text
Δ1(j) = 4 * WholeSource(j).re
```

and H7

```text
WholeSource(μ j).re = -WholeSource(j).re,
```

prove the exact finite identity

```text
Δ1(μ j) = -Δ1(j).
```

Preferred proof route: rewrite both sides with
`pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re`
and then apply the H7 channel theorem.

As an optional consistency theorem, derive the same parity through

```text
Δ1 = 2 * FiniteApproximant.im
```

and H7 approximant imaginary oddness.  This is useful only as a cross-check; do not duplicate a long proof if it adds no API value.

This theorem is the load-bearing `1`-channel parity statement.

## 4. H8-B — `I`-reference shifted-difference mirror evenness

Similarly use

```text
ΔI(j) = 4 * WholeSource(j).im
```

and

```text
WholeSource(μ j).im = WholeSource(j).im
```

to prove

```text
ΔI(μ j) = ΔI(j).
```

Again, the finite-approximant readout

```text
ΔI = -2 * FiniteApproximant.re
```

and H7 approximant real evenness may be recorded as a short consistency route if useful.

Do not change the sign merely because the reference is `I`; the H7 source orientation has already fixed the correct parity.

## 5. H8-C — transport of the `1`-reference dominance order

Define no new positivity assumption.  Work with the existing order proposition

```text
Dom1(j) := E1-(c_j) ≤ E1+(c_j).
```

From H8-A, prove the exact mirror reversal law

```text
Dom1(μ j) ↔ E1+(c_j) ≤ E1-(c_j).
```

Equivalently, using the existing source order readout,

```text
Dom1(j)   ↔ 0 ≤ WholeSource(j).re
Dom1(μ j) ↔ WholeSource(j).re ≤ 0.
```

Both presentations are useful; export at least one theorem that makes the reversal visible at the energy-order level, not only at the source-component level.

This theorem is a transport theorem.  It does not assert `Dom1(j)`.

## 6. H8-D — paired same-orientation `1`-dominance collapses to equality

Prove the exact conditional collapse

```text
Dom1(j) ∧ Dom1(μ j)
  ↔ E1+(c_j) = E1-(c_j).
```

or an equivalent pair of implications if the iff is awkward.  Prefer the iff if it is short.

Also expose the source readout:

```text
Dom1(j) ∧ Dom1(μ j)
  ↔ WholeSource(j).re = 0.
```

and, if clean through the existing finite approximant identity,

```text
Dom1(j) ∧ Dom1(μ j)
  ↔ FiniteApproximant(j).im = 0.
```

At minimum prove the forward implications to `WholeSource.re = 0` and energy equality.  The reverse implication is expected to be elementary and should be included when straightforward.

**Firewall:** this is not a positivity provider.  The theorem says that *if* the same `1`-reference dominance is supplied at both mirror endpoints, then the mirror-odd channel must vanish.  It does not supply either dominance hypothesis.

Do not identify this vanishing with `q.im = 0` unless an already-proved exact same-object theorem on the current branch directly justifies that identification.  Do not open a bridge search in H8.

## 7. H8-E — transport of the `I`-reference dominance order

For

```text
DomI(j) := EI-(c_j) ≤ EI+(c_j),
```

use H8-B or the existing source order readout plus H7 imaginary evenness to prove

```text
DomI(μ j) ↔ DomI(j).
```

Then record the paired redundancy statement

```text
DomI(j) ∧ DomI(μ j) ↔ DomI(j).
```

or an equivalent theorem.

The mathematical conclusion must be explicit:

```text
same-orientation mirror pairing in the I-reference channel supplies no
opposite inequality and therefore does not force ΔI(j) = 0.
```

Do not encode the final English sentence as an impossibility theorem stronger than what Lean proves.  A small `Prop := True` marker is not useful here; the exact equivalence above is the preferred certificate.

## 8. H8-F — optional anti-overreach certificate

If useful for downstream documentation, package the channel asymmetry in one theorem returning a conjunction of the two exact parity identities:

```text
Δ1(μ j) = -Δ1(j) ∧ ΔI(μ j) = ΔI(j).
```

A second compact theorem may package

```text
(Dom1(j) ∧ Dom1(μ j) ↔ WholeSource(j).re = 0)
∧
(DomI(μ j) ↔ DomI(j)).
```

Do not create a structure unless there is a clear downstream use.

## 9. Explicit firewalls

The following are forbidden in H8:

1. **No new P1 provider.** Existing energy nonnegativity is P0 only.
2. **No inference `energy ≥ 0 ⇒ E- ≤ E+`.** Individual nonnegative energies do not order one another.
3. **No claim that mirror symmetry is an independent source.** It transports the same source data.
4. **No claim that both channels collapse.** Only the mirror-odd `1`-difference collapses under same-orientation paired dominance; the `I`-difference is mirror-even.
5. **No pointwise WholeBoxFeature simplification.** H7 proved a mixed-`u` law; H8 should use integrated/source readouts instead.
6. **No identification of `WholeSource.re = 0` with RH or `q.im = 0` without an exact existing bridge.**
7. **No limits:** no `T → ∞`, no `X → ∞`, no limit interchange.
8. **No GWSS-004 / Guinand--Weil / Weil positivity / Li criterion / RH.**
9. **No `sorry`, `admit`, `native_decide`, or new axiom.**

## 10. Expected classifications

If both channel parities and the paired-order consequences close, use primary classification

```text
MIRROR-SHIFTED-ENERGY-CHANNEL-PARITY-CLOSED
```

with secondary classifications

```text
MIRROR-ONE-DOMINANCE-PAIR-COLLAPSES-TO-EQUALITY
MIRROR-I-DOMINANCE-PAIR-REDUNDANT
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

If difference parity closes but order packaging is blocked only by an API/presentation issue, classify

```text
MIRROR-SHIFTED-DIFFERENCE-PARITY-CLOSED-ORDER-API-GAP
```

and report the exact missing declaration.

If the existing source-readout theorem cannot be instantiated with the canonical coefficient rows, stop with

```text
CANONICAL-SHIFTED-ENERGY-SOURCE-READOUT-API-GAP
```

and identify the exact type mismatch.  Do not work around it by introducing a mathematically different energy.

## 11. Verification

Run at minimum:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorShiftedEnergyAudit
git diff --check
```

Run `#print axioms` on the load-bearing H8 parity and paired-dominance theorems.  Expected baseline only:

```text
[propext, Classical.choice, Quot.sound]
```

No new axiom.

## 12. Closeout report

Create

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0056-GWSS-003H6-shifted-energy-mirror-parity-paired-dominance-collapse-report.md
```

The report must state explicitly:

1. exact theorem names added;
2. `Δ1` mirror-odd result;
3. `ΔI` mirror-even result;
4. exact `1`-dominance mirror reversal theorem;
5. exact paired `1`-dominance equality / source-zero consequence;
6. exact `I`-dominance mirror invariance / redundancy theorem;
7. whether any individual energy (`E1+`, `E1-`, `EI+`, `EI-`) mirror identity was proved — this is **not required** for H8;
8. no new P1 provider was found;
9. no positivity, limit, GWSS-004, or RH step was introduced;
10. build / diff / axiom-audit results.

Stop after the report.  Do not proceed automatically to H9.
