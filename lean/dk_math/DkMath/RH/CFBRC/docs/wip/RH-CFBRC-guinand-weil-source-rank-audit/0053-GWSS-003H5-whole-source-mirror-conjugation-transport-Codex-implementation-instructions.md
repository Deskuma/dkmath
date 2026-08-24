# GWSS-003H5 whole-source mirror conjugation transport — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0052-GWSS-003H4-canonical-offcritical-coefficient-detector-mirror-transport-report.md`

## 0. Mission

GWSS-003H4 closed the canonical finite detector layer.  For the canonical mirror index `μ`, canonical inverse extractor row `r_j`, canonical off-critical coefficient row `cOff_j`, mass vector `M_j`, and detector scalar `D_j`, the current branch now proves

```text
q_(μ j) = conj(q_j)
r_(μ j) = conj(r_j)
cOff_(μ j) = -conj(cOff_j)
M_(μ j) = M_j
D_(μ j) = -D_j
```

and the paired canonical detector extraction sums are exact negatives.

GWSS-003H5 is H7 only.

Transport the canonical mirror pair through the **actual synthesized finite source surface**:

```text
canonical witness weight
vertical finite source
top-horizontal finite source
whole finite source
finite arithmetic approximant
normalized whole-feature integral
```

Determine the exact conjugation/sign law at each layer.

This stage is an audit, not a place to assume a simple pointwise whole-feature Schwarz law.  In particular, the top horizontal geometry can introduce the reflection `u ↦ -u` in the logarithmic-box feature before the outer symmetric `[-ε, ε]` integration removes it.  Derive the actual law from the definitions.

Stop after WholeSource / finite-approximant transport and their real/imaginary channel parity are closed, or at the first genuine finite source-conjugation API obstruction.

Do **not** define or compare shifted energies in this stage.  Do not prove P1/P2 inequalities, positivity, coercivity, source-rank independence, GWSS-004, Guinand--Weil, Weil positivity, Li criterion, infinite-height limits, arithmetic-cutoff limits, or RH.

## 1. Required files to inspect first

Read the current branch versions of at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorOffCriticalCoefficientAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaFunctionalEquationReflection.lean
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaHorizontalPairing.lean
DkMath/RH/CFBRC/PascalCanonicalXiFixedObservableBridge.lean
```

Search the pinned DkMath / Mathlib APIs for existing conjugation lemmas before proving local helpers.

Known load-bearing declarations include:

```text
pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow
pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror
pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow_mirror_fun
pascalCenteredXiMellinSecondDifferenceWeight_conj
pascalCenteredXiMellinWitnessWeight
pascalCenteredXiMellinGeneralTauWitnessVerticalSource
pascalCenteredXiMellinGeneralTauWitnessWholeSource
pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature
pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource
pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode
pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude
pascalCenteredXiPrimeSideQuadraticizationTopNode
pascalCenteredXiPrimeSideQuadraticizationTopAmplitude
pascalCenteredXiNegLogDeriv_neg
pascalCenteredRiemannXiKernel_conj
```

Also inspect whether a conjugation theorem for `pascalCenteredXiNegLogDeriv`, the finite PHZ cutoff, the archimedean correction, or the elementary correction already exists.  Do not duplicate a public theorem if the exact fact is already available.

## 2. Canonical notation for this stage

For fixed

```text
R ε : ℝ
τ : Fin n → ℝ
j : Fin n
H = pascalCenteredXiMellinEvaluationMatrix R ε τ
μ = pascalCenteredXiSquaredOrbitMirrorIndex R
c_j = pascalCenteredXiMellinCanonicalOffCriticalCoefficientRow R ε τ j
```

where `n = pascalCenteredXiSquaredOrbitIndexCard R`, write conceptually

```text
h_j(z) = pascalCenteredXiMellinWitnessWeight ε τ c_j z
V_j    = pascalCenteredXiMellinGeneralTauWitnessVerticalSource ε τ c_j W X
T_j    = pascalCenteredXiTopHorizontalContribution h_j W.toContourTransportWindow
S_j    = pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c_j W X
A_j    = pascalCenteredXiFiniteArithmeticApproximant h_j W X
```

Do not introduce excessive wrappers if direct expressions remain readable.  A small canonical alias layer is acceptable if it makes the final statements substantially clearer.

The H5/H6 hypotheses needed for coefficient transport are

```text
0 < ε
det H ≠ 0
```

The general-`τ` logarithmic whole-feature representation additionally needs

```text
∀ i, τ i ≠ 0.
```

Keep these roles separate.

## 3. H7-A — canonical witness-weight Schwarz transport

First prove the function-level transport before touching source amplitudes.

Using

```text
c_(μ j)(i) = -conj(c_j(i))
w_i(conj z) = conj(w_i(z))
```

prove the exact identity

```text
h_(μ j)(z) = -conj(h_j(conj z)).
```

Equivalent useful forms are

```text
h_(μ j)(conj z) = -conj(h_j(z))
```

and the function equality

```text
h_(μ j) = fun z => -conj(h_j(conj z)).
```

The basis-weight conjugation theorem is the all-real-`τ` theorem from H5, including the patched `τ = 0` branch.

Also record that both weights are even using the existing synthesized-witness evenness theorem; do not reprove evenness term by term unless necessary.

This step should not require `∀ i, τ i ≠ 0`.

## 4. H7-B — right-edge source conjugation geometry

Audit and prove the exact finite right-edge pairing needed by the vertical source.

The expected geometric node law is

```text
RightEdgeNode W (-t) = conj(RightEdgeNode W t).
```

For the complete finite deoriented source amplitude, audit whether the current definitions give

```text
VerticalAmplitude W X (-t) = conj(VerticalAmplitude W X t).
```

This amplitude contains all three retained finite right-edge pieces:

```text
finite PHZ / von-Mangoldt cutoff
archimedean logarithmic-derivative correction
elementary correction
```

Do not silently replace the finite PHZ cutoff by the full zeta logarithmic derivative.

Preferred proof policy:

1. reuse exact pinned conjugation lemmas for each summand if present;
2. otherwise prove the smallest local finite helper directly from the definitions;
3. if one summand lacks a usable conjugation API and a local proof would require opening a large unrelated analytic development, stop with the precise missing theorem.

The finite cutoff is real-coefficient data evaluated at conjugate points, so a direct finite-sum proof is acceptable.  The archimedean / elementary terms must be handled from their exact definitions or existing conjugation APIs, not by heuristic real-coefficient language.

## 5. H7-C — vertical source transport

Once H7-A and H7-B are available, prove the pointwise pulled-back integrand law and then the symmetric-interval source law

```text
V_(μ j) = -conj(V_j).
```

A robust proof should visibly use the substitution `t ↦ -t` on `[-T,T]` rather than pretending the integrands agree at the same `t`.

At the pointwise level, the expected shape is

```text
mirrorVerticalIntegrand(t)
  = -conj(originalVerticalIntegrand(-t)).
```

Then use interval-integral conjugation and `integral_comp_neg` / symmetric orientation carefully.

No `X → ∞` step is permitted.  `X` remains a fixed natural cutoff.

## 6. H7-D — fixed-Xi top conjugation helper

The top edge is subtler than the vertical edge.

First establish or locate conjugation covariance of the totalized centered Xi negative logarithmic derivative:

```text
pascalCenteredXiNegLogDeriv (conj z)
  = conj(pascalCenteredXiNegLogDeriv z).
```

Do **not** treat raw complex conjugation as holomorphic.  If this theorem is absent, prove it using the existing centered-Xi kernel conjugation identity together with the pinned derivative-conjugation API (`deriv_star_conj` / equivalent) and the totalized `logDeriv` definition.  The helper must remain valid at zeros because the project uses totalized `logDeriv`.

Combine it with the already-proved oddness

```text
pascalCenteredXiNegLogDeriv (-z)
  = -pascalCenteredXiNegLogDeriv z
```

and the top-node geometry

```text
TopNode W (1 - x)
  = -conj(TopNode W x).
```

to derive the exact amplitude pairing

```text
TopAmplitude W (1 - x)
  = -conj(TopAmplitude W x).
```

Keep the affine reflection `x ↦ 1 - x` explicit.

## 7. H7-E — top-horizontal source transport

Use H7-A, evenness of the synthesized witness, H7-D, and the interval substitution `x ↦ 1 - x` to determine the exact top-source law.

The expected law is

```text
T_(μ j) = conj(T_j).
```

This sign is intentionally different from the vertical-source sign.

Derive it.  Do not infer it merely from the expected WholeSource result.

The sign mechanism should remain visible:

```text
h_(μ j)(TopNode(1-x)) = -conj(h_j(TopNode(x)))
TopAmplitude(1-x)     = -conj(TopAmplitude(x))
```

so the two minus signs cancel before integration.

## 8. H7-F — whole-source transport

Recall the exact finite orientation convention

```text
WholeSource = VerticalSource - I * TopHorizontalContribution.
```

From

```text
V_(μ j) = -conj(V_j)
T_(μ j) =  conj(T_j)
```

prove

```text
S_(μ j) = -conj(S_j).
```

This is the load-bearing H7 whole-source theorem.

Then record the component parity

```text
Re(S_(μ j)) = -Re(S_j)
Im(S_(μ j)) =  Im(S_j).
```

These are finite exact identities.  Do not call them positivity or dominance statements.

## 9. H7-G — finite arithmetic approximant transport

Use the already-proved exact finite ledger

```text
A_j = 2 * I * S_j
```

for both mirror targets.  From the WholeSource law, derive

```text
A_(μ j) = conj(A_j).
```

Check the `I` conjugation sign explicitly:

```text
conj(2 * I * S) = -2 * I * conj(S).
```

Do not accidentally claim `A_(μ j) = -conj(A_j)`.

Record the exact component parity

```text
Re(A_(μ j)) =  Re(A_j)
Im(A_(μ j)) = -Im(A_j).
```

Again, this is finite and cutoff-preserving.

## 10. H7-H — logarithmic whole-feature transport: derive the actual law

Only after the source-level laws above are stable, inspect the pointwise logarithmic-box features.

Do **not** assume

```text
WholeBoxFeature_(μ j)(u) = -conj(WholeBoxFeature_j(u)).
```

without proof.

The vertical and top pieces have different source geometry.  The expected detailed laws are:

```text
VerticalAggregatedFeature_(μ j)(u)
  = -conj(VerticalAggregatedFeature_j(u))
```

and, because `TopNode(1-x) = -conj(TopNode x)` while the box feature contains `exp(u z)`, potentially

```text
TopAggregatedFeature_(μ j)(u)
  = conj(TopAggregatedFeature_j(-u)).
```

Audit the actual definitions and prove the exact statements if they close cleanly.

If these expected laws are correct, the pointwise WholeBoxFeature law is **mixed** rather than a simple Schwarz law:

```text
WholeFeature_(μ j)(u)
  = -conj(VerticalFeature_j(u))
    - I * conj(TopFeature_j(-u)).
```

Do not collapse the `-u` unless an independent evenness theorem for the top aggregated feature has actually been proved.

The important integral-level consequence over the symmetric box is expected to be

```text
((2*ε)⁻¹ : ℂ) * ∫ u in (-ε)..ε, WholeFeature_(μ j)(u)
  = -conj(
      ((2*ε)⁻¹ : ℂ) * ∫ u in (-ε)..ε, WholeFeature_j(u)).
```

This may be proved either directly from the detailed vertical/top laws and `u ↦ -u`, or as a corollary of the WholeSource law plus the existing normalized whole-source representation, provided `∀ i, τ i ≠ 0` is present.

If the simple pointwise Schwarz law fails but the mixed law and normalized-integral law close, that is a successful and informative H7 outcome, not a failure.

## 11. H7-I — explicit channel table for the next stage

At closeout, record the exact finite mirror transport table that is actually proved.  The target table is

```text
coefficient row:      c_(μ j) = -conj(c_j)
vertical source:      V_(μ j) = -conj(V_j)
top source:           T_(μ j) =  conj(T_j)
whole source:         S_(μ j) = -conj(S_j)
finite approximant:   A_(μ j) =  conj(A_j)
```

and therefore

```text
WholeSource.re : odd
WholeSource.im : even
Approximant.re : even
Approximant.im : odd
```

This table is the only input H8 may later use to transport the two shifted-energy polarization channels.

Do not implement H8 in this stage.

## 12. Firewalls

### Firewall 1 — coefficient transport alone is insufficient

From `c_(μ j) = -conj(c_j)` one cannot conclude a WholeSource or feature conjugation law without source/basis conjugation information.

### Firewall 2 — vertical and top signs differ

Do not force both source pieces into the same `-conj` law.  The top reflection carries two minus signs (weight and Xi log derivative), so its expected source law is `+conj`.

### Firewall 3 — no simple pointwise whole-feature law by default

The top logarithmic feature may carry `u ↦ -u`.  Preserve it unless it is genuinely discharged.

### Firewall 4 — finite cutoff remains finite

No `X → ∞`, no exchange of cutoff and integration, and no asymptotic argument.

### Firewall 5 — totalized log derivative

Any conjugation theorem for `pascalCenteredXiNegLogDeriv` must respect the totalized Mathlib `logDeriv` semantics and remain valid at zeros.

### Firewall 6 — raw conjugation is anti-holomorphic

Do not prove a derivative-conjugation helper by pretending `conj` is complex differentiable.

### Firewall 7 — no energy / dominance work

Even if the channel parity becomes obvious, do not define or compare shifted energies here.

### Firewall 8 — symmetry is not independent rank

All mirror results are transport of the same finite source data.  No independent provider is created.

### Firewall 9 — no RH-equivalent provider

No RH, Li criterion, Weil positivity, raw-ratio boundedness, or equivalent shortcut.

## 13. Expected implementation location

Prefer a new focused module, for example

```text
DkMath/RH/CFBRC/
  PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
```

Import only the H6 module and the existing general-`τ` source bridge / exact source geometry needed by the proof.

Small reusable conjugation helpers may be added to a more natural upstream module only when they are genuinely generic and the edit remains narrowly scoped.  Document any upstream edit in the closeout report.

## 14. Expected classifications

If the full H7 source / approximant layer closes:

```text
MIRROR-WHOLE-SOURCE-NEG-CONJ-TRANSPORT-CLOSED
```

Recommended secondary classifications:

```text
MIRROR-FINITE-APPROXIMANT-CONJ-TRANSPORT-CLOSED
MIRROR-WHOLE-SOURCE-CHANNEL-PARITY-CLOSED
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

If the detailed feature law closes with the expected `u ↦ -u` top reflection, also record

```text
MIRROR-WHOLE-FEATURE-MIXED-U-TRANSPORT-CLOSED
```

If a genuine finite API obstruction remains, classify the first missing layer precisely, for example

```text
VERTICAL-SOURCE-CONJUGATION-API-GAP
TOP-XI-LOGDERIV-CONJUGATION-API-GAP
TOP-SOURCE-AFFINE-REFLECTION-API-GAP
WHOLE-SOURCE-MIRROR-TRANSPORT-GAP
```

Do not use an API-gap classification merely because a convenience lemma is absent; build the smallest local helper when the mathematics and pinned APIs already suffice.

## 15. Verification

Run at minimum:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorWholeSourceAudit
git diff --check
```

Run `#print axioms` on the load-bearing public declarations, especially:

```text
canonical witness-weight mirror theorem
vertical-source mirror theorem
top-source mirror theorem
WholeSource mirror theorem
finite-approximant mirror theorem
normalized whole-feature integral mirror theorem (if implemented)
```

Expected baseline only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new axiom.

## 16. Closeout report

Write

```text
0054-GWSS-003H5-whole-source-mirror-conjugation-transport-report.md
```

The report must state:

1. exact source symmetry helpers proved or reused;
2. exact vertical and top source signs;
3. exact WholeSource conjugation law;
4. exact finite approximant conjugation law;
5. real/imaginary channel parity;
6. whether the pointwise WholeBoxFeature law is simple or mixed with `u ↦ -u`;
7. whether the normalized whole-feature integral transport closes;
8. all hypotheses (`hε`, `hdet`, `hτ`, finite `W`, finite `X`);
9. axiom audit;
10. primary and secondary classification;
11. explicit statement that shifted energy / P1-P2 / positivity / GWSS-004 were not started.

## 17. Stop rule

Stop as soon as one of the following occurs:

```text
A. WholeSource and finite approximant mirror transport close;
B. a precise finite source-conjugation API gap blocks them.
```

If A occurs, do not continue into shifted energies in the same implementation batch.

The next bounded stage after a successful H7 will be H8: transport the already-defined `+1/-1` and `+I/-I` shifted-energy polarization readouts using the proved channel parity, and determine exactly which channel is odd and which is even under the critical mirror.