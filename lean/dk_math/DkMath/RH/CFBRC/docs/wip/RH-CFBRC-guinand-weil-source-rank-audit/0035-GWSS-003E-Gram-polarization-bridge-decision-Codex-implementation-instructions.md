# GWSS-003E Gram / polarization bridge decision — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003D frontier.

Trusted state:

```text
GWSS-001 source rank                         CLOSED
GWSS-002 finite off-critical Mellin witness CLOSED
GWSS-003A finite arithmetic identity        FOUND
GWSS-003B universal complex-linear phase    NOGO
GWSS-003C first-order homogeneous norm      NOGO
GWSS-003D vanishing-scale provider          NOT FOUND
GWSS-003D real/conjugation provider         API GAP / cancellation risk
GWSS-003D nonlinear positivity              SOURCE-SIDE CANDIDATE ONLY
current primary classification              NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
```

Implement only the next bounded stage:

```text
GWSS-003E-1  audit the already-existing source-side polarization identities
GWSS-003E-2  determine whether polarization actually escapes the scalar-homogeneity obstruction
GWSS-003E-3  audit the exact bridge from the fixed tau=0 quadratic source to the synthesized GWSS-002 witness
GWSS-003E-4  identify the minimal independent shifted-energy order/asymmetry provider, if any
GWSS-003E-5  decide whether the nonlinear candidate survives or collapses back to the known linear source
```

This stage is a bridge/decision audit. Do not rebuild the existing quadraticization stack.

Do not start:

```text
GWSS-004 classical Guinand--Weil infrastructure
full Weil positivity criterion
Li criterion
T -> infinity
new zero-avoidance-height theory
new Xi growth theory
new source-rank family
new interpolation family
DkReal shrinking-window uniqueness
RiemannHypothesis deduction
```

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0033 instructions read
0034 report read
PascalCenteredXiMellinWitnessProviderDecisionAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiPrimeSideQuadraticizationAudit.lean read
PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean read
DkMath.Analysis.MellinQuadraticGramKernel read
global objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-003E
```

Load-bearing boundary:

```text
The GWSS-002 target witness satisfies an exact scalar factorization

h_off = qIm * h_mass,

where qIm is the target squared-orbit imaginary coordinate.

GWSS-003C proved that every currently audited first-order linear/norm estimate
transports this same scalar and therefore cannot force qIm = 0.

GWSS-003D found a genuinely source-derived quadratic/Gram candidate, but no
bridge from that candidate to the synthesized target witness or to off-critical
discrimination.

GWSS-003E must decide whether the existing polarization machinery adds genuine
relative information, or merely rewrites the same linear source as a
difference of nonnegative squares.
```

Forbidden shortcuts:

```text
RH
classical Weil positivity imported as a black box
Li criterion
functional-equation reflection promoted to a new independent source
conjugation promoted to a new independent source
fixed-Xi zero-side defect sign reused as arithmetic positivity
old CFZP / fixed-defect conclusions imported as the missing provider
unproved horizontal decay
unproved limit exchange
reverse triangle inequality
reverse Cauchy--Schwarz
reverse Parseval/Bessel/Gram
assuming shifted-energy dominance
assuming inverse-matrix conditioning
assuming qIm has a uniform positive lower bound
calling a polarization identity itself a positivity theorem
calling two separately nonnegative energies an ordered pair
```

## 2. Important existing API — do not reimplement it

The repository already contains substantially more than a bare Gram-energy
nonnegativity statement.

In `DkMath.Analysis.MellinQuadraticGramKernel` there is already:

```text
mellinQuadraticBoxGramKernel
mellinQuadraticBoxGramEnergy
mellinQuadraticBoxGramEnergy_nonneg
mellinQuadraticBoxGramQuadraticForm
mellinQuadraticBoxGramQuadraticForm_eq_energy
```

The generic kernel is genuinely two-index/Hermitian:

```text
K_epsilon(z,w)
  = z * conj(w) * MellinMultiplier_epsilon(z + conj(w)).
```

The source-side CFBRC quadraticization also already contains exact polarization
machinery. In particular, verify and reuse the exact declarations around:

```text
pascalCenteredXiPrimeSideQuadraticization_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticizationShiftedPlusEnergy
pascalCenteredXiPrimeSideQuadraticizationShiftedMinusEnergy
pascalCenteredXiPrimeSideQuadraticization_verticalSurface_eq_shiftedEnergyDifference
pascalCenteredXiPrimeSideQuadraticization_shiftedEnergy_order_iff_vertical_nonneg
```

The whole finite surface, including the source-derived horizontal
symmetrization, also has corresponding machinery. Verify and reuse the exact
current declarations around:

```text
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_normalized_wholeBoxFeature
pascalCenteredXiMellinQuadraticComplexWholeSurface_eq_conj
pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature_polarization_pointwise
pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference...
```

Do not recreate any of these under new names unless a very small wrapper is
needed for the GWSS-002 comparison.

## 3. GWSS-003E-1 — audit what polarization actually says

### E1. Vertical identity

Confirm the exact existing theorem with the semantic shape

```text
4 * V = E_plus - E_minus,
```

where `V` is the finite source-derived complex vertical surface and both
`E_plus`, `E_minus` are nonnegative shifted energies.

Also confirm the existing order/sign equivalence when present:

```text
E_minus <= E_plus  <->  0 <= Re(V).
```

Important interpretation:

```text
E_plus >= 0 and E_minus >= 0
```

alone do not imply either

```text
E_minus <= E_plus
```

or

```text
E_plus <= E_minus.
```

Therefore the polarization identity does not itself supply a sign theorem.

If useful, formalize a tiny scalar counterexample certificate showing that two
nonnegative shifted squares can occur in either order as the underlying real
feature changes sign. Keep it elementary.

### E2. Whole-surface identity

Prefer the whole finite source surface for provider decisions, because the
finite explicit formula retains the top-horizontal contribution.

Audit whether the current whole-box polarization gives an exact identity of
schematic form

```text
4 * WholeSurface = WholeE_plus - WholeE_minus.
```

If the repository already proves the corresponding order/sign equivalence,
reuse it. If it does not, a short algebraic wrapper is allowed.

Do not discard the horizontal contribution merely because the vertical
polarization is cleaner.

## 4. GWSS-003E-2 — scalar factorization versus a fixed reference

The key algebraic distinction is the fixed reference `1` inside the shifted
energies.

For a real scalar `q` and a conjugation-real feature `F`, the bare quadratic
energy obeys

```text
normSq(q * F) = q^2 * normSq(F),
```

which is the closed degree-two homogeneity from GWSS-003D.

But the shifted polarization terms obey schematically

```text
normSq(q * F + 1) - normSq(q * F - 1) = 4 * q * F
```

when `F` is real/conjugation-fixed.

Thus a fixed reference can algebraically preserve a term linear in `q`.

This does **not** yet mean the scalar obstruction is solved. The new question
is whether arithmetic structure independently orders or compares the two
shifted energies.

If compact, prove/reuse a generic scalar lemma capturing this distinction.
Possible theorem shape:

```lean
theorem normSq_shifted_difference_real_scale
    (q : ℝ) {F : ℂ} (hF : F = starRingEnd ℂ F) :
    (Complex.normSq (((q : ℂ) * F) + 1) : ℂ) -
      (Complex.normSq (((q : ℂ) * F) - 1) : ℂ) =
        (4 : ℂ) * (q : ℂ) * F := by
  ...
```

Equivalent orientation is acceptable.

Do not spend time generalizing polarization over arbitrary inner-product
spaces.

### E2a. Positivity-only no-go certificate

If cheap, add a tiny certificate demonstrating that nonnegativity of both
shifted energies does not determine their order.

For example, use fixed real values `F = 1` and `F = -1` to show opposite
orderings while every norm square remains nonnegative.

The semantic point to record is:

```text
shifted-energy nonnegativity: FOUND
shifted-energy dominance/order: still requires independent information
```

## 5. GWSS-003E-3 — exact bridge to the synthesized target witness

This is the load-bearing section.

The current source-side quadraticization is built around the fixed
`tau = 0` Mellin quadratic weight / logarithmic box feature. The GWSS-002
witness instead has the form

```text
h_target = sum_i c_i * H_{epsilon,tau_i},
```

with target-dependent complex coefficients from an inverse evaluation matrix.

Do not silently identify these two weight classes.

### E3. Audit exact compatibility

Search for an existing theorem that transports the source-side box/Gram
feature construction from the fixed `tau = 0` quadratic weight to either:

```text
1. arbitrary canonical Mellin second-difference weight H_{epsilon,tau}, or
2. a finite synthesized witness sum_i c_i H_{epsilon,tau_i}.
```

The needed bridge must preserve enough structure to define a source-derived
feature/energy for the **same synthesized witness** used by GWSS-002.

A valid bridge must not be obtained by first rewriting the target witness zero
moment through the explicit formula and then declaring that result to be the
source feature.

### E3a. If an existing basis-level bridge is available

If the repository already exposes source box features for general `tau`, audit
linearity carefully and derive only the smallest finite-sum bridge needed.

Then determine whether

```text
A_off = qIm * A_mass
```

holds for the synthesized source aggregate.

If yes, combine it with the fixed-reference polarization audit:

```text
WholeE_plus(A_off) - WholeE_minus(A_off)
  = 4 * qIm * WholeA_mass
```

or the exact current equivalent.

The important question is then whether any independent theorem determines the
sign/order of those two energies.

### E3b. If no general-tau/source-feature bridge exists

Do not build a large new quadraticization theory in this assignment.

Record the exact missing interface, for example:

```text
TARGET-WITNESS-QUADRATICIZATION-BRIDGE-GAP
```

with the smallest required theorem signature.

A legitimate minimal contract might be schematic:

```text
sourceFeature(h_target)
sourceFeature(q * h_target) = q * sourceFeature(h_target)
wholeArithmeticSurface(h_target)
  = normalizedIntegral(sourceFeature(h_target))
```

but do not introduce this as an axiom or provider structure merely to claim
progress.

## 6. GWSS-003E-4 — identify the actual missing nonlinear information

Suppose polarization is available for the same target witness.

Then distinguish sharply between:

```text
P0. each shifted energy is nonnegative
P1. one shifted energy dominates the other
P2. the shifted energies are equal
P3. a quantitative gap between shifted energies is controlled independently
```

Information content:

```text
P0 alone:
  no sign of the polarized linear source.

P1:
  gives a one-sided sign of the polarized source.

P2:
  forces the polarized source to zero.

P3:
  may give quantitative control if the gap is independent of target scalar
  rescaling.
```

Audit whether the current repository supplies P1, P2, or P3 from **source-side
arithmetic structure**, not from a zero-side defect sign or an RH-equivalent
criterion.

### E4a. Existing order equivalences are not providers by themselves

A theorem of the form

```text
E_minus <= E_plus  <->  0 <= Re(V)
```

is an exact equivalence, not an independent proof of either side.

Do not classify such an equivalence as shifted-energy dominance.

### E4b. Whole-surface preference

If P1/P2/P3 exists only for a vertical source while the top-horizontal term is
uncontrolled, it is not yet a provider for the full finite explicit formula.

Prefer an exact whole-surface theorem. If only the vertical theorem exists,
record the horizontal compatibility gap explicitly.

## 7. GWSS-003E-5 — decide whether the candidate survives

End with exactly one primary classification from:

```text
TARGET-WITNESS-QUADRATICIZATION-BRIDGE-GAP
POLARIZATION-RETURNS-LINEAR-SOURCE-NO-NEW-PROVIDER
SHIFTED-ENERGY-DOMINANCE-PROVIDER-GAP
WHOLE-SURFACE-POLARIZATION-ROUTE-OPEN
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
GWSS-003E-IMPLEMENTATION-API-GAP
```

Secondary findings may include:

```text
vertical shifted-energy polarization: FOUND / GAP
whole-surface shifted-energy polarization: FOUND / GAP
shifted-energy nonnegativity: FOUND / GAP
fixed-reference linear cross-term: FOUND / GAP
general-tau source feature: FOUND / GAP
synthesized witness source feature: FOUND / GAP
off-critical source aggregate scalar factorization: FOUND / GAP
independent shifted-energy dominance: FOUND / NOT FOUND / RH-EQUIVALENT
horizontal compatibility: FOUND / GAP
```

### Classification guidance

Use

```text
TARGET-WITNESS-QUADRATICIZATION-BRIDGE-GAP
```

if the existing quadraticization is genuinely restricted to the fixed
`tau = 0` weight and no small bridge reaches the synthesized witness.

Use

```text
POLARIZATION-RETURNS-LINEAR-SOURCE-NO-NEW-PROVIDER
```

if the same-target polarization can be formed but it gives only an exact
rewrite of the already-known linear source, with no independent shifted-energy
order/asymmetry theorem.

Use

```text
SHIFTED-ENERGY-DOMINANCE-PROVIDER-GAP
```

if the target bridge exists and the **only** remaining missing theorem is an
independent order/equality/asymmetry between the shifted positive energies.

Use

```text
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
```

only if all of the following are established:

```text
1. the source-side nonlinear observable applies to the same synthesized target witness,
2. it includes the whole finite arithmetic surface or an exact compatible replacement,
3. polarization retains off-critical information after GWSS-003C normalization,
4. a precise independent P1/P2/P3-style arithmetic statement is identified as the sole missing provider,
5. that statement is not already RH/Weil positivity/Li in disguise.
```

## 8. GWSS-004 authorization rule

GWSS-004 remains unauthorized by default.

Authorize GWSS-004 only if the primary result is

```text
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
```

and the report names one exact minimal source-side positivity/dominance
fragment as the only remaining provider.

If the result is any bridge gap, linear-rewrite no-go, or unresolved decision,
stay inside GWSS-003.

Even if GWSS-004 becomes authorized, it means only a bounded bridge audit. It
does not authorize importing the full classical Weil criterion.

## 9. Preferred focused Lean output

Prefer one small focused module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean
```

The module should contain only compact reusable facts needed to certify the
bridge decision.

Likely useful contents are limited to:

```text
1. one generic fixed-reference polarization/scaling lemma, if not already reusable,
2. one tiny positivity-does-not-imply-order certificate, if helpful,
3. at most one compact bridge theorem if existing APIs make it immediate.
```

If the target-witness bridge would require a large generalized
quadraticization construction, stop and report the API gap instead.

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0036-GWSS-003E-Gram-polarization-bridge-decision-report.md
```

## 10. Mandatory report structure

The 0036 report must contain:

```text
1. orientation and exact repository state
2. existing vertical polarization inventory
3. existing whole-surface polarization inventory
4. fixed-reference scaling audit
5. target-witness source-feature compatibility audit
6. shifted-energy order/dominance provider audit
7. exact primary classification
8. next unresolved Gap
9. GWSS-004 authorization status
10. verification and axiom audit
```

The report must explicitly answer these questions:

```text
Q1. Does the existing Gram/polarization candidate apply to the same GWSS-002 synthesized witness?
Q2. If yes, does a fixed reference preserve qIm linearly rather than only through |qIm|^2?
Q3. Does current source-side positivity independently order the shifted energies?
Q4. Does the whole finite surface, including top-horizontal, participate in the same bridge?
Q5. What exact theorem is now the first missing provider?
```

## 11. Verification requirements

Required focused build:

```text
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit
```

Also run:

```text
git diff --check
```

Audit load-bearing declarations with `#print axioms` or the established local
wrapper. Expected footprint is no stronger than the existing standard set:

```text
propext
Classical.choice
Quot.sound
```

No:

```text
sorry
admit
native_decide
new axiom
unproved limit exchange
unproved positivity order
RH
Weil criterion
Li criterion
```

## 12. Stop rule

Stop after GWSS-003E.

Do not start GWSS-004 in the same assignment even if the result identifies a
minimal provider. The 0036 report must first be reviewed.