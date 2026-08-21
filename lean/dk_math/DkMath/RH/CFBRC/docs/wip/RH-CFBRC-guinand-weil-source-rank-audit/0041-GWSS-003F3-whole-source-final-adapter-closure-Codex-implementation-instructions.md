# GWSS-003F3 whole-source final adapter closure — Codex implementation instructions

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003F2 frontier.

Trusted state:

```text
GWSS-001 source rank                                  CLOSED
GWSS-002 finite off-critical Mellin witness          CLOSED
GWSS-003A finite arithmetic identity                 FOUND
GWSS-003B universal complex-linear phase             NOGO
GWSS-003C first-order homogeneous norm               NOGO
GWSS-003D independent vanishing scale                NOT FOUND
GWSS-003D real/conjugation route                     API GAP / cancellation risk
GWSS-003D nonlinear positivity                       SOURCE-SIDE CANDIDATE
GWSS-003E fixed-reference polarization               FOUND
GWSS-003F nonzero-tau source representation          FOUND
GWSS-003F2 synthesized vertical integrability        FOUND
GWSS-003F2 synthesized top bridge                    FOUND
GWSS-003F2 synthesized whole source/feature          FOUND
GWSS-003F2 coefficient and q.im transport            FOUND
GWSS-003F2 finite approximant scalar transport       FOUND
GWSS-003F2 unconditional whole assembly              TWO ADAPTERS REMAIN
```

Current stage-local classification:

```text
TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-API-GAP
```

This label is an API/interface gap, not an information-theoretic obstruction.

Implement only the final representation adapters:

```text
GWSS-003F3-1  derive interval-integrability of synthesized vertical aggregate in u
GWSS-003F3-2  derive interval-integrability of synthesized top aggregate in u
GWSS-003F3-3  remove hV/hT from the normalized whole-source theorem
GWSS-003F3-4  prove the arbitrary-witness finite vertical-ledger identity
GWSS-003F3-5  specialize the vertical ledger to the synthesized Mellin witness
GWSS-003F3-6  remove hvertical from the finite approximant / whole-source assembly
GWSS-003F3-7  certify the final q.im-compatible unconditional finite representation
GWSS-003F3-8  classify whether the representation layer is closed
```

This is the final adapter-closure attempt for GWSS-003F. It is not authorization to start a shifted-energy sign theorem.

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
0039 instructions read
0040 report read
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
PascalCenteredXiPrimeSideQuadraticizationAudit.lean read
PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean read
PascalCenteredXiPrimeRightEdgeTransport.lean read
PascalCenteredXiFiniteArithmeticExplicitFormula.lean read
global objective
current stage
remaining two adapter gaps
```

Immediately before this instruction file was created, the branch was 39 commits ahead and 0 behind `develop`. Reconfirm exact repository state; the repository is the source of truth.

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
GWSS-003F3
```

Load-bearing boundary:

```text
The actual synthesized witness already has:

- nonzero-tau logarithmic-box source features,
- unconditional finite vertical representation,
- unconditional finite top-horizontal representation,
- assembled whole source
    WholeSource = VerticalSource - I * TopSource,
- assembled whole logarithmic-box feature,
- exact coefficient and q.im scalar transport,
- exact finite arithmetic approximant scalar transport.

Only two adapters prevent a completely unconditional finite representation:

A. interval-integrability in the logarithmic variable of the already-defined
   vertical/top aggregated features;

B. the finite vertical arithmetic ledger

   2*Prime + 2*Arch + 2*Elem = 2*I*VerticalSource

   for the same arbitrary/synthesized witness.
```

Forbidden shortcuts:

```text
using zeroMoment or the explicit zero-side formula to manufacture either adapter
using X -> infinity as an equality
replacing the finite cutoff by ordinary zeta
removing the top-horizontal term
changing the existing orientation convention
assuming interval-integrability because interval integrals are totalized
assuming finite sums/integrals commute without the required integrability
assuming witness coefficients are real
assuming conjugation-realness
calling shifted-energy nonnegativity a sign/order theorem
RH
Weil positivity
Li criterion
unproved limit exchange
```

## 2. GWSS-003F3-1/2 — aggregate interval-integrability

### 2.1 Existing product-rectangle facts

The current module already proves unconditional product-rectangle integrability for the synthesized two-variable features:

```text
pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integrableOn_rectangle
pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature_integrableOn_rectangle
```

The aggregated functions are already defined by integrating the contour variable:

```text
VerticalAggregatedBoxFeature(u) = integral_t VerticalBoxFeature(t,u)
TopAggregatedBoxFeature(u)      = integral_x TopBoxFeature(x,u)
```

Do not prove these aggregate functions continuous unless that is genuinely the shortest existing Mathlib route. Prefer the standard Fubini/Tonelli consequence of product integrability.

### 2.2 Preferred proof shape

From integrability on

```text
uIoc(t0,t1) x uIoc(-epsilon,epsilon)
```

prove the outer-variable statement

```text
IntervalIntegrable VerticalAggregatedBoxFeature volume (-epsilon) epsilon
```

and analogously for the top aggregate.

Inspect the current Mathlib API first. Likely relevant families include the equivalent of:

```text
Integrable.integral_prod_left
Integrable.integral_prod_right
Integrable.integral_prod_right'
Measure.prod_restrict
Measure.volume_eq_prod
intervalIntegrable_iff
```

Use the exact names available in the pinned toolchain; do not guess declarations in final code.

The subtle point is that the current rectangle certificate is `IntegrableOn` over a product `uIoc` set, while the aggregate uses an `intervalIntegral`. Convert through restricted measures carefully. Preserve the current interval orientation conventions.

A focused helper theorem is preferred over adding new generic measure-theory infrastructure.

### 2.3 Stop rule

If the pinned Mathlib product-integral API cannot derive the outer integrability without a substantial new measure-theory development, stop this subpart and classify the exact API gap. Do not manufacture an `IntervalIntegrable` assumption as a structure field.

## 3. GWSS-003F3-3 — unconditional normalized whole-source theorem

Once the two aggregate-integrability facts are available, turn

```text
pascalCenteredXiMellinGeneralTauWitness_whole_source_eq_normalized_aggregate_of_integrable
```

into an unconditional theorem for

```text
hε : 0 < ε
hτ : forall i, τ i != 0
```

with the same exact conclusion:

```text
WholeSource
  = ((2*ε)^-1 : C) * integral_u WholeBoxFeature(u).
```

Do not delete the `_of_integrable` theorem if it remains a useful lower-level adapter. Add the unconditional wrapper and use the new public integrability lemmas.

## 4. GWSS-003F3-4 — arbitrary-weight finite vertical ledger

This is the second and more important adapter.

### 4.1 Exact target

Prefer proving a generic theorem first for an arbitrary differentiable weight `h : C -> C`, because the algebra is independent of the Mellin synthesis:

```text
2 * pascalPrimePowerRightEdgeCutoffIntegral h σ T X
+ 2 * pascalXiArchimedeanRightEdgeIntegral h σ T
+ 2 * pascalXiElementaryRightEdgeIntegral h σ T
=
2 * I * integral_t
  h(centeredRightEdge(t)) *
  (primePHZ_X(t) + arch(t) + elem(t)).
```

For residue windows, express the right side with the existing
`pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t`.

The exact local theorem name may differ. Keep it small and source-side.

### 4.2 Pointwise orientation first

Do not begin by manipulating four interval integrals globally. First prove the pointwise identity.

The three existing oriented integrands have shape

```text
(h(node) * prime) * I
(h(node) * arch)  * I
(h(node) * elem)  * I
```

while the deoriented source has shape

```text
h(node) * (prime + arch + elem).
```

Therefore prove explicitly that

```text
primeIntegrand + archIntegrand + elemIntegrand
  = I * (h(node) * VerticalAmplitude)
```

or the algebraically equivalent orientation chosen by the existing definitions.

This should be ring algebra plus definitions; no zero-side theorem is relevant.

### 4.3 Lift pointwise identity to interval integrals

Use public integrability where available:

```text
intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_intervalIntegrable
```

For the finite prime cutoff integrand, inspect whether a public integrability theorem is already exported. If it is not, prove only the local focused adapter needed here, using one of the existing finite constructions:

```text
- continuity of the finite cutoff integrand on the compact right edge,
- the finite von-Mangoldt expansion plus interval integrability of each mode,
- or bounded continuous weight times the existing finite source amplitude.
```

Do not rebuild the entire dominated-convergence proof from `PascalCenteredXiPrimeRightEdgeTransport.lean`.

For the combined deoriented source, a useful route may be:

```text
Differentiable h -> continuous centered right-edge weight
VerticalAmplitude intervalIntegrable
compact interval -> continuous weight is bounded
continuous bounded multiplier * integrable amplitude -> integrable
```

Reuse local helpers already present in `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` where possible.

Then use `intervalIntegral.integral_add` / `integral_const_mul` or an equivalent existing linearity theorem to lift the pointwise identity.

### 4.4 Fixed-tau=0 precedent

`PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean` already contains the source-level orientation pattern:

```text
pascalCenteredXiVerticalDeorient
pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand
pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand
pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_weight_mul_decomposed
pascalCenteredXiMellinQuadraticDeorientedSurfaces_eq_complexVerticalSurface
```

Reuse the pattern, not the fixed `τ = 0` weight. The new theorem must apply to the actual synthesized witness or to arbitrary differentiable `h`.

## 5. GWSS-003F3-5 — synthesized witness specialization

After the generic vertical ledger exists, specialize it to

```text
h = pascalCenteredXiMellinWitnessWeight ε τ c
```

using

```text
pascalCenteredXiMellinWitnessWeight_differentiable hε τ c
```

and the residue-window safety already carried by `W`.

The result should discharge exactly the `hvertical` hypothesis of

```text
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_two_mul_I_mul_wholeSource_of_vertical_ledger
```

No new source object should be introduced unless a tiny named adapter materially clarifies the statement.

## 6. GWSS-003F3-6 — unconditional finite approximant / whole-source assembly

Prove an unconditional theorem of exact shape

```text
pascalCenteredXiFiniteArithmeticApproximant
  (pascalCenteredXiMellinWitnessWeight ε τ c) W X
=
2 * I * pascalCenteredXiMellinGeneralTauWitnessWholeSource ε τ c W X
```

under only the genuine witness assumptions needed for the weight/source representation, preferably:

```text
hε : 0 < ε
hτ : forall i, τ i != 0
```

If the vertical ledger does not actually require `hτ`, do not add it there merely for symmetry. The final whole feature representation does require the nonzero-τ box feature family.

Retain the existing conditional `_of_vertical_ledger` theorem as a useful low-level certificate if appropriate.

## 7. GWSS-003F3-7 — final finite representation and q.im transport

Once both adapters are closed, expose one theorem or compact pair of theorems that make the final representation boundary explicit:

```text
FiniteApprox(h_target)
  = 2 * I * WholeSource(h_target)

WholeSource(h_target)
  = normalizedIntegral(WholeBoxFeature(h_target))
```

therefore, by composition,

```text
FiniteApprox(h_target)
  = 2 * I * normalizedIntegral(WholeBoxFeature(h_target)).
```

The composed theorem is optional if it creates awkward rewriting; the two unconditional links are sufficient. Do not optimize theorem count at the expense of clarity.

Also certify compatibility with the already-proved off-critical coefficient scaling:

```text
c_off i = (q.im : C) * c_mass i.
```

It is enough to reuse the existing whole-source/whole-feature and finite-approximant scalar transport. Do not recreate GWSS-003C.

The purpose is to make explicit that the completed representation still transports `q.im` linearly and therefore does not itself solve the off-critical exclusion.

## 8. Representation closure firewall

Even after successful closure, do not claim the arithmetic/source side has supplied an independent sign.

The following remain invalid:

```text
E_plus >= 0 and E_minus >= 0 -> E_plus >= E_minus

WholeSource = normalized integral of WholeFeature -> sign of WholeSource

q.im transport -> q.im = 0
```

GWSS-003C and GWSS-003E remain load-bearing no-go results.

If this stage succeeds, the representation layer is closed and the first genuinely mathematical missing provider becomes:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
```

meaning an independent source-side theorem of type:

```text
P1 one shifted energy dominates the other,
P2 the shifted energies are equal,
or
P3 an asymmetric quantitative gap is controlled,
```

for the actual synthesized whole feature.

Do not implement P1/P2/P3 in this assignment.

## 9. Required classification

End with exactly one primary classification from:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
TARGET-WITNESS-AGGREGATE-INTEGRABILITY-API-GAP
TARGET-WITNESS-FINITE-VERTICAL-LEDGER-API-GAP
TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-OBSTRUCTION
GWSS-003F3-IMPLEMENTATION-API-GAP
```

Use `TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP` only if all of the following are unconditional theorems in the repository after this stage:

```text
synthesized vertical aggregate interval integrability
synthesized top aggregate interval integrability
whole source = normalized whole feature integral
finite vertical arithmetic ledger
finite approximant = 2*I*whole source
q.im-compatible source/feature transport
```

If so, explicitly state in the report:

```text
TARGET-WITNESS REPRESENTATION LAYER CLOSED
```

as a secondary milestone, not as a second primary classification.

Use `TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-OBSTRUCTION` only for a proved structural incompatibility, not for a missing Mathlib lemma or difficult proof.

## 10. GWSS-004 authorization rule

GWSS-004 remains unauthorized in this assignment.

Even if representation closes, stop at `TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP`. A later review must decide whether the minimal dominance/asymmetry provider is a bounded classical positivity fragment, a direct finite source theorem, or another already-present structure.

Do not import full Guinand--Weil or Weil positivity merely because representation is complete.

## 11. Preferred outputs

Prefer extending the existing focused module rather than creating another large source file:

```text
DkMath/RH/CFBRC/
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0042-GWSS-003F3-whole-source-final-adapter-closure-report.md
```

Keep this stage small. The target is adapter closure, not theorem accumulation.

## 12. Verification

Required focused verification:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

Also run:

```text
git diff --check
```

Axiom-audit the new load-bearing theorems. Expected standard footprint is only:

```text
propext
Classical.choice
Quot.sound
```

No new `sorry`, `admit`, `native_decide`, `axiom`, RH assumption, Weil criterion, Li criterion, or unproved limit exchange.

## 13. Report requirements

The 0042 report must include:

```text
exact branch and starting HEAD
files changed
aggregate-integrability proof route
vertical-ledger pointwise identity and orientation
which existing integrability APIs were reused
whether the finite prime cutoff needed a local integrability adapter
unconditional whole-source theorem status
unconditional finite approximant / whole-source theorem status
q.im transport status
one primary classification
secondary milestone if representation closed
next exact gap
focused build result
git diff --check result
axiom footprint
```

If closure fails, record the smallest exact Lean proposition still missing. Do not replace it with prose such as “more analysis is needed.”
