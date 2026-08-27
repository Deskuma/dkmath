# GWSS-003F2 synthesized whole-source assembly closure — Codex implementation instructions

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003F frontier.

Trusted state:

```text
GWSS-001 source rank                            CLOSED
GWSS-002 finite off-critical Mellin witness    CLOSED
GWSS-003A finite arithmetic identity           FOUND
GWSS-003B universal complex-linear phase       NOGO
GWSS-003C first-order homogeneous norm         NOGO
GWSS-003D independent vanishing scale          NOT FOUND
GWSS-003D real/conjugation route               API GAP / cancellation risk
GWSS-003D nonlinear positivity                 SOURCE-SIDE CANDIDATE
GWSS-003E fixed-reference polarization         FOUND
GWSS-003E target-witness source bridge         GAP
GWSS-003F nonzero-tau box feature              FOUND
GWSS-003F single-basis vertical bridge         FOUND
GWSS-003F single-basis top-horizontal bridge   FOUND
GWSS-003F synthesized weight feature           FOUND
GWSS-003F synthesized vertical fibre           FOUND
GWSS-003F synthesized whole assembly           INCOMPLETE
```

The stage-local 0038 classification was:

```text
TARGET-WITNESS-SOURCE-BRIDGE-REPRESENTATION-GAP
```

Do not treat that label as a proved obstruction. The repository now contains enough single-basis and finite-sum infrastructure that the remaining gap may be only assembly/bookkeeping.

Implement only the next bounded closure stage:

```text
GWSS-003F2-1  discharge synthesized vertical rectangle integrability
GWSS-003F2-2  build the synthesized top-horizontal feature and bridge
GWSS-003F2-3  assemble one synthesized finite whole-source feature
GWSS-003F2-4  prove the exact finite arithmetic-approximant / whole-source identity
GWSS-003F2-5  prove coefficient-scalar transport through vertical, top, and whole source features
GWSS-003F2-6  specialize the scalar transport to the GWSS-003C off-critical qIm scaling
GWSS-003F2-7  classify whether the representation layer is now closed
```

This assignment is an assembly closure. It is not authorization to prove shifted-energy dominance, positivity criteria, or RH.

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
0037 instructions read
0038 report read
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiPrimeSideQuadraticizationAudit.lean read
PascalCenteredXiFiniteArithmeticExplicitFormula.lean read
global objective
current GWSS stage
load-bearing representation boundary
next unresolved Gap
```

The branch was 37 commits ahead and 0 behind `develop` immediately before this instruction file was created. Reconfirm the exact repository state; the repository is the source of truth.

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
GWSS-003F2
```

Load-bearing boundary:

```text
For every selected nonzero tau_i, the repository already has an exact
single-basis logarithmic-box source feature for both the right edge and the
top-horizontal edge.

For a synthesized witness

h_target(z) = sum_i c_i H_{epsilon,tau_i}(z),

the repository already has the exact finite feature representation and the
right-edge fibre identity.

The remaining task is to close the finite-sum rectangle integrability,
synthesize the top feature, assemble vertical + top with the correct contour
orientation, and certify the same qIm scalar transport at the source-feature
level.
```

Forbidden shortcuts:

```text
assuming synthesized rectangle integrability without proving it
assuming the top bridge is linear without proving the finite-sum identity
silently replacing the finite arithmetic approximant by the exact zeta RHS
using X -> infinity as an equality
removing the top-horizontal term
changing the contour orientation convention
assuming c_i are real
assuming the synthesized feature is conjugation-real
calling polarization nonnegativity a sign/order theorem
using zeroMoment rewrite as an independent source-side provider
RH
Weil positivity
Li criterion
unproved limit exchange
```

## 2. Existing APIs that should make this stage small

From `PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean`:

```text
pascalCenteredXiMellinGeneralTauVerticalBoxFeature_integrableOn_rectangle
pascalCenteredXiMellinGeneralTauTopBoxFeature_integrableOn_rectangle

pascalCenteredXiMellinGeneralTau_weighted_vertical_source_eq_normalized_aggregate
pascalCenteredXiMellinGeneralTau_top_horizontal_source_eq_normalized_aggregate

pascalCenteredXiMellinWitnessWeight_eq_normalized_generalTauWitnessBoxFeature_integral
pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integral_eq_witnessWeight_mul_amplitude
pascalCenteredXiMellinGeneralTauWitness_weighted_vertical_source_eq_normalized_aggregate
```

The last synthesized vertical theorem currently takes an explicit `hbox` rectangle-integrability hypothesis.

From `PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean`:

```text
pascalCenteredXiMellinWitnessWeight_scaled_coefficients
pascalCenteredXiMellinWitnessTopHorizontalContribution_const_mul
pascalCenteredXiMellinWitnessFiniteArithmeticRHS_const_mul
exists_pascalCenteredXiMellinMassAndOffCriticalWitness
```

Do not reprove those results unless a tiny adapter is necessary.

From `PascalCenteredXiFiniteArithmeticExplicitFormula.lean`:

```text
pascalCenteredXiFiniteArithmeticApproximant h W X
```

is the finite-cutoff four-term arithmetic object. Keep it distinct from the exact finite-zeta RHS and the `X -> infinity` endpoint.

## 3. GWSS-003F2-1 — discharge synthesized vertical rectangle integrability

The synthesized vertical feature is definitionally a finite coefficient sum:

```text
Phi_target^V(t,u)
  = sum_i c_i * Phi_{tau_i}^V(t,u).
```

Each single-basis `Phi_{tau_i}^V` already has finite-rectangle `IntegrableOn`.

Prove an unconditional theorem of shape:

```lean
theorem pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature_integrableOn_rectangle
    {n : Nat} (epsilon : Real)
    (tau : Fin n -> Real) (c : Fin n -> Complex)
    (W : PascalCenteredXiResidueTransportWindow) (X : Nat) :
    IntegrableOn
      (Function.uncurry
        (pascalCenteredXiMellinGeneralTauWitnessVerticalBoxFeature tau c W X))
      (Set.uIoc (-W.rectangle.T) W.rectangle.T ×ˢ Set.uIoc (-epsilon) epsilon)
      volume := by
  ...
```

The exact local syntax may differ. Prefer finite-sum closure of the already-proved single-basis integrability:

```text
single-basis IntegrableOn
  -> const_mul by c_i
  -> finite sum
```

Do not rebuild compact-continuity domination for the synthesized feature unless the finite-sum route is unexpectedly blocked by the API.

Then add an unconditional wrapper for the existing synthesized vertical aggregate theorem, removing the explicit `hbox` premise.

## 4. GWSS-003F2-2 — synthesized top-horizontal feature

Define the finite synthesized top feature with exactly the same coefficients:

```text
Phi_target^H(x,u)
  = sum_i c_i * Phi_{tau_i}^H(x,u).
```

Recommended local surfaces:

```text
pascalCenteredXiMellinGeneralTauWitnessTopBoxFeature
pascalCenteredXiMellinGeneralTauWitnessTopAggregatedBoxFeature
```

Prove, under

```text
h_epsilon : 0 < epsilon
h_tau : forall i, tau i != 0,
```

the exact fibre theorem:

```text
(2 epsilon)^(-1) * integral_u Phi_target^H(x,u)
  = h_target(topNode(x)) * topAmplitude(x).
```

Then prove synthesized top rectangle integrability by the same finite-sum method from

```text
pascalCenteredXiMellinGeneralTauTopBoxFeature_integrableOn_rectangle.
```

Finally prove the unconditional aggregate identity:

```text
TopHorizontalContribution(h_target)
  = (2 epsilon)^(-1) * integral_u TopAggregate_target(u).
```

This theorem must concern the actual synthesized witness

```text
pascalCenteredXiMellinWitnessWeight epsilon tau c.
```

Do not replace it by a new unrelated coefficient family.

## 5. GWSS-003F2-3 — assemble one finite whole-source feature

The current finite right-edge source feature is deoriented: its source amplitude does not include the path factor `I`.

The top-horizontal source is not deoriented in the same way.

Preserve the existing fixed-`tau = 0` orientation convention. A natural synthesized whole source is schematically:

```text
WholeSource_target
  := VerticalSource_target - I * TopSource_target.
```

because the actual finite arithmetic approximant has the orientation

```text
2 * I * VerticalSource_target + 2 * TopSource_target.
```

Thus

```text
2 * I * WholeSource_target
  = finite arithmetic approximant.
```

Audit the exact definitions before committing to names or multiplication order. Prove the orientation algebra explicitly; do not rely on prose.

Define a pointwise whole box feature using the same orientation:

```text
WholeFeature_target(u)
  := VerticalAggregate_target(u)
       - I * TopAggregate_target(u).
```

Prove the exact normalized representation:

```text
WholeSource_target
  = (2 epsilon)^(-1) * integral_u WholeFeature_target(u).
```

If interval-integrability of the aggregate functions is needed for `integral_sub` / `integral_const_mul`, prove it from the existing single-basis/synthesized finite-sum infrastructure rather than assuming it.

## 6. GWSS-003F2-4 — finite arithmetic approximant / whole-source identity

This is the load-bearing representation closure theorem.

For the actual synthesized witness and finite cutoff `X`, prove a theorem of the mathematical shape:

```text
pascalCenteredXiFiniteArithmeticApproximant
    (pascalCenteredXiMellinWitnessWeight epsilon tau c) W X
  = 2 * I * WholeSource_target.
```

Equivalent rearrangements are acceptable if they preserve exactly the same orientation and all four finite terms:

```text
finite prime cutoff
archimedean correction
elementary correction
top-horizontal contribution.
```

The proof should unfold or reuse the finite source ledger and the definitions of the right-edge integrals. Do not use the exact zero-moment endpoint and do not pass to `X -> infinity`.

Then combine this theorem with the normalized whole-feature representation if convenient:

```text
finite arithmetic approximant
  = 2 * I * (2 epsilon)^(-1) * integral_u WholeFeature_target(u).
```

This final combined theorem is preferred if it remains short.

## 7. GWSS-003F2-5 — coefficient scalar transport through source features

The source feature construction must be explicitly linear in the witness coefficients.

For arbitrary `a : Complex`, prove compact theorems of the shape:

```text
WitnessVerticalBoxFeature tau (fun i => a * c i) ...
  = a * WitnessVerticalBoxFeature tau c ...

WitnessTopBoxFeature tau (fun i => a * c i) ...
  = a * WitnessTopBoxFeature tau c ...

WitnessWholeFeature tau (fun i => a * c i) ...
  = a * WitnessWholeFeature tau c ...
```

Also expose aggregate / whole-source scalar transport if it is not automatic from the pointwise theorem:

```text
WholeSource(tau, a*c)
  = a * WholeSource(tau,c).
```

These are representation theorems only. They must not be interpreted as new source rank or new arithmetic information.

## 8. GWSS-003F2-6 — specialize to the off-critical qIm scaling

Reuse the GWSS-003C coefficient factorization:

```text
c_off(i) = qIm * c_mass(i),

qIm = (target squared orbit).im,
```

with `qIm` cast to `Complex` where necessary.

Provide a focused theorem or corollary certifying:

```text
Phi_off^whole(u) = qIm * Phi_mass^whole(u)
```

and preferably

```text
WholeSource_off = qIm * WholeSource_mass.
```

It is acceptable for this theorem to be parameterized by `c0`, `tau`, and `qIm` rather than to re-run the entire existential full-rank construction, provided the specialization to the exact coefficient family used by `exists_pascalCenteredXiMellinMassAndOffCriticalWitness` is explicit in the report.

Do not seek a contradiction here. The point is to certify that the newly completed whole-source bridge transports exactly the same target scalar already isolated in GWSS-003C.

## 9. What success means

If Sections 3--8 all close, the representation layer is finished:

```text
nonzero-tau basis source bridge          FOUND
synthesized vertical bridge              FOUND
synthesized top-horizontal bridge        FOUND
synthesized finite whole-source bridge   FOUND
finite arithmetic approximant bridge     FOUND
off-critical qIm source transport        FOUND
```

At that point the next unresolved mathematical information is no longer representation. It is an independent order/asymmetry theorem for shifted energies or an equivalent nonlinear source observable.

The next Gap should then be:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
```

This does not itself authorize proving such dominance in this assignment.

## 10. Required classification

End with exactly one primary classification from:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
SYNTHESIZED-WITNESS-WHOLE-SOURCE-BRIDGE-FOUND
TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-API-GAP
TARGET-WITNESS-WHOLE-SOURCE-ASSEMBLY-OBSTRUCTION
GWSS-003F2-IMPLEMENTATION-API-GAP
```

Use:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
```

only if the synthesized vertical/top/whole representation, finite arithmetic approximant identity, and off-critical scalar transport are all proved.

Use:

```text
SYNTHESIZED-WITNESS-WHOLE-SOURCE-BRIDGE-FOUND
```

only if the whole bridge itself is proved but one narrow scalar-specialization theorem remains deliberately deferred.

Use an `...API-GAP` label only for a precise unavailable theorem/interface that cannot be discharged by the already-present finite-sum/integrability machinery.

Use `...OBSTRUCTION` only for a proved mathematical incompatibility, not a difficult Lean proof.

Secondary findings should separately record:

```text
synthesized vertical rectangle integrability: FOUND / GAP
synthesized vertical aggregate:               FOUND / GAP
synthesized top feature:                      FOUND / GAP
synthesized top rectangle integrability:      FOUND / GAP
synthesized top aggregate:                    FOUND / GAP
whole feature:                                FOUND / GAP
finite approximant / whole source:            FOUND / GAP
generic coefficient scalar transport:         FOUND / GAP
off-critical qIm source transport:            FOUND / GAP
independent shifted-energy dominance:          NOT FOUND
```

## 11. GWSS-004 authorization rule

GWSS-004 remains unauthorized in this assignment.

Even if the representation layer closes completely, stop at

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP.
```

A later review will decide whether the minimal missing dominance provider can be isolated as a bounded classical Guinand--Weil fragment, or whether another source-side route should be tested first.

Do not import or formalize a full Weil criterion merely because the word `dominance` appears.

## 12. Preferred outputs

Prefer extending the existing focused module if the additional code remains coherent:

```text
DkMath/RH/CFBRC/
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

A small follow-on module is acceptable if keeping the 003F source-feature layer separate makes the proof materially clearer, for example:

```text
DkMath/RH/CFBRC/
PascalCenteredXiMellinWitnessWholeSourceAssemblyAudit.lean
```

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0040-GWSS-003F2-synthesized-whole-source-assembly-closure-report.md
```

Do not retroactively rewrite 0038 merely to change its stage-local classification. The new 0040 report should state whether 0038's representation gap was discharged, narrowed, or upgraded to a proved obstruction.

## 13. Verification

Required focused build for whichever module carries the new load-bearing theorems, for example:

```text
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit
```

or

```text
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessWholeSourceAssemblyAudit
```

Also run:

```text
git diff --check
```

Axiom audit the main new integrability/whole-source/scalar-transport theorems. Expected footprint:

```text
propext
Classical.choice
Quot.sound
```

No new `sorry`, `admit`, `native_decide`, custom axiom, RH assumption, Weil criterion, Li criterion, unproved `T -> infinity` step, or unproved limit exchange.
