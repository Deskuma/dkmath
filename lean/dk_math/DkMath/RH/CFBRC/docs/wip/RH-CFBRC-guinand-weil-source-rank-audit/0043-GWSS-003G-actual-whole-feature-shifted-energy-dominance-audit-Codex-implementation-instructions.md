# GWSS-003G actual whole-feature shifted-energy dominance audit — Codex implementation instructions

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003F3 frontier.

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
GWSS-003E fixed-reference polarization               FOUND at fixed tau = 0
GWSS-003F general nonzero-tau source representation  FOUND
GWSS-003F2 synthesized whole source/feature          FOUND
GWSS-003F3 aggregate integrability adapters          CLOSED
GWSS-003F3 arbitrary-weight vertical ledger          CLOSED
GWSS-003F3 finite approximant / whole-source bridge  CLOSED
GWSS-003F3 q.im transport through full representation CLOSED
```

Verified milestone:

```text
TARGET-WITNESS REPRESENTATION LAYER CLOSED
```

Current primary frontier:

```text
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
```

Implement only the bounded provider audit:

```text
GWSS-003G-1  define shifted energies for the actual synthesized WholeBoxFeature
GWSS-003G-2  prove their interval-integrability from the existing F3 adapters
GWSS-003G-3  lift fixed-reference polarization to the normalized whole-feature integral
GWSS-003G-4  connect the two polarization channels exactly to WholeSource
GWSS-003G-5  connect the two polarization channels exactly to FiniteApprox
GWSS-003G-6  certify q.im linear transport of the shifted-energy differences
GWSS-003G-7  inventory existing source-side sign/order/equality providers for these exact objects
GWSS-003G-8  classify whether an independent P1/P2/P3 provider exists
```

This is an audit, not an instruction to manufacture a dominance theorem.

Do not start GWSS-004 unless a later review explicitly authorizes it.

Do not start:

```text
classical Guinand--Weil infrastructure
full Weil positivity criterion
Li criterion
T -> infinity
X -> infinity as an exact equality
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
0041 instructions read
0042 report read
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean read
PascalCenteredXiPrimeSideQuadraticizationAudit.lean read
PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean read
PascalCenteredXiPrimeSideSignAudit.lean read
PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
global objective
current stage
current primary frontier
```

Immediately before this instruction file was created, GitHub comparison reported:

```text
develop merge base: 8646c3f56591aa04a35b49d5e01ce107caf8cc3b
ahead of develop:   41 commits
behind develop:      0 commits
```

The branch was exactly one commit ahead of the prior instruction commit
`599cd0a251b024ff23fcc0f2c2635577335f8ab4`, and that single commit contains
only the GWSS-003F3 implementation/report changes. Reconfirm the exact current
HEAD from the repository before editing; GitHub is the source of truth.

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
GWSS-003G
```

Load-bearing boundary:

```text
For the actual synthesized nonzero-tau witness, the repository now proves:

WholeSource(h_target)
  = ((2*epsilon)^-1 : C) * integral_u WholeBoxFeature(h_target,u)

FiniteApprox(h_target)
  = 2 * I * WholeSource(h_target)

and coefficient scaling transports through

h_target
WholeBoxFeature
WholeSource
FiniteApprox.

For the off-critical witness:

h_off = qIm * h_mass,

where qIm is a real scalar embedded in C.

The representation problem is therefore finished. The only relevant question
in this stage is whether fixed-reference polarization exposes a source-derived
order/sign/asymmetry that is independent of the zero-side detector.
```

## 2. Existing precedent that must not be overgeneralized

The fixed `tau = 0` source-side quadraticization already has:

```text
pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy
pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy
pascalCenteredXiPrimeSideQuadraticization_wholeSurface_eq_shiftedEnergyDifference
pascalCenteredXiPrimeSideQuadraticization_wholeShiftedEnergy_order_iff_scalarSurface_nonneg
```

and analogous vertical-only declarations.

Important existing conclusion:

```text
shifted-energy nonnegativity: FOUND
polarization identity:        FOUND
order equivalence:             FOUND
independent order provider:    NOT FOUND
```

The tau-zero order equivalence is algebraic: it rewrites an energy order into
a source-surface sign. It is not itself a theorem asserting that the sign
holds.

Do not silently reuse the tau-zero whole feature as the actual synthesized
nonzero-tau witness.

## 3. GWSS-003G-1 — actual synthesized shifted energies

Use the already-defined actual feature:

```text
Phi(u) :=
  pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature tau c W X u
```

for finite `W`, finite `X`, `epsilon > 0`, and selected nonzero `tau_i`.

Introduce the smallest useful four real energies, preferably in a focused new
module such as:

```text
DkMath/RH/CFBRC/
  PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
```

Suggested semantic shapes:

```text
E1Plus  = (2*epsilon)^-1 * integral_u normSq(Phi(u) + 1)
E1Minus = (2*epsilon)^-1 * integral_u normSq(Phi(u) - 1)

EIPlus  = (2*epsilon)^-1 * integral_u normSq(Phi(u) + I)
EIMinus = (2*epsilon)^-1 * integral_u normSq(Phi(u) - I)
```

Use `R`-valued definitions if that matches the existing tau-zero API best.
Keep the normalization exactly compatible with the established whole-source
identity.

Do not add a new abstract provider structure merely to store an ordering.

## 4. GWSS-003G-2 — interval-integrability

Reuse the F3 theorem proving interval-integrability of the actual synthesized
whole aggregate/feature on `[-epsilon,epsilon]`.

For each shifted norm-square integrand, derive `IntervalIntegrable` using only
finite-window facts already available. Appropriate proof ingredients may
include:

```text
IntervalIntegrable.add / sub
continuous_const
continuous_normSq or continuity of Complex.normSq
IntervalIntegrable.norm / normSq composition if available
continuous-on-compact boundedness plus integrability
```

Inspect the pinned Mathlib API first and use exact available names.

Do not rely on totalization of interval integrals as a substitute for
integrability.

Do not introduce any limit.

## 5. GWSS-003G-3 — integrated polarization for the actual feature

The end of
`PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean` already proves
pointwise, for arbitrary complex `F`:

```text
normSq(F + 1) - normSq(F - 1) = 4 * F.re
normSq(F + I) - normSq(F - I) = 4 * F.im
```

Lift these exact identities through the normalized `u` integral for the actual
synthesized feature.

Target real identities should be equivalent to:

```text
E1Plus - E1Minus
  = 4 * Re(normalizedIntegral Phi)

EIPlus - EIMinus
  = 4 * Im(normalizedIntegral Phi).
```

Prove the pointwise identity first, then use interval-integral linearity with
the explicit integrability certificates.

Do not assume conjugation-realness. The two reference channels `1` and `I`
exist precisely because the general synthesized feature may be genuinely
complex.

## 6. GWSS-003G-4 — exact WholeSource readout

Use the unconditional F3 theorem:

```text
WholeSource
  = normalizedIntegral Phi.
```

Expose exact readout theorems:

```text
E1Plus - E1Minus = 4 * WholeSource.re
EIPlus - EIMinus = 4 * WholeSource.im
```

or algebraically equivalent statements.

This is still representation/polarization, not dominance.

## 7. GWSS-003G-5 — exact FiniteApprox readout

Use the unconditional finite identity:

```text
FiniteApprox = 2 * I * WholeSource.
```

If

```text
A := FiniteApprox
W := WholeSource,
A = 2 * I * W,
```

then the two shifted-energy differences satisfy the exact coordinate readout:

```text
E1Plus - E1Minus =  2 * A.im
EIPlus - EIMinus = -2 * A.re.
```

Prove these as exact finite-level algebraic theorems for the actual synthesized
witness. Keep `W`, `X`, `epsilon`, and the selected `tau` finite.

This is a high-value boundary theorem: after it exists, any future proposed
shifted-energy dominance/equality can be checked immediately for whether it is
merely a renamed sign/equality of the already-known finite arithmetic
approximant.

Do not use a zeroMoment rewrite to prove these identities.

## 8. GWSS-003G-6 — q.im transport of cross-term differences

The off-critical coefficient family has the exact shape:

```text
c_off i = (q.im : C) * c_mass i.
```

The whole feature therefore scales pointwise by this real scalar.

Prove, for the shifted-energy **differences**, the corresponding real-linear
transport. Schematically, for real `r = q.im`:

```text
(E1Plus - E1Minus)(r * Phi)
  = r * (E1Plus - E1Minus)(Phi)

(EIPlus - EIMinus)(r * Phi)
  = r * (EIPlus - EIMinus)(Phi).
```

Prefer deriving this from the exact WholeSource/FiniteApprox readout plus the
already-proved coefficient scalar transport, rather than expanding four
norm-square integrals again.

This theorem should demonstrate the only reason fixed-reference polarization
remains interesting after GWSS-003C: the cross term retains `q.im` to first
order instead of replacing it by `|q.im|^2`.

It still does not force `q.im = 0` without an independent sign/order/equality
provider.

## 9. GWSS-003G-7 — source-derived provider inventory

After the actual feature and readout theorems are in place, perform a bounded
repository audit for a theorem that applies to these exact objects.

Mandatory files to inspect:

```text
PascalCenteredXiPrimeSideQuadraticizationAudit.lean
PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
PascalCenteredXiPrimeSideSignAudit.lean
PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean
PascalCenteredXiMellinWitnessProviderDecisionAudit.lean
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

Also search the current `DkMath/RH/CFBRC` source tree for declarations involving:

```text
shifted energy
whole shifted
nonneg
nonpos
sign
order
dominance
polarization
Gram
autocorrelation
excess
defect
source surface
```

For every candidate provider, answer all of:

```text
1. Does it apply to the exact actual synthesized nonzero-tau WholeBoxFeature?
2. Does it include the top-horizontal source, not only the vertical edge?
3. Is it source-derived rather than a zeroMoment / zero-carrier rewrite?
4. Does it prove P1, P2, or P3, rather than only P0 nonnegativity?
5. Is it independent of q.im scalar rescaling?
6. Does it avoid RH-equivalent assumptions?
7. Does it remain finite-level, without an unproved limit exchange?
```

The already-known tau-zero theorem

```text
wholeShiftedEnergy_order_iff_scalarSurface_nonneg
```

is not automatically a provider. It proves an equivalence, not the sign.

The existing prime-side sign audit transports conditional nonpositivity through
ordered limits; its hypotheses are providers, not unconditional sign theorems.
Do not count those hypotheses as found information.

## 10. P0/P1/P2/P3 firewall

Keep these logically separate:

```text
P0: Eplus >= 0 and Eminus >= 0
P1: Eminus <= Eplus
P2: Eminus = Eplus
P3: a source-derived controlled asymmetric gap
```

P0 never implies P1 or P2.

For the actual feature, the polarization identities imply:

```text
P1 in the 1-reference channel
  <-> WholeSource.re >= 0
  <-> FiniteApprox.im >= 0

P1 in the I-reference channel
  <-> WholeSource.im >= 0
  <-> FiniteApprox.re <= 0
```

with orientation adjusted exactly to the final Lean definitions.

Therefore any theorem claiming P1 must be audited as a genuine source-side sign
theorem for the corresponding finite arithmetic component. An algebraic
restatement of that sign is not new information.

## 11. Homogeneity firewall

Do not fall back to bare energy:

```text
integral normSq(qIm * Phi)
```

because it scales as `|qIm|^2` and reproduces the GWSS-003C/003D homogeneity
obstruction.

The only reason to retain shifted energies is the fixed-reference cross term.
If the proposed control treats both sides with the same first- or second-order
homogeneity and cancels `q.im`, classify it as a no-go.

## 12. Independence firewall

Forbidden as providers:

```text
RiemannHypothesis
Li criterion
full Weil positivity criterion assumed as an axiom/provider
raw-ratio boundedness already audited as RH-equivalent
zeroMoment rewritten into the desired sign
centered horizontal energy positivity rewritten into the desired sign
functional-equation symmetry alone
conjugation alone
criticalMirror alone
invertible scalar/linear transport alone
```

A provider must add source-side arithmetic/order information not already
encoded by the target zero configuration.

## 13. Limit firewall

Remain finite in this stage.

Do not use without an existing exact theorem:

```text
T -> infinity
horizontal decay of the full Xi-weighted integrand
X -> infinity as an equality
interchange of cutoff and logarithmic-box integrals
epsilon -> 0
```

The entire F3 representation is finite-level. Preserve that advantage.

## 14. Minimal missing theorem shape if no provider is found

If no existing provider proves P1/P2/P3, do not start a large new positivity
framework.

Instead state the minimal missing theorem surface in the report.

Preferred schematic shapes include one of:

```text
-- 1-reference sign
0 <=
  (pascalCenteredXiMellinGeneralTauWitnessWholeSource epsilon tau c W X).re

-- I-reference sign
0 <=
  (pascalCenteredXiMellinGeneralTauWitnessWholeSource epsilon tau c W X).im

-- exact equality
(pascalCenteredXiMellinGeneralTauWitnessWholeSource epsilon tau c W X).re = 0

-- controlled source-side asymmetry
abs (Eplus - Eminus) <= sourceBound
```

but only after checking which coordinate actually couples to the target
witness and which orientation would yield useful centered-coordinate
information.

Do not promote a schematic theorem to an axiom, structure field, or assumed
hypothesis in production code.

## 15. Required classification

End with exactly one primary classification from:

```text
ACTUAL-SHIFTED-ENERGY-POLARIZATION-FOUND-DOMINANCE-GAP
SOURCE-DERIVED-SHIFTED-ENERGY-DOMINANCE-PROVIDER-FOUND
SOURCE-DERIVED-SHIFTED-ENERGY-EQUALITY-PROVIDER-FOUND
SHIFTED-ENERGY-POSITIVITY-ONLY-NOGO
ACTUAL-WHOLE-FEATURE-SHIFTED-ENERGY-API-GAP
NONLINEAR-POSITIVITY-MINIMAL-PROVIDER-IDENTIFIED
```

Use:

```text
ACTUAL-SHIFTED-ENERGY-POLARIZATION-FOUND-DOMINANCE-GAP
```

if all actual-feature definitions, integrability, polarization, WholeSource
readout, FiniteApprox readout, and q.im cross-term transport are Green, but no
independent P1/P2/P3 theorem exists.

Use:

```text
SHIFTED-ENERGY-POSITIVITY-ONLY-NOGO
```

only if the strongest exact source information found for the actual feature is
P0 and the report supplies an explicit order counterexample or reduction
showing why P0 cannot decide the needed sign.

Use a provider-FOUND classification only for a theorem that applies to the
actual synthesized whole feature and passes every independence firewall above.

Use `ACTUAL-WHOLE-FEATURE-SHIFTED-ENERGY-API-GAP` only if even the finite
actual-feature polarization layer cannot be built from the already closed F3
representation without substantial unrelated infrastructure.

## 16. GWSS-004 authorization rule

GWSS-004 remains unauthorized in this assignment.

A later review may consider a bounded classical Guinand--Weil fragment only if
this stage establishes all of:

```text
actual shifted-energy/polarization layer CLOSED
no current DkMath source theorem provides P1/P2/P3
minimal missing sign/order theorem shape identified
candidate classical positivity fragment is strictly smaller than RH/Weil criterion
candidate fragment is not merely the same finite arithmetic sign renamed
```

Do not import or assume classical Weil positivity here.

## 17. Implementation discipline

Prefer extending a focused new audit module over further enlarging the 1491-line
F3 source-bridge module, unless reuse makes a tiny local addition clearly
better.

Keep definitions/theorems small and named by mathematical role.

Reuse existing F3 theorems instead of reproving:

```text
whole feature coefficient linearity
whole source coefficient linearity
whole source = normalized whole-feature integral
finite approximant = 2*I*whole source
finite approximant coefficient linearity
q.im transport
```

Do not duplicate the tau-zero quadraticization subsystem merely to change
names. Generalize only the exact pieces required for the actual synthesized
feature.

## 18. Verification

At minimum run:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
```

or the final chosen focused module path.

Also run:

```text
git diff --check
```

If the repository workflow for this branch normally validates the root RH
module, run the focused public-import check required by the current project
conventions. Do not claim CI if only local Lean checks were run.

Axiom-audit the load-bearing new declarations. Expected footprint should not
exceed the usual:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `native_decide`, or new `axiom`.

## 19. Required report

Create the next report in the same directory, normally:

```text
0044-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-report.md
```

The report must include:

```text
starting HEAD
files changed
focused Lean verification result
actual shifted-energy definitions
integrability status
integrated 1/I polarization identities
WholeSource readout identities
FiniteApprox readout identities
q.im cross-term transport
provider inventory
P0/P1/P2/P3 distinction
independence audit
one primary classification
exact next missing theorem shape, if any
GWSS-004 authorization status
axiom footprint
```

If no provider is found, stop after naming the minimal missing theorem. Do not
continue into GWSS-004 in the same implementation pass.

## 20. Mathematical sanity check

The key algebra to preserve is finite and exact.

Let

```text
Wsrc = WholeSource
A    = FiniteApprox
```

with

```text
A = 2 * I * Wsrc.
```

Then:

```text
A.re = -2 * Wsrc.im
A.im =  2 * Wsrc.re.
```

Hence the two actual shifted-energy differences should reduce to:

```text
E1Plus - E1Minus =  4 * Wsrc.re =  2 * A.im
EIPlus - EIMinus =  4 * Wsrc.im = -2 * A.re.
```

These identities are not a sign theorem. They are the exact diagnostic surface
on which a genuine independent source-derived sign theorem must act.

That distinction is the entire purpose of GWSS-003G.
